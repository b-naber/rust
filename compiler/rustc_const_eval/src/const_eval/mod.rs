// Not in interpret to make sure we do not use private implementation details

use std::convert::TryFrom;

use rustc_errors::ErrorGuaranteed;
use rustc_hir::Mutability;
use rustc_middle::mir;
use rustc_middle::mir::interpret::{ErrorHandled, EvalToValTreeResult, GlobalId};
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{source_map::DUMMY_SP, symbol::Symbol};
use rustc_target::abi::VariantIdx;

use std::iter;

use crate::interpret::{
    get_slice_bytes, intern_const_alloc_recursive, ConstValue, GlobalAlloc, InternKind, InterpCx,
    InterpResult, MemPlaceMeta, Scalar,
};

mod error;
mod eval_queries;
mod fn_queries;
mod machine;
mod valtrees;

pub use error::*;
pub use eval_queries::*;
pub use fn_queries::*;
pub use machine::*;
pub(crate) use valtrees::{const_to_valtree_inner, valtree_to_const_value};

pub(crate) fn const_caller_location(
    tcx: TyCtxt<'_>,
    (file, line, col): (Symbol, u32, u32),
) -> ConstValue<'_> {
    trace!("const_caller_location: {}:{}:{}", file, line, col);
    let mut ecx = mk_eval_cx(tcx, DUMMY_SP, ty::ParamEnv::reveal_all(), false);

    let loc_place = ecx.alloc_caller_location(file, line, col);
    if intern_const_alloc_recursive(&mut ecx, InternKind::Constant, &loc_place).is_err() {
        bug!("intern_const_alloc_recursive should not error in this case")
    }
    ConstValue::Scalar(Scalar::from_maybe_pointer(loc_place.ptr, &tcx))
}

/// Evaluates a constant and turns it into a type-level constant value.
#[instrument(skip(tcx), level = "debug")]
pub(crate) fn eval_to_valtree<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    cid: GlobalId<'tcx>,
) -> EvalToValTreeResult<'tcx> {
    let const_alloc = tcx.eval_to_allocation_raw(param_env.and(cid))?;
    let ecx = mk_eval_cx(
        tcx, DUMMY_SP, param_env,
        // It is absolutely crucial for soundness that
        // we do not read from static items or other mutable memory.
        false,
    );
    let place = ecx.raw_const_to_mplace(const_alloc).unwrap();
    debug!(?place);

    let valtree = const_to_valtree_inner(&ecx, &place);

    let ty = const_alloc.ty;
    let const_val_old = turn_into_const_value(tcx, const_alloc, param_env.and(cid));
    let old = mir::ConstantKind::from_value(const_val_old, ty);
    let const_val_new = tcx.valtree_to_const_val((const_alloc.ty, valtree.unwrap()));
    let new = mir::ConstantKind::from_value(const_val_new, ty);

    if !check_const_value_eq(tcx, param_env, old, new) {
        bug!("old const_val {:?} not equal to new const_val {:?}", const_val_old, const_val_new);
    }

    Ok(valtree)
}

fn check_const_value_eq<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    a: mir::ConstantKind<'tcx>,
    b: mir::ConstantKind<'tcx>,
) -> bool {
    match (a, b) {
        (mir::ConstantKind::Val(a_const_val, a_ty), mir::ConstantKind::Val(b_const_val, b_ty)) => {
            match (a_const_val, b_const_val) {
                (
                    ConstValue::Scalar(Scalar::Int(a_val)),
                    ConstValue::Scalar(Scalar::Int(b_val)),
                ) => a_val == b_val,
                (
                    ConstValue::Scalar(Scalar::Ptr(a_val, _a_size)),
                    ConstValue::Scalar(Scalar::Ptr(b_val, _b_size)),
                ) => {
                    a_val == b_val
                        || match (
                            tcx.global_alloc(a_val.provenance),
                            tcx.global_alloc(b_val.provenance),
                        ) {
                            (
                                GlobalAlloc::Function(a_instance),
                                GlobalAlloc::Function(b_instance),
                            ) => a_instance == b_instance,
                            _ => false,
                        }
                }

                (ConstValue::Slice { .. }, ConstValue::Slice { .. }) => {
                    get_slice_bytes(&tcx, a_const_val) == get_slice_bytes(&tcx, b_const_val)
                }

                (
                    ConstValue::ByRef { alloc: alloc_a, .. },
                    ConstValue::ByRef { alloc: alloc_b, .. },
                ) if a.ty().is_ref() || b.ty().is_ref() => {
                    if a.ty().is_ref() && b.ty().is_ref() {
                        alloc_a == alloc_b
                    } else {
                        false
                    }
                }
                (ConstValue::ByRef { .. }, ConstValue::ByRef { .. }) => {
                    let a_destructured = tcx.destructure_mir_constant(param_env.and(a));
                    let b_destructured = tcx.destructure_mir_constant(param_env.and(b));

                    // Both the variant and each field have to be equal.
                    if a_destructured.variant == b_destructured.variant {
                        for (a_field, b_field) in
                            iter::zip(a_destructured.fields, b_destructured.fields)
                        {
                            if !check_const_value_eq(tcx, param_env, *a_field, *b_field) {
                                return false;
                            }
                        }

                        true
                    } else {
                        false
                    }
                }

                _ => false,
            }
        }
        _ => {
            bug!("expected concrete values, found: a: {:?}, b: {:?}", a, b);
        }
    }
}

/// Tries to destructure constants of type Array or Adt into the constants
/// of its fields.
pub(crate) fn try_destructure_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    _const: ty::Const<'tcx>,
) -> Option<mir::DestructuredConst<'tcx>> {
    if let ty::ConstKind::Value(valtree) = _const.val() {
        let branches = valtree.unwrap_branch();

        let (fields, variant) = match _const.ty().kind() {
            ty::Array(inner_ty, _) => {
                // construct the consts for the elements of the array
                let field_consts = branches
                    .iter()
                    .map(|b| {
                        tcx.mk_const(ty::ConstS { val: ty::ConstKind::Value(*b), ty: *inner_ty })
                    })
                    .collect::<Vec<_>>();
                debug!(?field_consts);

                (field_consts, None)
            }
            ty::Adt(def, _) if def.variants().is_empty() => bug!("unreachable"),
            ty::Adt(def, substs) if def.is_enum() => {
                let variant_idx = if def.is_enum() {
                    VariantIdx::from_u32(branches[0].unwrap_leaf().try_to_u32().unwrap())
                } else {
                    VariantIdx::from_u32(0)
                };
                let fields = &def.variant(variant_idx).fields;
                let mut field_consts = vec![];

                // Note: First element inValTree corresponds to variant of enum
                let mut valtree_idx = if def.is_enum() { 1 } else { 0 };
                for field in fields {
                    let field_ty = field.ty(tcx, substs);
                    let field_valtree = branches[valtree_idx]; // first element of branches is variant
                    let field_const = tcx.mk_const(ty::ConstS {
                        val: ty::ConstKind::Value(field_valtree),
                        ty: field_ty,
                    });
                    field_consts.push(field_const);
                    valtree_idx += 1;
                }
                debug!(?field_consts);

                (field_consts, Some(variant_idx))
            }
            _ => bug!("cannot destructure constant {:?}", _const.val()),
        };

        let fields = tcx.arena.alloc_from_iter(fields.into_iter());

        Some(mir::DestructuredConst { variant, fields })
    } else {
        None
    }
}

pub(crate) fn destructure_mir_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    val: mir::ConstantKind<'tcx>,
) -> mir::DestructuredMirConstant<'tcx> {
    trace!("destructure_const: {:?}", val);
    let ecx = mk_eval_cx(tcx, DUMMY_SP, param_env, false);
    let op = ecx.mir_const_to_op(&val, None).unwrap();

    // We go to `usize` as we cannot allocate anything bigger anyway.
    let (field_count, variant, down) = match val.ty().kind() {
        ty::Array(_, len) => (usize::try_from(len.eval_usize(tcx, param_env)).unwrap(), None, op),
        ty::Adt(def, _) if def.variants().is_empty() => {
            return mir::DestructuredMirConstant { variant: None, fields: &[] };
        }
        ty::Adt(def, _) => {
            let variant = ecx.read_discriminant(&op).unwrap().1;
            let down = ecx.operand_downcast(&op, variant).unwrap();
            (def.variants()[variant].fields.len(), Some(variant), down)
        }
        ty::Tuple(substs) => (substs.len(), None, op),
        _ => bug!("cannot destructure constant {:?}", val),
    };

    let fields_iter = (0..field_count).map(|i| {
        let field_op = ecx.operand_field(&down, i).unwrap();
        let val = op_to_const(&ecx, &field_op);
        mir::ConstantKind::Val(val, field_op.layout.ty)
    });
    let fields = tcx.arena.alloc_from_iter(fields_iter);

    mir::DestructuredMirConstant { variant, fields }
}

#[instrument(skip(tcx), level = "debug")]
pub(crate) fn destructure_mir_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    val: mir::ConstantKind<'tcx>,
) -> mir::DestructuredMirConstant<'tcx> {
    trace!("destructure_const: {:?}", val);
    let ecx = mk_eval_cx(tcx, DUMMY_SP, param_env, false);
    let op = ecx.mir_const_to_op(&val, None).unwrap();

    // We go to `usize` as we cannot allocate anything bigger anyway.
    let (field_count, variant, down) = match val.ty().kind() {
        ty::Array(_, len) => (usize::try_from(len.eval_usize(tcx, param_env)).unwrap(), None, op),
        ty::Adt(def, _) if def.variants.is_empty() => {
            return mir::DestructuredMirConstant { variant: None, fields: &[] };
        }
        ty::Adt(def, _) => {
            let variant = ecx.read_discriminant(&op).unwrap().1;
            let down = ecx.operand_downcast(&op, variant).unwrap();
            (def.variants[variant].fields.len(), Some(variant), down)
        }
        ty::Tuple(substs) => (substs.len(), None, op),
        _ => bug!("cannot destructure constant {:?}", val),
    };

    let fields_iter = (0..field_count).map(|i| {
        let field_op = ecx.operand_field(&down, i).unwrap();
        let val = op_to_const(&ecx, &field_op);
        mir::ConstantKind::Val(val, field_op.layout.ty)
    });
    let fields = tcx.arena.alloc_from_iter(fields_iter);

    mir::DestructuredMirConstant { variant, fields }
}

>>>>>>> 46a16603658 (change thir to use mir::ConstantKind instead of ty::Const)
=======
#[instrument(skip(tcx), level = "debug")]
>>>>>>> 3ef9ce3e369 (implement valtree -> constvalue conversion)
pub(crate) fn deref_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    val: ty::Const<'tcx>,
) -> ty::Const<'tcx> {
    let pointee_type =
        val.ty().builtin_deref(true).expect("`deref_const` called on non-ptr type").ty;
    debug!(?pointee_type);

    tcx.mk_const(ty::ConstS { val: val.val(), ty: pointee_type })
}

#[instrument(skip(tcx), level = "debug")]
pub(crate) fn deref_mir_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    val: mir::ConstantKind<'tcx>,
) -> mir::ConstantKind<'tcx> {
    let ecx = mk_eval_cx(tcx, DUMMY_SP, param_env, false);
    let op = ecx.mir_const_to_op(&val, None).unwrap();
    let mplace = ecx.deref_operand(&op).unwrap();
    if let Some(alloc_id) = mplace.ptr.provenance {
        assert_eq!(
            tcx.get_global_alloc(alloc_id).unwrap().unwrap_memory().mutability,
            Mutability::Not,
            "deref_const cannot be used with mutable allocations as \
            that could allow pattern matching to observe mutable statics",
        );
    }

    let ty = match mplace.meta {
        MemPlaceMeta::None => mplace.layout.ty,
        MemPlaceMeta::Poison => bug!("poison metadata in `deref_const`: {:#?}", mplace),
        // In case of unsized types, figure out the real type behind.
        MemPlaceMeta::Meta(scalar) => match mplace.layout.ty.kind() {
            ty::Str => bug!("there's no sized equivalent of a `str`"),
            ty::Slice(elem_ty) => tcx.mk_array(*elem_ty, scalar.to_machine_usize(&tcx).unwrap()),
            _ => bug!(
                "type {} should not have metadata, but had {:?}",
                mplace.layout.ty,
                mplace.meta
            ),
        },
    };

    mir::ConstantKind::Val(op_to_const(&ecx, &mplace.into()), ty)
}
