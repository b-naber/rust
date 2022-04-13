// Not in interpret to make sure we do not use private implementation details

use std::convert::TryFrom;

use rustc_hir::Mutability;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{source_map::DUMMY_SP, symbol::Symbol};

use crate::interpret::{
    intern_const_alloc_recursive, ConstValue, InternKind, InterpCx, InterpResult, MemPlaceMeta,
    Scalar,
};
use valtrees::const_to_valtree_inner;

mod error;
mod eval_queries;
mod fn_queries;
mod machine;
mod valtrees;

pub use error::*;
pub use eval_queries::*;
pub use fn_queries::*;
pub use machine::*;
pub(crate) use valtrees::{const_to_valtree, valtree_to_const_value};

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
    ConstValue::Scalar(Scalar::from_pointer(loc_place.ptr.into_pointer_or_addr().unwrap(), &tcx))
}

/// Evaluates a constant and turns it into a type-level constant value.
#[instrument(skip(tcx), level = "debug")]
pub(crate) fn eval_to_valtree(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    cid: GlobalId<'tcx>,
) -> EvalToValTreeResult<'tcx> {
    let const_alloc = tcx.eval_to_allocation_raw(param_env.and(gid))?;
    let ecx = mk_eval_cx(
        tcx, DUMMY_SP, param_env,
        // It is absolutely crucial for soundness that
        // we do not read from static items or other mutable memory.
        false,
    );
    let place = ecx.raw_const_to_mplace(raw).unwrap();
    debug!(?place);

    const_to_valtree_inner(&ecx, &place)
}

/// Tries to destructure constants of type Array or Adt into the constants
/// of its fields.
pub(crate) fn try_destructure_const(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    _const: ty::Const<'tcx>,
) -> Option<mir::DestructuredConst<'tcx>> {
    if let ty::ConstKind::Value(valtree) = _const.val() {
        let branches = _const.val().unwrap_branch();

        let (fields, variant) = match _const.ty().kind() {
            ty::Array(inner_ty, _) => {
                // construct the consts for the elements of the array
                let field_consts = branches
                    .iter()
                    .map(|b| tcx.mk_const(ConstS { val: ConstKind::Value(b), ty: *inner_ty }))
                    .collect::<Vec<_>>();
                debug!(?field_consts);

                (field_consts, None)
            }
            ty::Adt(def, _) if def.variants().is_empty() => throw_ub!(Unreachable),
            ty::Adt(def, substs) if def.is_enum() => {
                let variant_idx = if def.is_enum() {
                    VariantIdx::from_u32(branches[0].unwrap_leaf().try_to_u32().unwrap())
                } else {
                    VariantIdx::from_u32(0)
                };
                let fields = def.variant(variant_idx).fields();
                let mut field_consts = vec![];

                // Note: First element in ValTree corresponds to variant of enum
                let mut valtree_idx = if def.is_enum() { 1 } else { 0 };
                for field in fields {
                    let field_ty = field.ty(tcx, substs);
                    let field_valtree = branches[valtree_idx]; // first element of branches is variant
                    let field_const = tcx.mk_const(ConstS { val: field_valtree, ty: field_ty });
                    field_consts.push(field_const);
                    valtree_idx += 1;
                }
                debug!(?field_consts);

                (field_consts, Some(variant_idx))
            }
            _ => bug!("cannot destructure constant {:?}", val),
        };

        let fields = tcx.arena.alloc_from_iter(fields.iter());

        Some(mir::DestructuredConst { variant, fields })
    } else {
        None
    }
}

#[instrument(skip(tcx), level = "debug")]
pub(crate) fn deref_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    val: ty::Const<'tcx>,
) -> ty::Const<'tcx> {
    trace!("deref_const: {:?}", val);
    let ecx = mk_eval_cx(tcx, DUMMY_SP, param_env, false);
    let op = ecx.const_to_op(val, None).unwrap();
    let mplace = ecx.deref_operand(&op).unwrap();
    if let Some(alloc_id) = mplace.ptr.provenance {
        assert_eq!(
            tcx.get_global_alloc(alloc_id).unwrap().unwrap_memory().inner().mutability,
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

    tcx.mk_const(ty::ConstS { val: ty::ConstKind::Value(op_to_const(&ecx, &mplace.into())), ty })
}
