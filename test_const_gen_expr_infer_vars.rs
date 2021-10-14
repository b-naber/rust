#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

trait Foo {
    const N: usize;
}

impl Foo for u8 {
    const N: usize = 1;
}

impl Foo for u32 {
  const N: usize = 32;
}

fn foo<T: Foo>(_: [u8; T::N]) -> T {
    todo!()
}

pub fn bar() {
    //foo::<u32>([0;1]);

    // This equivalent line does not ICE
    //foo::<u8>([0; 1]);

    // This ICEs
    let _ : u8 = foo([0; 1]);

    // type check error caught after stalls
    let _ = foo([0; 1]);
}

fn main() {}
