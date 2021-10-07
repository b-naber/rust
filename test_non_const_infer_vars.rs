trait Foo {
    type T;
}

impl Foo for u8 {
  type T = u32;
}

impl Foo for u32 {
  type T = u32;
}

fn foo<T: Foo>(_: [T::T; 9]) -> T {
    todo!()
}

pub fn bar() {
    //foo::<u32>([0;1]);

    // This equivalent line does not ICE
    //foo::<u8>([0; 1]);

    // This ICEs
    //let _: &str = foo([0; 9]);
    let _ = foo([0; 9]);
}

fn main() {}
