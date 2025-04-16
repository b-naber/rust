//@ build-pass
//@ aux-crate: my_api=my_api.rs
//@ aux-crate: my_api::utils=my_api::utils.rs
//@ aux-crate: my_api::core=my_api::core.rs
//@ edition: 2024

use my_api::core::{core_fn, core_fn2};
use my_api::utils::*;
use my_api::*;

fn main() {
    let _ = root_function();
    let _ = utils_helper();
    let _ = core_fn();
    let _ = core_fn2();
}
