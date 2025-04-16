//@ build-pass
//@ aux-crate:my_api=my_api.rs
//@ aux-crate:my_api::utils=my_api::utils.rs
//@ edition: 2024

use my_api::root_function;
use my_api::utils::util;

fn main() {
    let _x = util::util_mod_helper();
    let _ = root_function();
}
