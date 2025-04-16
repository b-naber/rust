//@ aux-crate: my_api=open-ns-mod-my_api.rs
//@ aux-crate: my_api::utils=my_api::utils.rs
//@ edition: 2024

// FIXME need a way to set crate name of `open-ns-mod-my_api.rs` to `my_api`

fn main() {
    let _ = my_api::root_function();
    let _ = my_api::utils::root_helper();
    let _ = my_api::utils::utils_helper();
}
