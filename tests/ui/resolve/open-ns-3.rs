//@ aux-crate: my_api=open-ns-mod-my_api.rs
//@ aux-crate: my_api::utils=open-ns-my_api_utils.rs
//@ compile-flags: -Z namespaced-crates
//@ edition: 2024
//@ build-pass

fn main() {
    let _ = my_api::root_function();
    let _ = my_api::utils::utils_helper();
}
