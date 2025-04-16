//#![crate_name = "my_api::utilz"]

pub mod util {
    pub fn util_mod_helper() -> String {
        format!("Helper from my_api::utils::util",)
    }
}

pub fn utils_helper() -> String {
    format!("Helper from my_api::utils!",)
}
