pub extern "C" fn exported_abi() {}

pub fn f() -> u32 {
    let crate_count = 1;
    crate_count
}
