pub const TEXT: &str = concat!("include", "_str");

pub fn include() -> &'static str {
    stringify!(include_str)
}
