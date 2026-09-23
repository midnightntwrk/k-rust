pub const NAME: &str = env!("CARGO_PKG_NAME");

pub fn home() -> Option<&'static str> {
    std::option_env!("HOME")
}
