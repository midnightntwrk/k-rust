#[derive(Debug, Serialize, ::serde::Deserialize)]
pub struct A;

#[no_mangle]
pub fn exported() {}

#[rustfmt::skip]
pub fn tool() {}

pub fn body() {
    let _ = lazy_static!(x);
    let _ = k::constructors!(y);
}

#[k::syntax("stray")]
pub struct Stray;

#[derive(Default)]
pub enum Choice {
    #[default]
    First,
}
