use k::KResult;

k::sorts! {
    #[k::bracket("(", ")")]
    #[serde(skip)]
    M: KResult;
}

pub fn f() -> Vec<&'static str> {
    vec![include_str!("x"), env ! ("HOME")]
}

k::rules! {
    for M;
    extern crate alloc;
    boom: lazy!() => Bar();
}

pub fn g() -> bool {
    if !(true) { return !(false) } else { true }
}
