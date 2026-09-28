#[renamed_krs::configuration]
struct Machine {
    #[renamed_krs::cell]
    k: renamed_krs::builtin::KSequence,
    env: renamed_krs::builtin::Map, //~ ERROR wrapper-free configurations require `#[k::cell]` on every plain field
}

fn main() {}
