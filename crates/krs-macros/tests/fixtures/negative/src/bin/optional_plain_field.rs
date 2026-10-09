#[renamed_krs::configuration]
struct Machine {
    #[renamed_krs::cell]
    k: renamed_krs::builtin::KSequence,
    #[renamed_krs::cell(multiplicity = "?")]
    counter: renamed_krs::builtin::Int, //~ ERROR a `multiplicity = "?"` cell is declared `Option<T>`
}

fn main() {}
