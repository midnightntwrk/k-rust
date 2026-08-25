use krs_macros::claim;

#[claim(all_paths, label = "term-shaped")]
fn invalid(value: renamed_krs::Term<renamed_krs::builtin::Int>) -> renamed_krs::Term<renamed_krs::builtin::Int> {
    value
}

fn main() {}
