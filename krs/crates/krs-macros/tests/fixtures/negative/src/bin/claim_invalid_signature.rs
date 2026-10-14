use krs_macros::claim;

#[claim(all_paths, label = "term-shaped")]
fn invalid(value: renamed_krs::Term<renamed_krs::builtin::Int>) -> renamed_krs::Term<renamed_krs::builtin::Int> { //~ ERROR a configuration-rule subject must be `cells! { ... }`
    value
}

fn main() {}
