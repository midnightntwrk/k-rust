use krs_macros::claim;

#[claim(all_paths, label = "fresh-claim")]
#[renamed_krs::fresh(n: renamed_krs::builtin::int::Int)] //~ ERROR fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context, context alias, anywhere rule, or heat or cool rule
fn invalid() {}

fn main() {}
