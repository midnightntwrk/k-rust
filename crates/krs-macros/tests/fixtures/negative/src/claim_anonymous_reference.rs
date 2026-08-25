use krs_macros::claim;

#[claim(all_paths, label = "anonymous-reference")]
fn invalid(
    cells! {
        k: renamed_krs::configuration::KCell(
            renamed_krs::anonymous!(renamed_krs::builtin::Bool, "_B"),
            tail @ ..
        ),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: renamed_krs::configuration::KCell(_B, ..tail),
        ..state
    }
}

fn main() {}
