use krs_macros::init;

struct Machine;

impl Machine {
    #[init]
    fn init(first: renamed_krs::builtin::Id, second: renamed_krs::builtin::Id) -> Self { //~ ERROR at most one configuration variable may be marked `main`
        Self { k: renamed_krs::k![first, second] }
    }
}

fn main() {}
