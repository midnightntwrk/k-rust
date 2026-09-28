use krs_macros::init;

struct Machine;

impl Machine {
    #[init]
    fn init() -> Self {
        if true { Self } else { Self } //~ ERROR statements, semicolons, control flow, mutation, and early return are forbidden
    }
}

fn main() {}
