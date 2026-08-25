use krs_macros::init;

struct Machine;

impl Machine {
    #[init]
    fn init() -> Self {
        if true { Self } else { Self }
    }
}

fn main() {}
