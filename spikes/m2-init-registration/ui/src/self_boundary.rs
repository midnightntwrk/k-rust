struct Machine;

impl Machine {
    #[k::init(attempt_self)]
    fn init() -> Self {
        Self
    }
}

fn main() {}

