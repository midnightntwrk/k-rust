trait HasInit {
    fn init() -> Self;
}

struct Machine;

impl HasInit for Machine {
    #[k::init]
    fn init() -> Self {
        Self
    }
}

fn main() {}

