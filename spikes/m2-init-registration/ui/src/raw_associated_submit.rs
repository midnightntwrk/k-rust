struct Machine;

impl Machine {
    fn descriptor() -> k::Descriptor {
        panic!()
    }

    // inventory 0.3.24 expands this to `const _: ()`, which is not a valid
    // associated item unless another named associated const wraps it.
    k::__submit!(Machine::descriptor);
}

fn main() {}
