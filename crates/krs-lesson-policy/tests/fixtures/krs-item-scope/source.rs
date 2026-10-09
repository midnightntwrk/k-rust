mod semantics {
    k::sorts! {
        M: k::KResult;
    }

    #[k::configuration]
    pub struct Machine {
        #[k::cell]
        pub k: k::builtin::KSequence,
    }
}

pub fn helper() {
    k::rules! {
        for M;
    }
}

#[k::spec_module(imports = [crate])]
mod proofs {
    mod nested {
        k::rules! {
            for M;
        }
    }
}
