//! Author fixture with two same-named initializers and a direct explicit-path variant.

use std::sync::atomic::{AtomicUsize, Ordering};

static RUNTIME_INIT_CALLS: AtomicUsize = AtomicUsize::new(0);

pub mod paired {
    use super::{Ordering, RUNTIME_INIT_CALLS};

    #[k::configuration]
    pub struct Alpha;

    impl Alpha {
        #[k::init]
        pub fn init() -> Self {
            RUNTIME_INIT_CALLS.fetch_add(1, Ordering::SeqCst);
            Self
        }
    }

    #[k::configuration]
    pub struct Beta;

    impl Beta {
        #[k::init]
        pub fn init() -> Self {
            RUNTIME_INIT_CALLS.fetch_add(1, Ordering::SeqCst);
            Self
        }
    }

    pub fn ordinary_navigation_surface() {
        let _: fn() -> Alpha = Alpha::init;
        let _: fn() -> Beta = Beta::init;
    }
}

pub mod explicit {
    use super::{Ordering, RUNTIME_INIT_CALLS};

    pub struct Gamma;

    impl Gamma {
        #[k::init(config = Gamma)]
        pub fn init() -> Self {
            RUNTIME_INIT_CALLS.fetch_add(1, Ordering::SeqCst);
            Self
        }
    }

    pub fn ordinary_navigation_surface() {
        let _: fn() -> Gamma = Gamma::init;
    }
}

/// Explicit linker-retention edge called by the generated collector binary.
pub fn retain_for_collector() {
    paired::ordinary_navigation_surface();
    explicit::ordinary_navigation_surface();
}

/// Proves descriptor collection did not execute any authored initializer.
#[must_use]
pub fn runtime_init_calls() -> usize {
    RUNTIME_INIT_CALLS.load(Ordering::SeqCst)
}

