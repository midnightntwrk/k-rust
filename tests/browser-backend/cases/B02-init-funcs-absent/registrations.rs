// Two registrations submitted by `.init_array` constructors.
use b02_registry::{submit, Node};
use std::ptr;
use std::sync::atomic::AtomicPtr;

static ALPHA: Node = Node { name: "alpha", next: AtomicPtr::new(ptr::null_mut()) };
static BETA: Node = Node { name: "beta", next: AtomicPtr::new(ptr::null_mut()) };

extern "C" fn submit_alpha() {
    submit(&ALPHA);
}

extern "C" fn submit_beta() {
    submit(&BETA);
}

#[used]
#[unsafe(link_section = ".init_array")]
static SUBMIT_ALPHA: extern "C" fn() = submit_alpha;

#[used]
#[unsafe(link_section = ".init_array")]
static SUBMIT_BETA: extern "C" fn() = submit_beta;

pub fn force_link() -> usize {
    2
}
