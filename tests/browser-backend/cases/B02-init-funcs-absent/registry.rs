// An inventory-style registry: registrations are linked into a list by
// constructors in `.init_array`, as inventory 0.3 does on wasm
// (spikes/BL-003/backend-control/init-array.rs and the original collector-ab).
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

pub struct Node {
    pub name: &'static str,
    pub next: AtomicPtr<Node>,
}

static HEAD: AtomicPtr<Node> = AtomicPtr::new(ptr::null_mut());

pub fn submit(node: &'static Node) {
    let node_ptr = node as *const Node as *mut Node;
    let mut head = HEAD.load(Ordering::Acquire);
    loop {
        node.next.store(head, Ordering::Relaxed);
        match HEAD.compare_exchange(head, node_ptr, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => return,
            Err(current) => head = current,
        }
    }
}

pub fn names() -> Vec<&'static str> {
    let mut out = Vec::new();
    let mut at = HEAD.load(Ordering::Acquire);
    while let Some(node) = unsafe { at.as_ref() } {
        out.push(node.name);
        at = node.next.load(Ordering::Acquire);
    }
    out
}
