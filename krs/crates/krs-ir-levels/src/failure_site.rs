//! The innermost node a failed IR validation walk was visiting.
//!
//! The validators fail with errors whose shapes callers match exactly, and those errors carry no
//! node. The term walk knows the node it was visiting, and the compiler, which turns a failure into
//! a diagnostic, needs its origin: [`record`] runs a validation with a site installed for the
//! current thread, each term recursion that fails reports its node's origin, and the first report
//! wins, so the site is the innermost term that encloses the failure. Outside `record`, a report
//! goes nowhere.

use std::cell::RefCell;

use krs_ir::NodeOrigin;

thread_local! {
    static SITES: RefCell<Vec<Option<NodeOrigin>>> = const { RefCell::new(Vec::new()) };
}

/// Pops the site [`record`] pushed, also when the validation unwinds.
struct Installed;

impl Drop for Installed {
    fn drop(&mut self) {
        SITES.with(|sites| sites.borrow_mut().pop());
    }
}

/// Runs `validate` and returns its result with the origin of the innermost term a failed walk
/// inside it reported, `None` on success or when no term walk failed.
pub fn record<T, E>(validate: impl FnOnce() -> Result<T, E>) -> (Result<T, E>, Option<NodeOrigin>) {
    SITES.with(|sites| sites.borrow_mut().push(None));
    let installed = Installed;
    let result = validate();
    let site = SITES.with(|sites| sites.borrow_mut().last_mut().and_then(Option::take));
    drop(installed);
    let site = if result.is_err() { site } else { None };
    (result, site)
}

/// Reports that a walk failed inside the node of `origin`, unless a node inside it already did.
pub(crate) fn report(origin: &NodeOrigin) {
    SITES.with(|sites| {
        if let Some(site @ None) = sites.borrow_mut().last_mut() {
            *site = Some(origin.clone());
        }
    });
}
