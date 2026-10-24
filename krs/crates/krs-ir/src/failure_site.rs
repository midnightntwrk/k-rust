//! The innermost node a failed validation walk was visiting.
//!
//! Transport validation walks terms recursively and fails with errors whose shapes callers match
//! exactly; the errors carry no location. The walk knows the node it was visiting, and the
//! boundary that turns a failure into a diagnostic needs it: [`record`] runs a validation with a
//! site installed for the current thread, each recursion that fails [`report`]s its node, and the
//! first report wins, so the site is the innermost node that encloses the failure. Outside
//! `record`, a report goes nowhere.

use std::cell::RefCell;

use crate::ProvenanceKey;

thread_local! {
    static SITES: RefCell<Vec<Option<ProvenanceKey>>> = const { RefCell::new(Vec::new()) };
}

/// Pops the site [`record`] pushed, also when the validation unwinds.
struct Installed;

impl Drop for Installed {
    fn drop(&mut self) {
        SITES.with(|sites| sites.borrow_mut().pop());
    }
}

/// Runs `validate` and returns its result with the innermost node a failed walk inside it
/// reported, `None` on success or when no walk failed.
pub(crate) fn record<T, E>(
    validate: impl FnOnce() -> Result<T, E>,
) -> (Result<T, E>, Option<ProvenanceKey>) {
    SITES.with(|sites| sites.borrow_mut().push(None));
    let installed = Installed;
    let result = validate();
    let site = SITES.with(|sites| sites.borrow_mut().last_mut().and_then(Option::take));
    drop(installed);
    let site = if result.is_err() { site } else { None };
    (result, site)
}

/// Reports that a walk failed inside the node `key`, unless a node inside it already did.
pub(crate) fn report(key: &ProvenanceKey) {
    SITES.with(|sites| {
        if let Some(site @ None) = sites.borrow_mut().last_mut() {
            *site = Some(key.clone());
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ProvenanceRole;

    #[test]
    fn the_innermost_report_of_a_failed_recording_is_its_site() {
        let inner = ProvenanceKey::new(ProvenanceRole::RulePattern, 1);
        let outer = ProvenanceKey::new(ProvenanceRole::RulePattern, 0);
        report(&outer);
        let (result, site) = record(|| {
            report(&inner);
            report(&outer);
            Err::<(), _>(())
        });
        assert_eq!((result, site), (Err(()), Some(inner)));
        let (result, site) = record(|| {
            report(&outer);
            Ok::<_, ()>(())
        });
        assert_eq!((result, site), (Ok(()), None));
    }
}
