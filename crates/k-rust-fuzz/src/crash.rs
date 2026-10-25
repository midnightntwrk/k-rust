//! Crash containment: the panic hook, the catch sites' discipline and crash signatures
//! (FZ-CRASH; ARCHITECTURE 5.3, 5.4, 9.3).
//!
//! # Catching
//!
//! [`catch`] runs a closure under `catch_unwind` and turns a panic into a [`PanicRecord`]. A
//! process-wide panic hook ([`install`]), installed once and chaining to the hook it replaced,
//! records the message and the location of a panic raised while a catch site on the same thread
//! is active, and prints nothing for it; outside every catch site it calls the previous hook, so
//! a panic elsewhere (a test's own) prints as before. Two thread-locals carry the discipline:
//! `CAPTURE`, whether a catch site is active on this thread, and `LAST`, the last record. Every
//! catch site clears `LAST` on entry and again when its closure returns, and takes it only when
//! the closure unwound, so a panic that code inside the closure caught and handled itself (the
//! backend's own containment of a refused stack segment) leaves nothing behind. `resume_unwind`
//! does not call the hook, so a re-raised panic keeps the record, and the location, of the panic
//! that raised it. The hook reads both thread-locals with `try_with` and `try_borrow_mut`, so a
//! panic in a thread-local destructor falls through to the previous hook instead of panicking
//! again inside this one.
//!
//! The hook is installed only in builds that unwind (`cfg(panic = "unwind")`): where a panic
//! aborts (WebAssembly, a `panic = "abort"` profile) nothing is caught, and suppressing the
//! message would leave the abort silent. A hook an embedder installs after the campaign's
//! replaces it: the record then has no location, and the signature falls back to the message
//! (`site-kind: message`; ARCHITECTURE 5.4 lists this among the exclusions).
//!
//! # What survives a caught panic
//!
//! A catch site wraps its closure in `AssertUnwindSafe`. What the closure may leave half-changed
//! is discarded after the panic: the campaign rebuilds the case's backends, sessions, solvers,
//! executors and assemblers (`CaseRunner::recover`). Thread-locals and process statics survive;
//! the backend restores its thread-locals on unwind through drop guards, and its statics are
//! insert-only or pure (FZ-CRASH design, section 3).
//!
//! # Signatures
//!
//! Crashes are told apart by their [`CrashSignature`]: kind, side, stage, and the site, which is
//! the panic's location normalized to start at its crate's `src` directory, or, for an internal
//! error, for a panic without a location and for one located in toolchain or generated source,
//! the message's class ([`message_class`]).

use std::{
    cell::{Cell, RefCell},
    panic::{AssertUnwindSafe, catch_unwind},
};

use crate::report::{CrashKind, CrashSide, CrashSignature, CrashStage, PanicRecord, SiteKind};

/// The texts of the panics `stacker` 0.1.21 raises when the system refuses to map a stack
/// segment (`mmap_stack_restore_guard.rs`, `alloc_stack_restore_guard.rs`). A panic whose message
/// holds one of them is the host refusing memory, outside the determinism contract, not a
/// defect of k-rust (`docs/compatibility.md`, "a guarded recursion on a host out of memory may
/// panic"). `stacker` gives no typed cause, so these texts are pinned to the locked version: a
/// test fails when `Cargo.lock` moves `stacker` off 0.1.21, so that an upgrade re-checks them.
pub(crate) const STACKER_MAPPING_TEXTS: [&str; 3] = [
    "mmap failed to allocate stack",
    "mprotect/mmap failed",
    "unable to allocate stack",
];

/// The most crash signatures a report keeps (D32): further signatures' cases are counted in
/// `crashes-omitted`.
pub(crate) const MAX_CRASH_SIGNATURES: usize = 16;

/// The most shrink candidates the engine screens for one crash signature: each crashing
/// candidate costs a rebuild of the campaign's backends, so the hit shrinker's cap
/// (`MAX_SHRINK_RUNS`, 256) would be too many.
pub(crate) const MAX_CRASH_SHRINK_RUNS: u64 = 32;

/// The most crash shrink candidates the engine screens in one campaign.
pub(crate) const MAX_CAMPAIGN_CRASH_SHRINK_RUNS: u64 = 64;

/// The longest message a crash finding keeps, in bytes (cut at a character boundary).
pub(crate) const MAX_MESSAGE_BYTES: usize = 1024;

/// Whether a panic with `message` is the host refusing to map a stack segment
/// ([`STACKER_MAPPING_TEXTS`]).
pub(crate) fn is_stack_mapping_refusal(message: &str) -> bool {
    STACKER_MAPPING_TEXTS
        .iter()
        .any(|text| message.contains(text))
}

thread_local! {
    /// Whether a catch site is active on this thread.
    static CAPTURE: Cell<bool> = const { Cell::new(false) };
    /// The record of the last panic raised on this thread while a catch site was active.
    static LAST: RefCell<Option<PanicRecord>> = const { RefCell::new(None) };
}

/// Install the chaining panic hook, once per process; a no-op where panics do not unwind.
pub(crate) fn install() {
    #[cfg(panic = "unwind")]
    {
        static INSTALL: std::sync::Once = std::sync::Once::new();
        INSTALL.call_once(|| {
            let previous = std::panic::take_hook();
            std::panic::set_hook(Box::new(move |info| {
                let capturing = CAPTURE.try_with(Cell::get).unwrap_or(false);
                if capturing {
                    let record = PanicRecord {
                        message: payload_text(info.payload()),
                        location: info.location().map(|location| {
                            format!(
                                "{}:{}:{}",
                                location.file(),
                                location.line(),
                                location.column()
                            )
                        }),
                    };
                    let stored = LAST
                        .try_with(|last| match last.try_borrow_mut() {
                            Ok(mut slot) => {
                                *slot = Some(record);
                                true
                            }
                            Err(_) => false,
                        })
                        .unwrap_or(false);
                    if stored {
                        return;
                    }
                }
                previous(info);
            }));
        });
    }
}

fn clear_last() {
    let _ = LAST.try_with(|last| {
        if let Ok(mut slot) = last.try_borrow_mut() {
            *slot = None;
        }
    });
}

fn take_last() -> Option<PanicRecord> {
    LAST.try_with(|last| last.try_borrow_mut().ok().and_then(|mut slot| slot.take()))
        .ok()
        .flatten()
}

/// Whether this thread holds no panic record (the crash tests' check of the clearing
/// discipline).
#[cfg(test)]
pub(crate) fn no_record() -> bool {
    LAST.with(|last| last.borrow().is_none())
}

/// The text of a panic payload: the `&str` or `String` it holds, or a placeholder naming that
/// it holds neither.
fn payload_text(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(text) = payload.downcast_ref::<&str>() {
        (*text).to_owned()
    } else if let Some(text) = payload.downcast_ref::<String>() {
        text.clone()
    } else {
        "a panic whose payload is not a string".to_owned()
    }
}

/// Run `work`; a panic it raises becomes `Err` with its record (module documentation,
/// "Catching"). The record has the location the hook saw when the hook ran, and only the
/// payload's text otherwise.
pub(crate) fn catch<R>(work: impl FnOnce() -> R) -> Result<R, PanicRecord> {
    install();
    let outer = CAPTURE
        .try_with(|capture| capture.replace(true))
        .unwrap_or(false);
    clear_last();
    let result = catch_unwind(AssertUnwindSafe(work));
    let _ = CAPTURE.try_with(|capture| capture.set(outer));
    match result {
        Ok(value) => {
            clear_last();
            Ok(value)
        }
        Err(payload) => {
            let record = take_last().unwrap_or_else(|| PanicRecord {
                message: payload_text(&*payload),
                location: None,
            });
            Err(record)
        }
    }
}

/// `message` cut to [`MAX_MESSAGE_BYTES`] at a character boundary, with `…` when cut.
pub(crate) fn bounded_message(message: &str) -> String {
    if message.len() <= MAX_MESSAGE_BYTES {
        return message.to_owned();
    }
    let mut end = MAX_MESSAGE_BYTES;
    while !message.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &message[..end])
}

/// The signature of a crash of `kind` on `side` at `stage`: for a panic with a location outside
/// toolchain and generated source, that location normalized ([`normalized_location`]); otherwise
/// the message's class ([`message_class`]).
pub(crate) fn signature(
    kind: CrashKind,
    side: CrashSide,
    stage: CrashStage,
    message: &str,
    location: Option<&str>,
) -> CrashSignature {
    let located = match kind {
        CrashKind::Panic => location.and_then(normalized_location),
        CrashKind::InternalError => None,
    };
    let (site_kind, place) = match located {
        Some(place) => (SiteKind::Location, place),
        None => (SiteKind::Message, message_class(message)),
    };
    CrashSignature {
        kind,
        side,
        stage,
        site_kind,
        site: place,
    }
}

/// A panic location `file:line:column` normalized so that one source gives one site wherever it
/// was built: the path starts at its crate's directory (the component before the last `src`),
/// with a `-<version>` suffix stripped from that directory (a registry build names the crate
/// `stacker-0.1.21`, a workspace build `stacker`), and `\` read as `/`. `None` for a location in
/// the toolchain's sources (`/rustc/…`, `library/core/src`, `library/std/src`,
/// `library/alloc/src`), whose line numbers depend on the toolchain the build identity does not
/// name, and for generated source under a build script's `OUT_DIR`.
pub(crate) fn normalized_location(location: &str) -> Option<String> {
    let location = location.replace('\\', "/");
    // `file:line:column`: the file may itself hold a `:` (a Windows drive).
    let mut parts = location.rsplitn(3, ':');
    let column = parts.next()?;
    let line = parts.next()?;
    let file = parts.next()?;
    if column.parse::<u32>().is_err() || line.parse::<u32>().is_err() {
        return None;
    }
    let toolchain = file.contains("/rustc/")
        || file.starts_with("rustc/")
        || ["library/core/src", "library/std/src", "library/alloc/src"]
            .iter()
            .any(|library| file.starts_with(library) || file.contains(&format!("/{library}")));
    let generated = file.contains("/build/") && file.contains("/out/");
    if toolchain || generated {
        return None;
    }
    let components: Vec<&str> = file.split('/').collect();
    let file = match components.iter().rposition(|component| *component == "src") {
        Some(src) if src > 0 => {
            let krate = strip_version(components[src - 1]);
            let rest = components[src..].join("/");
            format!("{krate}/{rest}")
        }
        _ => file.to_owned(),
    };
    Some(format!("{file}:{line}:{column}"))
}

/// `name` without a trailing `-<version>`, where the version starts with a digit and holds only
/// digits, dots and the characters of a pre-release or build suffix.
fn strip_version(name: &str) -> &str {
    match name.rsplit_once('-') {
        Some((krate, version))
            if !krate.is_empty()
                && version.starts_with(|c: char| c.is_ascii_digit())
                && version.contains('.')
                && version
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '+' | '-')) =>
        {
            krate
        }
        _ => name,
    }
}

/// The class of a message, which stands for the site of a crash without a usable location: its
/// first line, with every span between backticks, quotes or double quotes masked as `…`, cut
/// before its first `:`, every run of digits masked as `N`, at most 200 characters. A message
/// that formats a term, a number or a name into its text gives one class for one defect, so the
/// signature cap is not spent on the values one defect printed.
pub(crate) fn message_class(message: &str) -> String {
    let line = message.lines().next().unwrap_or("");
    let mut masked = String::with_capacity(line.len());
    let mut open: Option<char> = None;
    for c in line.chars() {
        match open {
            Some(delimiter) if c == delimiter => {
                masked.push('…');
                masked.push(c);
                open = None;
            }
            Some(_) => {}
            None if matches!(c, '`' | '\'' | '"') => {
                masked.push(c);
                open = Some(c);
            }
            None => masked.push(c),
        }
    }
    if open.is_some() {
        masked.push('…');
    }
    let cut = masked.split(':').next().unwrap_or("").trim_end();
    let mut class = String::with_capacity(cut.len());
    let mut in_digits = false;
    for c in cut.chars() {
        if c.is_ascii_digit() {
            if !in_digits {
                class.push('N');
            }
            in_digits = true;
        } else {
            class.push(c);
            in_digits = false;
        }
    }
    class.chars().take(200).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_location_starts_at_its_crate_without_the_version() {
        assert_eq!(
            normalized_location(
                "/home/u/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/stacker-0.1.21/src/lib.rs:12:5"
            )
            .as_deref(),
            Some("stacker/src/lib.rs:12:5")
        );
        assert_eq!(
            normalized_location("crates/k-rust-backend/src/term.rs:40:9").as_deref(),
            Some("k-rust-backend/src/term.rs:40:9")
        );
        assert_eq!(
            normalized_location("/build/k-rust/crates/k-rust/src/backend/mod.rs:1:2").as_deref(),
            Some("k-rust/src/backend/mod.rs:1:2")
        );
        // A crate whose name ends in a number is no version.
        assert_eq!(
            normalized_location("crates/base-64/src/lib.rs:1:1").as_deref(),
            Some("base-64/src/lib.rs:1:1")
        );
        assert_eq!(
            normalized_location(r"C:\work\k-rust\crates\k-rust\src\lib.rs:3:4").as_deref(),
            Some("k-rust/src/lib.rs:3:4")
        );
        assert_eq!(
            normalized_location("crates/k-rust-fuzz/tests/crash.rs:60:17").as_deref(),
            Some("crates/k-rust-fuzz/tests/crash.rs:60:17")
        );
    }

    #[test]
    fn a_toolchain_or_generated_location_falls_back_to_the_message() {
        for location in [
            "/rustc/90b35a6239c3d8bdabc530a6a0816f7ff89a0aaf/library/core/src/option.rs:2011:5",
            "library/std/src/thread/mod.rs:10:1",
            "/home/u/.rustup/toolchains/stable/lib/rustlib/src/rust/library/alloc/src/vec/mod.rs:1:1",
            "/var/tmp/target/debug/build/k-rust-1a2b/out/generated.rs:4:2",
        ] {
            assert_eq!(normalized_location(location), None, "{location}");
            let signature = signature(
                CrashKind::Panic,
                CrashSide::Baseline,
                CrashStage::Execute,
                "called `Option::unwrap()` on a `None` value",
                Some(location),
            );
            assert_eq!(signature.site_kind, SiteKind::Message);
            assert_eq!(signature.site, "called `…` on a `…` value");
        }
    }

    #[test]
    fn a_message_class_masks_values_and_keeps_the_text_before_its_first_colon() {
        assert_eq!(
            message_class("index out of bounds: the len is 3 but the index is 7"),
            "index out of bounds"
        );
        assert_eq!(
            message_class("unexpected term `foo(1, 2)` at depth 12\nmore"),
            "unexpected term `…` at depth N"
        );
        assert_eq!(message_class("no rule for 'x::y': 42"), "no rule for '…'");
        // Two messages of one defect that format different values share their class.
        assert_eq!(
            message_class("could not encode KORE JSON: depth 9123 exceeds 4096"),
            message_class("could not encode KORE JSON: depth 17 exceeds 4096")
        );
    }

    #[test]
    fn an_internal_error_is_always_classed_by_its_message() {
        let signature = signature(
            CrashKind::InternalError,
            CrashSide::Mutant,
            CrashStage::Judge,
            "the state of leaf 3 does not decode as KORE",
            Some("crates/k-rust/src/lib.rs:1:1"),
        );
        assert_eq!(signature.site_kind, SiteKind::Message);
        assert_eq!(
            signature.site,
            "the state of leaf N does not decode as KORE"
        );
    }

    #[test]
    fn stackers_mapping_texts_are_recognized() {
        assert!(is_stack_mapping_refusal(
            "assertion `left != right` failed: mmap failed to allocate stack: Cannot allocate memory (os error 12)"
        ));
        assert!(is_stack_mapping_refusal("mprotect/mmap failed: x"));
        assert!(is_stack_mapping_refusal("unable to allocate stack"));
        assert!(!is_stack_mapping_refusal("index out of bounds"));
    }

    /// The pinned texts are `stacker` 0.1.21's: an upgrade must re-check them.
    #[test]
    fn the_locked_stacker_is_the_version_whose_texts_are_pinned() {
        let lock = include_str!("../../../Cargo.lock");
        let versions: Vec<&str> = lock
            .split("[[package]]")
            .filter(|package| package.contains("\nname = \"stacker\"\n"))
            .filter_map(|package| {
                package
                    .lines()
                    .find_map(|line| line.strip_prefix("version = "))
            })
            .collect();
        assert_eq!(
            versions,
            ["\"0.1.21\""],
            "stacker moved: re-check crash::STACKER_MAPPING_TEXTS against its sources"
        );
    }

    #[test]
    fn a_caught_panic_has_its_message_and_location() {
        let caught = catch(|| -> u32 { panic!("boom {}", 7) }).expect_err("it panics");
        assert_eq!(caught.message, "boom 7");
        let location = caught.location.expect("the hook saw the location");
        assert!(location.contains("crash.rs"), "{location}");
    }

    /// (H) A panic the closure catches and handles itself leaves no record on `Ok`: the next
    /// panic that escapes is reported with its own message, never the handled one.
    #[test]
    fn a_panic_handled_inside_the_closure_leaves_no_record() {
        let value = catch(|| {
            let inner = std::panic::catch_unwind(|| panic!("handled inside"));
            assert!(inner.is_err());
            5
        })
        .expect("the closure returns");
        assert_eq!(value, 5);
        assert!(take_last().is_none(), "a handled panic left its record");
        let escaped = catch(|| -> u32 { std::panic::resume_unwind(Box::new("re-raised")) })
            .expect_err("it unwinds");
        // `resume_unwind` runs no hook: the record is the payload's, never the handled panic's.
        assert_eq!(escaped.message, "re-raised");
        assert_eq!(escaped.location, None);
    }

    /// A panic outside every catch site is not recorded (the previous hook prints it).
    #[test]
    fn a_panic_outside_a_catch_site_is_not_recorded() {
        install();
        let result = std::panic::catch_unwind(|| panic!("outside"));
        assert!(result.is_err());
        assert!(take_last().is_none());
    }
}
