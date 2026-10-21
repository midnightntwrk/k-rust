//! Re-pin L1-4: the warm path's memos (`kink_flow::memo`) change nothing but wall time, and a
//! record is used only under exactly its key.
//!
//! - With and without memos (`MemoUse::On` against `MemoUse::Off`), cold then warm, the run
//!   documents (wall times removed), the outcome cache, the killer hints and the stored report are
//!   byte-equal, on a `.k` and a Markdown fixture with every status.
//! - A forged record under exactly the current key is used (the positive control that the memo
//!   is read at all), and `run --verify` reports it and writes nothing.
//! - The same forged record under a key that differs in any one input (kink's build, one
//!   component of kink's semantics identity, the memo version, the specification digest, the
//!   mutation's edits) is not used: the row is the live one and the record is rewritten. So is
//!   every record after a byte of a source file or of the mutation's text changes.
//! - Re-pin L1-4-tail (review L1-4-2 N1): each key is built here member by member from its inputs
//!   (`resolution_key_of`, `census_key_of`), not from `memo`'s functions, and must equal `memo`'s:
//!   a key that omits an input fails, which a stale key made by editing a copy of `memo`'s key
//!   cannot show (the copy keeps the member the key omits). A source file changed after the
//!   admission read it and before resolution reads no record (`memo::sources_unchanged`).

// Under Z3 the tests of the caches (off by design) compile out, and their helpers with them.
#![cfg_attr(feature = "z3", allow(dead_code, unused_imports))]

use kink_corpus::Store;
use kink_flow::{
    EditAction, FlowManifest, Mutation, MutationList, admit_spec,
    digest::spec_digest,
    memo::{self, CENSUS_MEMO_VERSION, Facts, MemoUse, RESOLUTION_MEMO_VERSION},
    results::CACHE_DIRECTORY,
    search::{ProgramOrder, RunMode, RunOptions, run_with},
};
use kink_patch::Sha256Digest;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(&name));
        } else {
            fs::copy(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// A private copy of the testdata/flow fixture `name`, as `tag`.
fn fixture(name: &str, tag: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-memo-{}", std::process::id()))
        .join(format!("{}-{tag}", name.replace('/', "_")));
    let _ = fs::remove_dir_all(&dir);
    copy_dir(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../testdata/flow")
            .join(name),
        &dir,
    );
    dir
}

/// The document without its wall times, the only fields that differ between equal runs.
fn timeless(value: &Value) -> Value {
    match value {
        Value::Object(map) => Value::Object(
            map.iter()
                .filter(|(key, _)| {
                    !matches!(key.as_str(), "call_wall_ms" | "wall_ms" | "baseline_ms")
                })
                .map(|(key, value)| (key.clone(), timeless(value)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(timeless).collect()),
        other => other.clone(),
    }
}

/// Every file under `dir` of the cache directory `cache`, by relative path, with its bytes.
fn files(cache: &Path, dir: &str) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(root: &Path, dir: &Path, files: &mut BTreeMap<PathBuf, Vec<u8>>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(root, &path, files);
            } else {
                files.insert(
                    path.strip_prefix(root).unwrap().to_owned(),
                    fs::read(&path).unwrap(),
                );
            }
        }
    }
    let mut found = BTreeMap::new();
    walk(cache, &cache.join(dir), &mut found);
    found
}

/// The outcome cache and the hints.
fn stores(cache: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    let mut stores = files(cache, "outcomes");
    if let Ok(bytes) = fs::read(cache.join("hints.json")) {
        stores.insert(PathBuf::from("hints.json"), bytes);
    }
    stores
}

fn search(dir: &Path, list: &str, memo: MemoUse, mode: RunMode) -> (Value, bool) {
    search_only(dir, list, memo, mode, &[])
}

/// [`search`] with `--only` for each of `only`.
fn search_only(
    dir: &Path,
    list: &str,
    memo: MemoUse,
    mode: RunMode,
    only: &[&str],
) -> (Value, bool) {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let mutations = MutationList::read(&dir.join(list)).unwrap();
    run_with(
        &manifest,
        &mutations,
        &RunOptions {
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: Some(1),
            memo,
        },
        mode,
    )
}

fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
}

/// What a memo key is built from: the specification digest of the fixture's admission, kink's
/// build and the mutation `id` of `list`.
struct KeyParts {
    spec: kink_patch::Sha256Digest,
    build: kink_patch::Sha256Digest,
    mutation: Mutation,
}

fn key_parts(dir: &Path, list: &str, id: &str) -> KeyParts {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let (_, admitted) = admit_spec(&manifest);
    let (spec, _) = admitted.expect("the fixture is admitted");
    let mutations = MutationList::read(&dir.join(list)).unwrap();
    KeyParts {
        spec: spec_digest(&manifest, &spec.loaded.files),
        build: kink_campaign::kink_build().expect("the test binary is readable"),
        mutation: mutations
            .mutations
            .into_iter()
            .find(|mutation| mutation.id == id)
            .unwrap(),
    }
}

/// A mutation's edits as the resolution key names them, built here from the edits (not by
/// `memo::mutation_entry`): every field of every edit, in order.
fn edits_of(mutation: &Mutation) -> Value {
    mutation
        .edits
        .iter()
        .map(|edit| {
            let (find, replace, delete) = match &edit.action {
                EditAction::Replace { find, replace } => (json!(find), json!(replace), false),
                EditAction::Delete => (Value::Null, Value::Null, true),
            };
            json!({
                "file": edit.file,
                "rule": edit.rule,
                "line": edit.line,
                "find": find,
                "replace": replace,
                "delete": delete,
            })
        })
        .collect()
}

/// A resolution memo key built here, member by member, from every input it must name (memo
/// module docs): the memo version, kink's build, kink's semantics identity, the specification
/// digest and the mutation's edits. Re-pin L1-4-tail: a key `memo::resolution_key` builds
/// without one of them differs from this one.
fn resolution_key_of(
    version: &str,
    build: Sha256Digest,
    kink: &Value,
    spec: Sha256Digest,
    mutation: &Mutation,
) -> Value {
    json!({
        "version": version,
        "kink_build": build.to_string(),
        "kink": kink,
        "spec": spec.to_string(),
        "mutation": edits_of(mutation),
    })
}

/// A census memo key built here from every input it must name: the memo version, kink's build,
/// kink's semantics identity and the specification digest.
fn census_key_of(version: &str, build: Sha256Digest, kink: &Value, spec: Sha256Digest) -> Value {
    json!({
        "version": version,
        "kink_build": build.to_string(),
        "kink": kink,
        "spec": spec.to_string(),
    })
}

/// kink's semantics identity with one component changed: the identity of another kink.
fn another_identity() -> Value {
    let mut identity = kink_campaign::kink_identity();
    identity["mutant_consistency"] = json!("kink-native/mutant-consistency/v0");
    assert_ne!(identity, kink_campaign::kink_identity());
    identity
}

/// The rounds of [`compare`]: cold and warm in the kink tier, and a second warm round in the
/// heavy tier.
const ROUNDS: [&str; 3] = ["cold", "warm", "warm again"];

fn compare(name: &str, list: &str, rounds: &[&str]) {
    // The round count is in the tag: under `cargo test` the kink-tier and heavy variants share a
    // process, and so the directory root.
    let with = fixture(name, &format!("{list}-{}-on", rounds.len()));
    let without = fixture(name, &format!("{list}-{}-off", rounds.len()));
    for round in rounds {
        let (on, on_ok) = search(&with, list, MemoUse::On, RunMode::Search);
        let (off, off_ok) = search(&without, list, MemoUse::Off, RunMode::Search);
        assert_eq!(on_ok, off_ok, "{name} {list} {round}");
        assert_eq!(
            timeless(&on),
            timeless(&off),
            "STOP: {name} {list} {round}: the memos changed the run document"
        );
        let (on_cache, off_cache) = (with.join(CACHE_DIRECTORY), without.join(CACHE_DIRECTORY));
        assert_eq!(
            stores(&on_cache),
            stores(&off_cache),
            "STOP: {name} {list} {round}: the memos changed the outcome cache or the hints"
        );
        let report = |cache: &Path| {
            timeless(
                &serde_json::from_slice::<Value>(&fs::read(cache.join("report.json")).unwrap())
                    .unwrap(),
            )
        };
        assert_eq!(
            report(&on_cache),
            report(&off_cache),
            "{name} {list} {round}"
        );
        assert!(files(&off_cache, memo::MEMO_DIRECTORY).is_empty());
        let memos = files(&on_cache, memo::MEMO_DIRECTORY);
        let census = memos
            .keys()
            .filter(|path| path.starts_with("memo/census"))
            .count();
        assert_eq!(census, 1, "{name} {list} {round}: {:?}", memos.keys());
        // One record per mutation that resolves (an `invalid-mutation` has none).
        let resolving = on["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["status"] != "invalid-mutation")
            .count();
        assert_eq!(memos.len() - census, resolving, "{name} {list} {round}");
        eprintln!(
            "L14_MEMO {name} {list} {round} statuses={:?} from_cache={}",
            on["mutations"]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| format!("{}={}", row["id"], row["status"]))
                .collect::<Vec<_>>(),
            on["outcome_cache"]["mutations_from_cache"]
        );
    }
}

/// Deliverable 4: with and without memos, every document, outcome, hint and report is equal,
/// cold and warm, on calc (every status: invalid-mutation, killed, survived, equivalent, invalid)
/// and on the Markdown fixture (K views of a `.md` source); one test per fixture (test-gate TG-F,
/// formerly `memos_change_no_row_record_or_hint`), the second warm round in the heavy tier.
mod kink_tier {
    use super::*;

    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn memos_change_no_row_record_or_hint_on_calc() {
        compare("calc", "MUTATIONS-statuses.toml", &ROUNDS[..2]);
    }

    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn memos_change_no_row_record_or_hint_on_markdown() {
        compare("markdown", "MUTATIONS.toml", &ROUNDS[..2]);
    }

    /// Re-pin L1-4 fix 1 (review D1): a stored census that admits a specification the live census
    /// refuses (a natural record for a flagged specification, the one record that would drop the
    /// VI-T13 guard) is used by a warm run under exactly its key (the positive control), and `run
    /// --verify` refuses the specification with the live census and reports the record in the
    /// refused document's `mismatches`, writing nothing.
    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn a_stored_census_admitting_what_the_live_census_refuses_is_reported_by_verify() {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("kink-flow-memo-{}", std::process::id()))
            .join("t13tok");
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        fs::copy(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/t13tok.k"),
            dir.join("t13tok.k"),
        )
        .unwrap();
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nentry = \"t13tok.k\"\nmain_module = \"T13TOK\"\nsyntax_module = \
             \"T13TOK-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"start(1)\"\n",
        )
        .unwrap();
        fs::write(
            dir.join("MUTATIONS.toml"),
            "[[mutation]]\nid = \"range-seven\"\n  [[mutation.edit]]\n  rule = \"range\"\n  find = \
             \"done(7)\"\n  replace = \"done(8)\"\n",
        )
        .unwrap();
        let list = "MUTATIONS.toml";
        let cache = dir.join(CACHE_DIRECTORY);
        let store = Store::new(&cache);
        // Live, the census flags the specification (VI-T13), and the cold run records that census.
        let (cold, ok) = search(&dir, list, MemoUse::On, RunMode::Search);
        assert!(!ok);
        assert_eq!(cold["spec"]["outcome"], "refused", "{cold:#}");
        assert_eq!(cold["spec"]["stage"], "declaration-census");
        assert_eq!(cold["mismatches"], json!([]));
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let files = cold["spec"]["files"]
            .as_array()
            .unwrap()
            .iter()
            .map(|file| kink_corpus::SourceFile {
                name: file["name"].as_str().unwrap().to_owned(),
                sha256: kink_patch::Sha256Digest::parse(file["sha256"].as_str().unwrap()).unwrap(),
            })
            .collect::<Vec<_>>();
        let spec = spec_digest(&manifest, &files);
        let build = kink_campaign::kink_build().expect("the test binary is readable");
        let (key, path) = (
            memo::census_key(spec, build),
            memo::census_path(&cache, spec),
        );
        let live = memo::read_census(&path, &key).expect("the cold run wrote the census");
        assert_eq!(live.value()["verdict"], "flagged");
        // The lie: the same census, natural and without findings.
        let mut value = live.value();
        value["verdict"] = json!("natural");
        value["findings"] = json!([]);
        let lie = kink_native::DeclarationCensus::from_value(&value).expect("a census value");
        memo::write_census(&store, &path, &key, &lie);
        // The positive control: a warm run reads it and admits the specification.
        let (warm, _) = search(&dir, list, MemoUse::On, RunMode::Search);
        assert_eq!(
            warm["spec"]["outcome"], "admitted",
            "the census memo was not read: {warm:#}"
        );
        // --no-memo refuses, as live.
        let (off, _) = search(&dir, list, MemoUse::Off, RunMode::Search);
        assert_eq!(off["spec"]["outcome"], "refused");
        assert_eq!(off["mismatches"], json!([]));
        // --verify refuses with the live census and reports the record.
        let before = fs::read(&path).unwrap();
        let (verified, ok) = search(&dir, list, MemoUse::On, RunMode::Verify);
        assert!(!ok);
        assert_eq!(verified["spec"]["outcome"], "refused", "{verified:#}");
        assert_eq!(verified["spec"]["stage"], "declaration-census");
        assert_eq!(verified["spec"]["reason"], off["spec"]["reason"]);
        let mismatches = verified["mismatches"].as_array().unwrap();
        assert_eq!(mismatches.len(), 1, "{verified:#}");
        assert_eq!(mismatches[0]["mutation"], Value::Null);
        assert_eq!(mismatches[0]["program"], Value::Null);
        assert_eq!(mismatches[0]["cached"]["census"], lie.value());
        assert_eq!(mismatches[0]["live"]["census"], live.value());
        assert_eq!(fs::read(&path).unwrap(), before, "--verify wrote a memo");
        let stored: Value =
            serde_json::from_slice(&fs::read(cache.join("report.json")).unwrap()).unwrap();
        assert_eq!(stored["mismatches"], verified["mismatches"]);
    }

    /// Re-pin L1-4-tail (review L1-4-2 N1): a source file that changes after the admission read it
    /// and before resolution reads no resolution record (`memo::sources_unchanged`). Every record of
    /// the run is under the admitted digest, so its key still matches: only the guard keeps a memo
    /// row, made from the admitted bytes, from standing in for live resolution, which sees the new
    /// bytes. The change is made deterministically between the two: the first program's file is a
    /// named pipe, which the run first reads after the admission (`update_results` reads each
    /// program's text) and before any resolution, and the pipe serves the program only after
    /// `calc.k` changed. With memos the run gives the document a run without memos gives under the
    /// same change, the survivor's forged record (under exactly the admitted key) is not read, and
    /// the memo directory is unchanged.
    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn a_source_changed_after_admission_reads_no_record() {
        let with = fixture("calc", "changed-after-admission-on");
        let without = fixture("calc", "changed-after-admission-off");
        let (cold, _) = search(&with, LIST, MemoUse::On, RunMode::Search);
        let (cold_off, _) = search(&without, LIST, MemoUse::Off, RunMode::Search);
        assert_eq!(timeless(&cold), timeless(&cold_off));
        let cache = with.join(CACHE_DIRECTORY);
        let parts = key_parts(&with, LIST, SURVIVOR);
        let key = memo::resolution_key(parts.spec, parts.build, &parts.mutation);
        let path = memo::resolution_path(&cache, parts.spec, &parts.mutation);
        let lie = forged(&memo::read_facts(&path, &key).expect("the cold run wrote the facts"));
        memo::write_facts(&Store::new(&cache), &path, &key, &lie);
        // The positive control: unchanged, the forged record is read.
        let (warm, _) = search(&with, LIST, MemoUse::On, RunMode::Search);
        assert_eq!(
            row(&warm, SURVIVOR)["rules"][0]["after"],
            "rule [add]: I1 + I2 => FORGED",
            "the memo was not read"
        );
        search(&without, LIST, MemoUse::Off, RunMode::Search);
        let memos = files(&cache, memo::MEMO_DIRECTORY);

        let changed_run = |dir: &Path, memo: MemoUse| {
            let source = dir.join("calc.k");
            let change = move || {
                let mut text = fs::read_to_string(&source).unwrap();
                text.push_str("\n// changed after the admission\n");
                fs::write(&source, text).unwrap();
            };
            let ((document, _), served) =
                with_change_on_first_read(&dir.join("programs/add.calc"), change, || {
                    search(dir, LIST, memo, RunMode::Search)
                });
            assert!(served, "the run did not read the program");
            document
        };
        let on = changed_run(&with, MemoUse::On);
        let off = changed_run(&without, MemoUse::Off);
        // The admission read calc.k before the change, and resolution after it.
        assert_eq!(on["spec"]["files"], cold["spec"]["files"], "{on:#}");
        let survivor = row(&on, SURVIVOR);
        assert_eq!(
            survivor["status"], "invalid-mutation",
            "a record was read for a source changed after the admission: {survivor:#}"
        );
        assert_eq!(survivor["reason"], "source-changed", "{survivor:#}");
        assert_eq!(
            timeless(&on),
            timeless(&off),
            "STOP: a source changed after the admission: the memos changed the run document"
        );
        assert_eq!(
            files(&cache, memo::MEMO_DIRECTORY),
            memos,
            "a memo was written"
        );
    }

    /// The census memo is read under exactly its key: a forged flagged census refuses the
    /// specification there (the positive control), `--verify` admits it with the live census and
    /// reports the record, and the same record under another build or identity is not used.
    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn a_census_record_is_used_under_exactly_its_key() {
        let dir = fixture("calc", "census");
        let cache = dir.join(CACHE_DIRECTORY);
        let store = Store::new(&cache);
        let (cold, ok) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        assert!(ok, "{cold:#}");
        let parts = key_parts(&dir, LIST, SURVIVOR);
        // Re-pin L1-4-tail: the key, built here from every input, is the one `memo` builds.
        let identity = kink_campaign::kink_identity();
        let key = census_key_of(CENSUS_MEMO_VERSION, parts.build, &identity, parts.spec);
        assert_eq!(
            memo::census_key(parts.spec, parts.build),
            key,
            "the census key does not name each of its inputs"
        );
        let path = memo::census_path(&cache, parts.spec);
        let census = memo::read_census(&path, &key).expect("the cold run wrote the census");
        assert!(census.findings().is_empty());
        let mut value = census.value();
        value["verdict"] = json!("flagged");
        value["findings"] = json!([{
            "class": "U", "symbol": "Lblforged", "hook": "FORGED.hook",
            "declared": {"arguments": [], "result": "SortInt"},
            "expected": "reference declaration or verified inert hook",
            "source": null, "location": null,
        }]);
        let lie = kink_native::DeclarationCensus::from_value(&value).expect("a census value");
        memo::write_census(&store, &path, &key, &lie);
        let (refused, ok) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        assert!(!ok);
        assert_eq!(
            refused["spec"]["outcome"], "refused",
            "the census memo was not read"
        );
        assert_eq!(refused["spec"]["stage"], "declaration-census");
        let (off, off_ok) = search(&dir, LIST, MemoUse::Off, RunMode::Search);
        assert!(off_ok);
        assert_eq!(off["spec"]["outcome"], "admitted");
        let before = fs::read(&path).unwrap();
        let (verified, ok) = search(&dir, LIST, MemoUse::On, RunMode::Verify);
        assert!(!ok);
        assert_eq!(verified["spec"]["outcome"], "admitted");
        let mismatch = verified["mismatches"]
            .as_array()
            .unwrap()
            .iter()
            .find(|m| m["mutation"].is_null())
            .expect("a census mismatch");
        assert_eq!(mismatch["cached"]["census"], lie.value());
        assert_eq!(mismatch["live"]["census"], census.value());
        assert_eq!(fs::read(&path).unwrap(), before, "--verify wrote a memo");
        // Each stale key is built from the inputs with one input another (re-pin L1-4-tail), and
        // where `memo` takes that input as an argument, its key under the other input is that key.
        let other_build = kink_patch::sha256(b"another build");
        let other_spec = kink_patch::sha256(b"another specification");
        for (component, stale, from_memo) in [
            (
                "build",
                census_key_of(CENSUS_MEMO_VERSION, other_build, &identity, parts.spec),
                Some(memo::census_key(parts.spec, other_build)),
            ),
            (
                "kink",
                census_key_of(
                    CENSUS_MEMO_VERSION,
                    parts.build,
                    &another_identity(),
                    parts.spec,
                ),
                None,
            ),
            (
                "version",
                census_key_of(
                    "kink-flow/census-memo/v0",
                    parts.build,
                    &identity,
                    parts.spec,
                ),
                None,
            ),
            (
                "spec",
                census_key_of(CENSUS_MEMO_VERSION, parts.build, &identity, other_spec),
                Some(memo::census_key(other_spec, parts.build)),
            ),
        ] {
            assert_ne!(stale, key, "{component}");
            if let Some(from_memo) = from_memo {
                assert_eq!(from_memo, stale, "{component}");
            }
            memo::write_census(&store, &path, &stale, &lie);
            let (again, ok) = search(&dir, LIST, MemoUse::On, RunMode::Search);
            assert!(ok, "{component}: {again:#}");
            assert_eq!(again["spec"]["outcome"], "admitted", "{component}");
            assert_eq!(memo::read_census(&path, &key).as_ref(), Some(&census));
        }
    }

    /// A byte of a source file or of the mutation's text changes the key: no record of the old
    /// inputs is read, and the rows are the rows a run without memos gives on the new inputs.
    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn a_changed_source_byte_or_mutation_text_misses() {
        let dir = fixture("calc", "inputs");
        let cache = dir.join(CACHE_DIRECTORY);
        let store = Store::new(&cache);
        // The reference runs without memos through the same history (its hints and caches).
        let reference = fixture("calc", "inputs-reference");
        search(&dir, LIST, MemoUse::On, RunMode::Search);
        search(&reference, LIST, MemoUse::Off, RunMode::Search);
        let parts = key_parts(&dir, LIST, SURVIVOR);
        let key = memo::resolution_key(parts.spec, parts.build, &parts.mutation);
        let path = memo::resolution_path(&cache, parts.spec, &parts.mutation);
        let lie = forged(&memo::read_facts(&path, &key).unwrap());
        memo::write_facts(&store, &path, &key, &lie);

        // A source byte: a comment appended to calc.k changes the specification digest. The forged
        // record of the old digest is also copied where the new digest's record would be.
        let source = dir.join("calc.k");
        let mut text = fs::read_to_string(&source).unwrap();
        text.push_str("\n// one more byte\n");
        fs::write(&source, &text).unwrap();
        let edited = key_parts(&dir, LIST, SURVIVOR);
        assert_ne!(edited.spec, parts.spec);
        let moved = memo::resolution_path(&cache, edited.spec, &edited.mutation);
        memo::write_facts(&store, &moved, &key, &lie);
        fs::write(reference.join("calc.k"), &text).unwrap();
        let (on, _) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        let (off, _) = search(&reference, LIST, MemoUse::Off, RunMode::Search);
        assert_eq!(timeless(&on), timeless(&off), "a changed source byte");
        assert_ne!(
            row(&on, SURVIVOR)["rules"][0]["after"],
            lie.rules[0].after.as_deref().unwrap()
        );

        // The mutation's text: the replacement gains a space.
        let list = dir.join(LIST);
        let changed = fs::read_to_string(&list)
            .unwrap()
            .replace("replace = \"I2 +Int I1\"", "replace = \"I2 +Int  I1\"");
        fs::write(&list, &changed).unwrap();
        fs::write(reference.join(LIST), &changed).unwrap();
        let new = key_parts(&dir, LIST, SURVIVOR);
        let key_now = memo::resolution_key(new.spec, new.build, &new.mutation);
        let old_entry = memo::resolution_key(new.spec, new.build, &edited.mutation);
        assert_ne!(key_now, old_entry);
        let path_now = memo::resolution_path(&cache, new.spec, &new.mutation);
        memo::write_facts(&store, &path_now, &old_entry, &lie);
        let (on, _) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        let (off, _) = search(&reference, LIST, MemoUse::Off, RunMode::Search);
        assert_eq!(timeless(&on), timeless(&off), "a changed mutation text");
        assert!(memo::read_facts(&path_now, &key_now).is_some());

        // A source file that changed since the admission read it: no record is read at all.
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let (_, admitted) = admit_spec(&manifest);
        let (spec, _) = admitted.unwrap();
        assert!(memo::sources_unchanged(&dir, &spec.loaded));
        fs::write(&source, format!("{text} ")).unwrap();
        assert!(!memo::sources_unchanged(&dir, &spec.loaded));
    }

    /// The resolution memo is read under exactly its key, and only there; `--verify` reports a
    /// record that differs from the live resolution and writes nothing.
    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn a_resolution_record_is_used_under_exactly_its_key() {
        let dir = fixture("calc", "keys");
        let cache = dir.join(CACHE_DIRECTORY);
        let store = Store::new(&cache);
        let (cold, _) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        let live_rules = row(&cold, SURVIVOR)["rules"].clone();
        let parts = key_parts(&dir, LIST, SURVIVOR);
        // Re-pin L1-4-tail: the key, built here from every input, is the one `memo` builds, so the
        // positive control below reads the record under a key that names each of them.
        let identity = kink_campaign::kink_identity();
        let key = resolution_key_of(
            RESOLUTION_MEMO_VERSION,
            parts.build,
            &identity,
            parts.spec,
            &parts.mutation,
        );
        assert_eq!(
            memo::resolution_key(parts.spec, parts.build, &parts.mutation),
            key,
            "the resolution key does not name each of its inputs"
        );
        let path = memo::resolution_path(&cache, parts.spec, &parts.mutation);
        let facts = memo::read_facts(&path, &key).expect("the cold run wrote the facts");
        let lie = forged(&facts);

        // The positive control: under exactly the key, the forged facts are the row's.
        memo::write_facts(&store, &path, &key, &lie);
        let (warm, _) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        assert_eq!(row(&warm, SURVIVOR)["status"], "survived");
        assert_eq!(
            row(&warm, SURVIVOR)["rules"][0]["after"],
            "rule [add]: I1 + I2 => FORGED",
            "the memo was not read"
        );
        // --no-memo reads nothing.
        let (off, _) = search(&dir, LIST, MemoUse::Off, RunMode::Search);
        assert_eq!(row(&off, SURVIVOR)["rules"], live_rules);
        // --verify reads no record for a decision, reports the differing one and writes nothing.
        let before = fs::read(&path).unwrap();
        let (verified, ok) = search(&dir, LIST, MemoUse::On, RunMode::Verify);
        assert!(!ok);
        let checked = row(&verified, SURVIVOR);
        assert_eq!(checked["status"], "error", "{checked:#}");
        assert_eq!(checked["reason"], "resolution-mismatch");
        assert_eq!(checked["rules"], live_rules);
        let mismatch = verified["mismatches"]
            .as_array()
            .unwrap()
            .iter()
            .find(|m| m["mutation"] == SURVIVOR)
            .expect("a resolution mismatch");
        assert_eq!(mismatch["program"], Value::Null);
        assert_eq!(mismatch["cached"]["resolution"], lie.value());
        assert_eq!(mismatch["live"]["resolution"], facts.value());
        assert_eq!(fs::read(&path).unwrap(), before, "--verify wrote a memo");
        // No other row differs, and nothing else is reported.
        for other in verified["mutations"].as_array().unwrap() {
            if other["id"] != SURVIVOR {
                assert_ne!(other["reason"], "resolution-mismatch", "{other:#}");
            }
        }
        // Re-pin L1-4 fix 1 (review D5): `--verify --only` another mutation still resolves the
        // survivor and reports its differing record, which then has no row.
        let (selected, ok) = search_only(
            &dir,
            LIST,
            MemoUse::On,
            RunMode::Verify,
            &["add-becomes-sub"],
        );
        assert!(!ok, "a differing record was not reported: {selected:#}");
        assert_eq!(selected["mutations"].as_array().unwrap().len(), 1);
        let mismatch = selected["mismatches"]
            .as_array()
            .unwrap()
            .iter()
            .find(|m| m["mutation"] == SURVIVOR)
            .unwrap_or_else(|| panic!("no resolution mismatch under --only: {selected:#}"));
        assert_eq!(mismatch["cached"]["resolution"], lie.value());
        assert_eq!(mismatch["live"]["resolution"], facts.value());
        assert_eq!(
            fs::read(&path).unwrap(),
            before,
            "--verify --only wrote a memo"
        );

        // The same lie under a key that differs in one input is not used, and is rewritten. Each
        // stale key is built from the inputs, with that one input another (re-pin L1-4-tail: not by
        // editing a copy of the key, which would keep a member the key omits); where `memo` takes
        // the input as an argument, its key under the other input is that stale key.
        let other_build = kink_patch::sha256(b"another build of kink");
        let other_spec = kink_patch::sha256(b"another specification");
        let mut other_mutation = parts.mutation.clone();
        if let EditAction::Replace { replace, .. } = &mut other_mutation.edits[0].action {
            replace.push(' ');
        }
        let stale_keys = [
            (
                "build",
                resolution_key_of(
                    RESOLUTION_MEMO_VERSION,
                    other_build,
                    &identity,
                    parts.spec,
                    &parts.mutation,
                ),
                Some(memo::resolution_key(
                    parts.spec,
                    other_build,
                    &parts.mutation,
                )),
            ),
            (
                "kink",
                resolution_key_of(
                    RESOLUTION_MEMO_VERSION,
                    parts.build,
                    &another_identity(),
                    parts.spec,
                    &parts.mutation,
                ),
                None,
            ),
            (
                "version",
                resolution_key_of(
                    "kink-flow/resolution-memo/v0",
                    parts.build,
                    &identity,
                    parts.spec,
                    &parts.mutation,
                ),
                None,
            ),
            (
                "spec",
                resolution_key_of(
                    RESOLUTION_MEMO_VERSION,
                    parts.build,
                    &identity,
                    other_spec,
                    &parts.mutation,
                ),
                Some(memo::resolution_key(
                    other_spec,
                    parts.build,
                    &parts.mutation,
                )),
            ),
            (
                "mutation",
                resolution_key_of(
                    RESOLUTION_MEMO_VERSION,
                    parts.build,
                    &identity,
                    parts.spec,
                    &other_mutation,
                ),
                Some(memo::resolution_key(
                    parts.spec,
                    parts.build,
                    &other_mutation,
                )),
            ),
        ];
        for (component, stale, from_memo) in stale_keys {
            assert_ne!(stale, key, "{component}");
            if let Some(from_memo) = from_memo {
                assert_eq!(from_memo, stale, "{component}");
            }
            memo::write_facts(&store, &path, &stale, &lie);
            let (again, _) = search(&dir, LIST, MemoUse::On, RunMode::Search);
            assert_eq!(
                row(&again, SURVIVOR)["rules"],
                live_rules,
                "a record under another {component} was used"
            );
            assert_eq!(
                memo::read_facts(&path, &key).as_ref(),
                Some(&facts),
                "{component}: the live facts were not written back"
            );
            assert_eq!(memo::read_facts(&path, &stale), None);
        }
        // A record that does not carry its own digest is not used.
        memo::write_facts(&store, &path, &key, &lie);
        let mut record: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        record["value"]["rules"][0]["after"] = json!("rule [add]: I1 + I2 => OTHER");
        fs::write(&path, serde_json::to_vec(&record).unwrap()).unwrap();
        assert_eq!(memo::read_facts(&path, &key), None);
        let (again, _) = search(&dir, LIST, MemoUse::On, RunMode::Search);
        assert_eq!(row(&again, SURVIVOR)["rules"], live_rules);
    }

    /// Re-pin L1-4 fix 1 (review D2, end to end): mutations that differ from a killed base in one
    /// field each (an `invalid-mutation` for `file`, `rule`, `line` and `find`, a survivor for
    /// `replace`, the rule deleted for `delete`) never share a record. With memos and without, cold,
    /// warm and warm again, the documents, outcome cache and hints are equal, also after the base's
    /// record is copied to every other mutation's path. Had the key dropped a field, the warm run
    /// would give that field's mutation the base's facts, which tier 1 decides: `killed` for an
    /// `invalid-mutation` (review L1-4-1: dropping all fields but `replace` reported markdown's
    /// ghost-rule killed).
    // Portable only: tests the warm-path memos, off under Z3 by design as tier 1 is.
    #[cfg(not(feature = "z3"))]
    #[test]
    #[ignore = "kink"]
    fn mutations_differing_in_one_field_never_share_a_record() {
        let list = "MUTATIONS-fields.toml";
        let with = fixture("calc", "fields-on");
        let without = fixture("calc", "fields-off");
        for dir in [&with, &without] {
            fs::write(dir.join(list), field_list()).unwrap();
        }
        let cache = with.join(CACHE_DIRECTORY);
        for round in ["cold", "warm", "warm again"] {
            let (on, on_ok) = search(&with, list, MemoUse::On, RunMode::Search);
            let (off, off_ok) = search(&without, list, MemoUse::Off, RunMode::Search);
            assert_eq!(on_ok, off_ok, "{round}");
            assert_eq!(
                timeless(&on),
                timeless(&off),
                "STOP: {round}: two mutations that differ in one field shared a record"
            );
            assert_eq!(
                stores(&cache),
                stores(&without.join(CACHE_DIRECTORY)),
                "{round}"
            );
            let status = |id: &str| row(&off, id)["status"].clone();
            assert_eq!(status("base"), "killed", "{off:#}");
            for id in ["file", "rule", "line", "find"] {
                assert_eq!(status(id), "invalid-mutation", "{id}: {off:#}");
            }
            assert_eq!(status("replace"), "survived", "{off:#}");
            assert_ne!(status("delete"), "invalid-mutation", "{off:#}");
            // The base's record, copied where each other mutation's record is found: its key names
            // the base, so it is not used for the other.
            let parts = key_parts(&with, list, "base");
            let base = memo::resolution_path(&cache, parts.spec, &parts.mutation);
            assert!(
                memo::read_facts(
                    &base,
                    &memo::resolution_key(parts.spec, parts.build, &parts.mutation)
                )
                .is_some()
            );
            for (id, _) in &field_variants()[1..] {
                let other = key_parts(&with, list, id);
                let path = memo::resolution_path(&cache, other.spec, &other.mutation);
                assert_ne!(path, base, "{id}");
                fs::copy(&base, &path).unwrap();
            }
        }
    }
}

mod heavy {
    use super::*;

    #[test]
    #[ignore = "heavy"]
    fn memos_change_no_row_record_or_hint_on_calc_in_three_rounds() {
        compare("calc", "MUTATIONS-statuses.toml", &ROUNDS);
    }

    #[test]
    #[ignore = "heavy"]
    fn memos_change_no_row_record_or_hint_on_markdown_in_three_rounds() {
        compare("markdown", "MUTATIONS.toml", &ROUNDS);
    }
}

/// A forged record of `add-commutes` (survived, so its row shows its rules): the edited rule's
/// text is a lie.
fn forged(facts: &Facts) -> Facts {
    let mut lie = facts.clone();
    lie.rules[0].after = Some("rule [add]: I1 + I2 => FORGED".to_owned());
    lie
}

const LIST: &str = "MUTATIONS-statuses.toml";
const SURVIVOR: &str = "add-commutes";

/// One mutation entry of a mutation list, from its fields as TOML values (`None`: absent).
fn entry(id: &str, fields: &[(&str, Option<String>)]) -> String {
    let mut text = format!("[[mutation]]\nid = \"{id}\"\n  [[mutation.edit]]\n");
    for (name, value) in fields {
        if let Some(value) = value {
            text.push_str(&format!("  {name} = {value}\n"));
        }
    }
    text
}

fn quoted(text: &str) -> Option<String> {
    Some(serde_json::to_string(text).unwrap())
}

/// The base mutation of the field tests (killed on calc: 1 + 2 is not -1) with every field of an
/// edit given, and for each field the mutation that differs from it in that field alone (for
/// `delete`, the action: the rule deleted instead of edited).
/// An edit's fields as TOML values (`None`: absent).
type Fields = Vec<(&'static str, Option<String>)>;

fn field_variants() -> Vec<(&'static str, Fields)> {
    let base = || {
        vec![
            ("file", quoted("calc.k")),
            ("rule", quoted("add")),
            ("line", Some("21".to_owned())),
            ("find", quoted("I1 +Int I2")),
            ("replace", quoted("I1 -Int I2")),
            ("delete", None),
        ]
    };
    let with = |field: &str, value: Option<String>| {
        base()
            .into_iter()
            .map(|(name, old)| (name, if name == field { value.clone() } else { old }))
            .collect::<Vec<_>>()
    };
    let deleted = base()
        .into_iter()
        .map(|(name, old)| match name {
            "find" | "replace" => (name, None),
            "delete" => (name, Some("true".to_owned())),
            _ => (name, old),
        })
        .collect();
    vec![
        ("base", base()),
        ("file", with("file", quoted("other.k"))),
        ("rule", with("rule", quoted("mul"))),
        ("line", with("line", Some("22".to_owned()))),
        ("find", with("find", quoted("+Int I2"))),
        ("replace", with("replace", quoted("I2 +Int I1"))),
        ("delete", deleted),
    ]
}

fn field_list() -> String {
    field_variants()
        .iter()
        .map(|(id, fields)| entry(id, fields))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Re-pin L1-4 fix 1 (review D2): the resolution key pins every field of a mutation's edits. For
/// each field (`file`, `rule`, `line`, `find`, `replace`, and `delete`, the action), the key and
/// the record path of a mutation that differs from the base in that field alone differ from the
/// base's; and every key's `mutation` entry, written back as a mutation list, decodes to exactly
/// the mutation's edits, so the key is injective on edits (a field dropped from the key, `delete`
/// included, fails here).
#[test]
fn the_resolution_key_pins_every_field_of_the_edits() {
    let list = MutationList::decode(&field_list()).unwrap();
    let spec = kink_patch::sha256(b"a specification");
    let build = kink_patch::sha256(b"a build");
    let cache = Path::new("/nonexistent");
    let base = &list.mutations[0];
    assert_eq!(base.id, "base");
    let base_key = memo::resolution_key(spec, build, base);
    for mutation in &list.mutations[1..] {
        assert_ne!(mutation.edits, base.edits, "{}", mutation.id);
        assert_ne!(
            memo::resolution_key(spec, build, mutation),
            base_key,
            "the key does not name {}",
            mutation.id
        );
        assert_ne!(
            memo::resolution_path(cache, spec, mutation),
            memo::resolution_path(cache, spec, base),
            "the record path does not name {}",
            mutation.id
        );
    }
    for mutation in &list.mutations {
        let key = memo::resolution_key(spec, build, mutation);
        let edits = key["mutation"].as_array().unwrap();
        let mut text = format!("[[mutation]]\nid = \"{}\"\n", mutation.id);
        for edit in edits {
            let fields = edit.as_object().unwrap();
            assert_eq!(
                fields.keys().map(String::as_str).collect::<Vec<_>>(),
                ["delete", "file", "find", "line", "replace", "rule"],
                "{}",
                mutation.id
            );
            text.push_str("  [[mutation.edit]]\n");
            for (name, value) in fields {
                match value {
                    Value::Null | Value::Bool(false) => {}
                    value => text.push_str(&format!("  {name} = {value}\n")),
                }
            }
        }
        let decoded = MutationList::decode(&text)
            .unwrap_or_else(|e| panic!("{}: the key's edits do not decode: {e:?}", mutation.id));
        assert_eq!(
            decoded.mutations[0].edits, mutation.edits,
            "{}: the key does not determine the edits",
            mutation.id
        );
    }
}

/// Re-pin L1-4-tail (review L1-4-2 N1): both memo keys name every input, each as a member built
/// here (`resolution_key_of`, `census_key_of`): the memo version, kink's build, kink's semantics
/// identity (`kink_campaign::kink_identity`, a constant of this build, which no stale key made
/// from `memo`'s functions can vary), the specification digest and, for a resolution, every field
/// of the mutation's edits. A key that omits any of them, or adds one, fails here.
#[test]
fn the_memo_keys_name_every_input() {
    let list = MutationList::decode(&field_list()).unwrap();
    let spec = kink_patch::sha256(b"a specification");
    let build = kink_patch::sha256(b"a build");
    let identity = kink_campaign::kink_identity();
    for mutation in &list.mutations {
        assert_eq!(
            memo::resolution_key(spec, build, mutation),
            resolution_key_of(RESOLUTION_MEMO_VERSION, build, &identity, spec, mutation),
            "{}",
            mutation.id
        );
    }
    assert_eq!(
        memo::census_key(spec, build),
        census_key_of(CENSUS_MEMO_VERSION, build, &identity, spec)
    );
}

/// Serves the bytes of the fixture file `file` once, through a named pipe at its path, while
/// `run` runs: when the pipe is first opened, `change` runs, then a regular file with the same
/// bytes replaces the pipe (every later open reads it), and only then are the bytes served. So
/// `change` happens after everything `run` does before it first opens `file`, and before
/// everything it does after reading it. Returns `run`'s result and whether the pipe was read.
fn with_change_on_first_read<T>(
    file: &Path,
    change: impl FnOnce() + Send + 'static,
    run: impl FnOnce() -> T,
) -> (T, bool) {
    let bytes = fs::read(file).unwrap();
    let regular = file.with_extension("regular");
    fs::write(&regular, &bytes).unwrap();
    fs::remove_file(file).unwrap();
    let made = Command::new("mkfifo").arg(file).status().unwrap();
    assert!(made.success(), "mkfifo {}", file.display());
    let served = Arc::new(AtomicBool::new(false));
    let writer = {
        let (file, served) = (file.to_owned(), served.clone());
        std::thread::spawn(move || {
            // Opening a pipe for writing blocks until a reader opens it.
            let Ok(mut pipe) = fs::OpenOptions::new().write(true).open(&file) else {
                return;
            };
            served.store(true, Ordering::SeqCst);
            change();
            fs::rename(&regular, &file).unwrap();
            let _ = pipe.write_all(&bytes);
        })
    };
    let result = run();
    // A reader of the pipe reads to its end, which comes only when the writer is done, so the
    // pipe was never opened when nothing was served: release the writer.
    let served = served.load(Ordering::SeqCst);
    if !served && !writer.is_finished() {
        drop(fs::File::open(file).unwrap());
    }
    writer.join().unwrap();
    (result, served)
}
