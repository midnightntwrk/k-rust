//! Re-pin R0b (`draft/tasks/repin-501f18b9`): the exclusions of kink-native's `exclusion` module
//! on real k-rust runs and loads, the implementation-chosen hook list pinned against k-rust's
//! source, and the testdata definitions each definition-level exclusion affects.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, parser::parse_definition, parser::parse_pattern};
use k_rust_backend::nesting::with_simplification_stack_budget;
use kink_native::exclusion::{
    BUILTIN_OPEN_HOOKS, DOMAINS_OPEN_HOOKS, DefinitionExclusions, Exclusion,
    IMPLEMENTATION_CHOSEN_HOOKS, K_RUST_IMPLEMENTATION_CHOSEN_HOOKS, RUN_LIST_HOOKS,
    SHORT_CIRCUIT_HOOKS, UNDOCUMENTED_EVALUATED_HOOKS, census_hook,
    state_references_implementation_chosen,
};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_native::{NativeValidator, ValidatedDefinition};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The R0b fixture `testdata/k/r0b/<name>.k`, compiled, and its encoded main module (the
/// upper-cased name).
fn r0b(name: &str) -> (ValidatedDefinition, String) {
    fixture("r0b", name)
}

/// The fixture `testdata/k/<dir>/<name>.k`, compiled, and its encoded main module (the
/// upper-cased name).
fn fixture(dir: &str, name: &str) -> (ValidatedDefinition, String) {
    let module = name.to_ascii_uppercase();
    let loaded = support::load_path(
        &Path::new(support::DIR).join(format!("{dir}/{name}.k")),
        &module,
    );
    let side = NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    (side, k_rust::kast::identifier::encode(&module))
}

fn budget() -> ExecutionBudget {
    ExecutionBudget {
        time: Duration::from_secs(60),
        max_simplification_iterations: 10_000,
        max_depth: Some(100),
        max_breadth: None,
    }
}

fn backend(side: &ValidatedDefinition, module: &str) -> Backend {
    Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .unwrap()
}

fn run(side: &ValidatedDefinition, module: &str, program: Pattern) -> AdaptedExecution {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(
            &mut backend(side, module),
            &support::initial_state(program, "SortProg"),
            budget(),
        )
        .unwrap()
}

/// Every string literal naming a hook (`"NAMESPACE.name"`) written before a `=>` in `text`.
fn arm_hooks(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|line| line.contains("=>"))
        .flat_map(|line| {
            let head = &line[..line.find("=>").unwrap()];
            head.split('"')
                .skip(1)
                .step_by(2)
                .filter(|literal| literal.contains('.'))
                .map(str::to_owned)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// The text of the function `name` in `source`, from its signature to its closing brace at the
/// signature's indentation.
fn function<'s>(source: &'s str, name: &str) -> &'s str {
    let start = source
        .find(&format!("fn {name}("))
        .unwrap_or_else(|| panic!("k-rust has no fn {name}"));
    let line_start = source[..start].rfind('\n').map_or(0, |at| at + 1);
    let indent = source[line_start..start]
        .chars()
        .take_while(|c| *c == ' ')
        .count();
    let close = format!("\n{}}}\n", " ".repeat(indent));
    let end = source[start..].find(&close).expect("the function ends") + start;
    &source[start..end]
}

/// The k-rust-backend source directory the workspace builds against (its path dependency in
/// k-rust's root manifest, since kink is a part of k-rust's workspace: merge packet M-1).
fn k_rust_backend() -> PathBuf {
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root().join("../Cargo.toml")).unwrap()).unwrap();
    root().join("..").join(
        manifest["workspace"]["dependencies"]["k-rust-backend"]["path"]
            .as_str()
            .expect("k-rust-backend is a path dependency"),
    )
}

/// `K_RUST_IMPLEMENTATION_CHOSEN_HOOKS` is exactly the set of hooks for which k-rust's
/// classifier `chosen_value` (k-rust-backend `builtin.rs`) can return `Some`, read from the
/// k-rust source the workspace builds against: its match arms, the hooks of the binary Float
/// operations `float::mixed_destination` accepts (`BinaryOperation::of`), the one hook
/// `float::nan_sign` reads, and the two `float::signed_zeros` reads. The arms' other helpers
/// (`lists_several_items`, `writes_a_letter_digit`, `substitutes_under_a_binder`, `read_string`)
/// only narrow when an arm's hook fires, so they do not change the set. `IMPLEMENTATION_CHOSEN_HOOKS`
/// is that list and the kink-side `DOMAINS_OPEN_HOOKS`, `BUILTIN_OPEN_HOOKS` and
/// `UNDOCUMENTED_EVALUATED_HOOKS`, each once. A change of any of them in k-rust fails this test,
/// so a re-pin re-derives the list.
///
/// Re-pin R0c deliverable 5 (R0b review 1 minor): reading arms and the helper calls misses a
/// further fallthrough helper or a widened helper condition, so the source text of the
/// functions is pinned by digest as well.
///
/// Re-pin L-1 (`draft/tasks/repin-58720d2e`, k-rust 8f8ad57c5): KINK-17/2 (k-rust 1691bf61c,
/// review 25fa4ccc9, merge 978d30070) replaced `implementation_chosen_in` with `chosen_value`,
/// which adds the arms `STRING.base2string`, `SUBSTITUTION.substOne` and `IO.read` and the
/// fallthrough `float::signed_zeros` (`FLOAT.min`, `FLOAT.max`); KINK-17/1 (375710b23, merge
/// 3a196ed14) gave it its text at the pin (the `ChosenValue::new` constructor), with the same
/// arms. So the reading moved to `chosen_value` and `signed_zeros`, the classifier's digest and
/// the new helper's are pinned, and the three new arms' hooks moved from the kink-side lists to
/// `K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`. The census (`IMPLEMENTATION_CHOSEN_HOOKS`) is the same
/// set of 88 hooks as at 501f18b9: none left it and none joined it, so no status moves. The
/// three other helpers' texts are unchanged since 501f18b9.
#[test]
fn implementation_chosen_hooks_are_k_rusts() {
    let backend = k_rust_backend();
    let builtin = std::fs::read_to_string(backend.join("src/builtin.rs")).unwrap();
    let float = std::fs::read_to_string(backend.join("src/builtin/float.rs")).unwrap();
    let chosen = function(&builtin, "chosen_value");
    let mixed = function(&float, "mixed_destination");
    let of = function(
        &float[float
            .find("impl BinaryOperation {")
            .expect("BinaryOperation")..],
        "of",
    );
    let nan = function(&float, "nan_sign");
    let zeros = function(&float, "signed_zeros");
    // The exact texts at k-rust 8f8ad57c5; a changed text needs the hook list re-derived from it.
    let digests = [
        ("chosen_value", chosen),
        ("float::mixed_destination", mixed),
        ("BinaryOperation::of", of),
        ("float::nan_sign", nan),
        ("float::signed_zeros", zeros),
    ]
    .map(|(name, text)| (name, kink_patch::sha256(text.as_bytes()).to_string()));
    assert_eq!(
        digests,
        [
            (
                "chosen_value",
                "a2f71c474f7546ada2a8d73480b9022cca1ab8ea8e16fffc3dbd71847ccebf6e".to_owned()
            ),
            (
                "float::mixed_destination",
                "c219eec25b1ad8899f7af425aed682f2edcb72010065a62f60a019324354d623".to_owned()
            ),
            (
                "BinaryOperation::of",
                "7d79eac8ebb73ef293b15f4a731b339f576b74f29b3b93de85080b52d0b20eca".to_owned()
            ),
            (
                "float::nan_sign",
                "c17041cfd7ea611ad2def7d98277f9204f00e410c066beb4ac6d7bc93c2f285a".to_owned()
            ),
            (
                "float::signed_zeros",
                "4f3a6a28b4aa2a95fb9ef1d2c1b87a638bec25f8f459507ba5d48191a90566ff".to_owned()
            ),
        ]
    );
    // The fallthrough arms are exactly the three Float helpers.
    assert!(
        chosen.contains("_ if float::mixed_destination(hook, arguments).is_some() =>")
            && chosen.contains("_ if float::nan_sign(hook, arguments).is_some() =>")
            && chosen.contains("float::signed_zeros(hook, arguments),"),
        "{chosen}"
    );
    let mut hooks = arm_hooks(chosen);
    assert_eq!(hooks.len(), 8, "{chosen}");
    assert!(mixed.contains("BinaryOperation::of(hook)?"), "{mixed}");
    let operations = arm_hooks(of);
    assert_eq!(operations.len(), 6, "{operations:?}");
    hooks.extend(operations);
    assert!(nan.contains(r#"if hook != "FLOAT.sign" {"#), "{nan}");
    hooks.insert("FLOAT.sign".to_owned());
    assert!(
        zeros.contains(r#"if !matches!(hook, "FLOAT.min" | "FLOAT.max") {"#),
        "{zeros}"
    );
    hooks.extend(["FLOAT.min".to_owned(), "FLOAT.max".to_owned()]);
    let k_rust = K_RUST_IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .map(|hook| (*hook).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(hooks, k_rust);
    assert_eq!(hooks.len(), K_RUST_IMPLEMENTATION_CHOSEN_HOOKS.len());
    let all = K_RUST_IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .copied()
        .chain(DOMAINS_OPEN_HOOKS.iter().map(|(hook, _, _)| *hook))
        .chain(BUILTIN_OPEN_HOOKS.iter().map(|(_, hook, _, _)| *hook))
        .chain(UNDOCUMENTED_EVALUATED_HOOKS.iter().copied())
        .collect::<Vec<_>>();
    assert_eq!(IMPLEMENTATION_CHOSEN_HOOKS, all.as_slice());
    assert_eq!(
        all.iter().collect::<BTreeSet<_>>().len(),
        all.len(),
        "each hook once"
    );
    // Re-pin L-1: the census is a superset of the one judged at 501f18b9 (a hook that left it
    // would let a definition that reads it be compared); here it is the same set.
    let census = IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    assert!(census.is_superset(&CENSUS_AT_501F18B9.into_iter().collect()));
    assert_eq!(census.len(), CENSUS_AT_501F18B9.len());
}

/// `IMPLEMENTATION_CHOSEN_HOOKS` at k-rust 501f18b9 (K-in-K2 main 71ab7d0), in its order then.
const CENSUS_AT_501F18B9: [&str; 88] = [
    "MAP.keys_list",
    "MAP.values",
    "SET.set2list",
    "MAP.choice",
    "SET.choice",
    "FLOAT.add",
    "FLOAT.sub",
    "FLOAT.mul",
    "FLOAT.div",
    "FLOAT.min",
    "FLOAT.max",
    "FLOAT.sign",
    "BYTES.string2bytes",
    "BYTES.bytes2string",
    "STRING.base2string",
    "STRING.float2string",
    "STRING.floatFormat",
    "STRING.category",
    "STRING.directionality",
    "STRING.uuid",
    "INT.rand",
    "INT.srand",
    "RANGEMAP.choice",
    "RANGEMAP.keys_list",
    "RANGEMAP.values",
    "KREFLECTION.configuration",
    "KREFLECTION.fresh",
    "KREFLECTION.getenv",
    "KREFLECTION.kompiledDir",
    "KREFLECTION.argv",
    "KREFLECTION.printKORE",
    "IO.open",
    "IO.tell",
    "IO.seek",
    "IO.seekEnd",
    "IO.getc",
    "IO.read",
    "IO.putc",
    "IO.write",
    "IO.close",
    "IO.lock",
    "IO.unlock",
    "IO.accept",
    "IO.shutdownWrite",
    "IO.time",
    "IO.system",
    "IO.mkstemp",
    "IO.remove",
    "SUBSTITUTION.substOne",
    "SUBSTITUTION.substMany",
    "UNIFICATION.renameVariables",
    "UNIFICATION.variables",
    "UNIFICATION.metaVariables",
    "UNIFICATION.variablesMap",
    "UNIFICATION.rename",
    "UNIFICATION.freezeVariables",
    "UNIFICATION.unifiable",
    "JSON.json2string",
    "JSON.string2json",
    "TIMER.timerStart",
    "TIMER.timerStop",
    "FFI.call",
    "FFI.call_variadic",
    "FFI.address",
    "FFI.alloc",
    "FFI.bytes_address",
    "FFI.read",
    "FFI.write",
    "HASH.keccak256",
    "HASH.ripemd160",
    "HASH.sha256",
    "HASH.sha3_256",
    "KRYPTO.bn128add",
    "KRYPTO.bn128ate",
    "KRYPTO.bn128g2valid",
    "KRYPTO.bn128mul",
    "KRYPTO.bn128valid",
    "KRYPTO.ecdsaPubKey",
    "KRYPTO.ecdsaRecover",
    "KRYPTO.keccak256",
    "KRYPTO.keccak256raw",
    "KRYPTO.ripemd160",
    "KRYPTO.ripemd160raw",
    "KRYPTO.sha256",
    "KRYPTO.sha256raw",
    "KRYPTO.sha3256",
    "KRYPTO.sha512_256raw",
    "SECP256K1.ecdsaRecover",
];

/// Re-pin R0c deliverable 2 (R0b review 1 major 2): every kink-side census hook is one whose
/// value `k-rust/builtin/domains.md` leaves to the backend, the implementation or the
/// environment. For each, the cited lines of domains.md at the pinned k-rust say so (the phrase
/// is in them), and domains.md declares the hook. The file's digest is pinned: a re-pin that
/// changes the prelude text sweeps it again (README "What a kill trusts"; handoff R0c lists each
/// hook with its lines).
///
/// Re-pin R1-PINS (kink27): k-rust 0da031036 is the only change to domains.md since the last
/// sweep. It adds two definedness rules to `INT-SYMBOLIC-KORE` (lines 1395 and 1398): `divInt`
/// is defined where its divisor is nonzero and `bitRangeInt` where its offset and length are
/// nonnegative, each together with its operands. Both state a domain the file already gives
/// (divInt's "Division by zero is `#False`", and `bitRangeInt`'s defining equation through
/// `>>Int` and `<<Int`, whose negative amounts are `#False`), declare no hook and change no hook's
/// text, so no value becomes open or fixed: the open hooks are the same, and each citation after
/// line 1394 moved by two lines.
#[test]
fn domains_md_leaves_these_hook_values_open() {
    let path = k_rust_backend().join("../k-rust/builtin/domains.md");
    let text = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        kink_patch::sha256(text.as_bytes()).to_string(),
        "574450e9c15431156336b7851f0e5b8b0944dc49db2b8425cbb919bb141d337b",
        "domains.md changed: sweep it again for hook values it leaves open"
    );
    let lines = text.lines().collect::<Vec<_>>();
    for (hook, range, phrase) in DOMAINS_OPEN_HOOKS {
        let (first, last) = range.split_once('-').unwrap();
        let (first, last) = (
            first.parse::<usize>().unwrap(),
            last.parse::<usize>().unwrap(),
        );
        let cited = lines[first - 1..last].join(" ");
        assert!(
            cited.contains(phrase),
            "{hook}: domains.md:{range} does not say {phrase:?}"
        );
        assert!(
            text.contains(&format!("hook({hook})")) || text.contains(&format!("hook({hook}),")),
            "{hook} is not a domains.md hook"
        );
    }
    // Each kink-side hook, once, and none of k-rust's own.
    let kink = DOMAINS_OPEN_HOOKS
        .iter()
        .map(|(hook, _, _)| *hook)
        .collect::<BTreeSet<_>>();
    assert_eq!(kink.len(), DOMAINS_OPEN_HOOKS.len());
    assert!(
        kink.iter()
            .all(|hook| !K_RUST_IMPLEMENTATION_CHOSEN_HOOKS.contains(hook))
    );
    // Deliverable 8 rests on `encodeBytes` with a named encoding: domains.md names its
    // encodings (line 2014), so it is not on the list.
    assert!(lines[2013].contains("using `UTF-8`"), "{}", lines[2013]);
    assert!(!IMPLEMENTATION_CHOSEN_HOOKS.contains(&"BYTES.encodeBytes"));
}

/// The builtin files k-rust 501f18b9 ships (`k-rust/builtin`), each with its digest: a re-pin
/// that adds, removes or changes one sweeps it again for hook values it leaves open.
const BUILTIN_FILES: [(&str, &str); 9] = [
    (
        "domains.md",
        "574450e9c15431156336b7851f0e5b8b0944dc49db2b8425cbb919bb141d337b",
    ),
    (
        "ffi.md",
        "9715ca4b6424dc2d2c7145b356dd78138350d8ac7b7d42bd735b909582efa6aa",
    ),
    (
        "json.md",
        "f167dae52f2fb2cc0f87631b93b0bb5425f5f8adeb61d666126ddae25e6d12fa",
    ),
    (
        "kast.md",
        "6e62ad3f96785ed24b6db2ce34ff201367493f01c285a34eec98da1f3cbd6b6f",
    ),
    (
        "prelude.md",
        "60abd2e7ee255b202dd95f50f760ab09b71a78547454d99a8a3d0fc33020172c",
    ),
    (
        "rat.md",
        "685711fa32c16b27f4e4e9da20b2a9ea0d2a63a7dba566eba711e35dde31fd03",
    ),
    (
        "substitution.md",
        "c7e3fe10066a8b0cb8dcfd60c2b8e9bda78914b1e8d488ceeeacd16f231e293e",
    ),
    (
        "timer.md",
        "4b718e4ac1929f5bf9ccdb1f27a7998870c5105aeaeb300358a8a1fc601605e4",
    ),
    (
        "unification.k",
        "4a6fc7b72406d14a26c584366e8395b93071f6377ca8ca44aeba3edea5da8dbd",
    ),
];

/// Every hook `hook(NAME)` a builtin file's text declares, with whether that declaration is
/// `impure`.
fn declared_hooks(text: &str) -> Vec<(String, bool)> {
    text.lines()
        .filter_map(|line| {
            let start = line.find("hook(")? + "hook(".len();
            let end = line[start..].find(')')? + start;
            Some((line[start..end].to_owned(), line.contains("impure")))
        })
        .collect()
}

/// Re-pin R0c-fix-1 deliverable 2 (R0c review 1 major 3): decision 1's sweep covers every builtin
/// file k-rust ships, not only domains.md. The file set and each file's digest are pinned. Each
/// `BUILTIN_OPEN_HOOKS` entry's cited lines say what it cites, and its file declares the hook.
/// Every hook the non-domains files declare is on the census list or named here as fixed by its
/// file; every hook any builtin file declares `impure` is on the list or named here, with the
/// reason its value is fixed (domains.md's sweep, pinned by
/// `domains_md_leaves_these_hook_values_open`, covers the rest of domains.md).
#[test]
fn builtin_files_leave_these_hook_values_open() {
    let dir = k_rust_backend().join("../k-rust/builtin");
    let mut names = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        BUILTIN_FILES.map(|(name, _)| name.to_owned()),
        "k-rust's builtin files changed: sweep them again"
    );
    let texts = BUILTIN_FILES
        .iter()
        .map(|(name, digest)| {
            let text = std::fs::read_to_string(dir.join(name)).unwrap();
            assert_eq!(
                kink_patch::sha256(text.as_bytes()).to_string(),
                *digest,
                "{name} changed: sweep it again for hook values it leaves open"
            );
            (*name, text)
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    for (file, hook, range, phrase) in BUILTIN_OPEN_HOOKS {
        let text = &texts[file];
        let lines = text.lines().collect::<Vec<_>>();
        let (first, last) = range.split_once('-').unwrap();
        let (first, last) = (
            first.parse::<usize>().unwrap(),
            last.parse::<usize>().unwrap(),
        );
        assert!(
            lines[first - 1..last].join(" ").contains(phrase),
            "{hook}: {file}:{range} does not say {phrase:?}"
        );
        assert!(
            declared_hooks(text)
                .iter()
                .any(|(declared, _)| declared == hook),
            "{hook} is not a {file} hook"
        );
        assert!(IMPLEMENTATION_CHOSEN_HOOKS.contains(hook));
    }
    // Hooks whose value their file fixes, each with the reason.
    let fixed = [
        ("FFI.free", "ffi.md:178 \"The function returns `.K`\""),
        (
            "BUFFER.empty",
            "domains.md: the empty StringBuffer (impure for mutability)",
        ),
        ("IO.log", "domains.md:2662-2692: returns `.K` (returnsUnit)"),
        (
            "IO.logString",
            "domains.md:2662-2692: returns `.K` (returnsUnit)",
        ),
        (
            "IO.traceTerm",
            "domains.md:2662-2692: returns `.K` (returnsUnit)",
        ),
        ("K.K", "kast.md: a sort hook, no value"),
        ("K.KItem", "kast.md: a sort hook, no value"),
        ("KVAR.KVar", "substitution.md: a sort hook, no value"),
        (
            "STRING.string2token",
            "substitution.md:51 String2KVar: the KVar token spelled by the string",
        ),
    ];
    let listed = |hook: &str| {
        IMPLEMENTATION_CHOSEN_HOOKS.contains(&hook) || fixed.iter().any(|(h, _)| *h == hook)
    };
    for (name, text) in &texts {
        for (hook, impure) in declared_hooks(text) {
            if *name == "domains.md" {
                assert!(
                    !impure || listed(&hook),
                    "domains.md: impure {hook} unswept"
                );
            } else if *name == "rat.md" {
                // Rational arithmetic in the canonical form rat.md states; Rat2Float rounds as
                // IEEE 754, as the other Float hooks.
                assert!(
                    hook.starts_with("RAT.") || hook == "FLOAT.rat2float",
                    "rat.md: {hook}"
                );
                assert!(!impure, "rat.md: impure {hook}");
            } else {
                assert!(listed(&hook), "{name}: {hook} unswept");
            }
        }
    }
    // The fresh-value judgement rests on kast.md's wording: `!X` is only distinct.
    assert!(
        texts["kast.md"]
            .contains("refer to a unique value of the specified sort which is distinct from any")
    );
}

/// Every hook k-rust 501f18b9's builtin dispatch evaluates: each hook literal written before a
/// match arm's `=>` or `|` in k-rust-backend `src/builtin.rs` and `src/builtin/**/*.rs`.
const K_RUST_EVALUATED_HOOKS: [&str; 196] = [
    "BOOL.and",
    "BOOL.andThen",
    "BOOL.eq",
    "BOOL.implies",
    "BOOL.ne",
    "BOOL.not",
    "BOOL.or",
    "BOOL.orElse",
    "BOOL.xor",
    "BYTES.bytes2int",
    "BYTES.bytes2string",
    "BYTES.concat",
    "BYTES.decodeBytes",
    "BYTES.empty",
    "BYTES.encodeBytes",
    "BYTES.get",
    "BYTES.int2bytes",
    "BYTES.length",
    "BYTES.padLeft",
    "BYTES.padRight",
    "BYTES.replaceAt",
    "BYTES.reverse",
    "BYTES.string2bytes",
    "BYTES.substr",
    "BYTES.update",
    "FLOAT.abs",
    "FLOAT.add",
    "FLOAT.ceil",
    "FLOAT.div",
    "FLOAT.eq",
    "FLOAT.exponentBits",
    "FLOAT.float2int",
    "FLOAT.floor",
    "FLOAT.ge",
    "FLOAT.gt",
    "FLOAT.int2float",
    "FLOAT.isNaN",
    "FLOAT.le",
    "FLOAT.lt",
    "FLOAT.max",
    "FLOAT.maxValue",
    "FLOAT.min",
    "FLOAT.mul",
    "FLOAT.neg",
    "FLOAT.precision",
    "FLOAT.root",
    "FLOAT.round",
    "FLOAT.sign",
    "FLOAT.sub",
    "FLOAT.trunc",
    "HASH.keccak256",
    "HASH.ripemd160",
    "HASH.sha256",
    "HASH.sha3_256",
    "INT.abs",
    "INT.add",
    "INT.and",
    "INT.bitRange",
    "INT.ediv",
    "INT.emod",
    "INT.eq",
    "INT.ge",
    "INT.gt",
    "INT.le",
    "INT.log2",
    "INT.lt",
    "INT.max",
    "INT.min",
    "INT.mul",
    "INT.ne",
    "INT.not",
    "INT.or",
    "INT.pow",
    "INT.powmod",
    "INT.shl",
    "INT.shr",
    "INT.signExtendBitRange",
    "INT.sub",
    "INT.tdiv",
    "INT.tmod",
    "INT.xor",
    "IO.getc",
    "IO.logString",
    "IO.putc",
    "IO.read",
    "IO.write",
    "KEQUAL.eq",
    "KEQUAL.ite",
    "KEQUAL.ne",
    "KRYPTO.bn128add",
    "KRYPTO.bn128ate",
    "KRYPTO.bn128g2valid",
    "KRYPTO.bn128mul",
    "KRYPTO.bn128valid",
    "KRYPTO.ecdsaPubKey",
    "KRYPTO.ecdsaRecover",
    "KRYPTO.keccak256",
    "KRYPTO.keccak256raw",
    "KRYPTO.ripemd160",
    "KRYPTO.ripemd160raw",
    "KRYPTO.sha256",
    "KRYPTO.sha256raw",
    "KRYPTO.sha3256",
    "KRYPTO.sha512_256raw",
    "LIST.concat",
    "LIST.element",
    "LIST.get",
    "LIST.in",
    "LIST.make",
    "LIST.range",
    "LIST.size",
    "LIST.unit",
    "LIST.update",
    "LIST.updateAll",
    "MAP.choice",
    "MAP.concat",
    "MAP.difference",
    "MAP.element",
    "MAP.in_keys",
    "MAP.inclusion",
    "MAP.keys",
    "MAP.keys_list",
    "MAP.lookup",
    "MAP.lookupOrDefault",
    "MAP.remove",
    "MAP.removeAll",
    "MAP.size",
    "MAP.unit",
    "MAP.update",
    "MAP.updateAll",
    "MAP.values",
    "MINT.add",
    "MINT.and",
    "MINT.ashr",
    "MINT.bitwidth",
    "MINT.eq",
    "MINT.integer",
    "MINT.lshr",
    "MINT.mul",
    "MINT.ne",
    "MINT.neg",
    "MINT.not",
    "MINT.or",
    "MINT.sdiv",
    "MINT.sge",
    "MINT.sgt",
    "MINT.shl",
    "MINT.sle",
    "MINT.slt",
    "MINT.srem",
    "MINT.sub",
    "MINT.svalue",
    "MINT.udiv",
    "MINT.uge",
    "MINT.ugt",
    "MINT.ule",
    "MINT.ult",
    "MINT.urem",
    "MINT.uvalue",
    "MINT.xor",
    "SECP256K1.ecdsaRecover",
    "SET.choice",
    "SET.concat",
    "SET.difference",
    "SET.element",
    "SET.in",
    "SET.inclusion",
    "SET.intersection",
    "SET.list2set",
    "SET.set2list",
    "SET.size",
    "SET.union",
    "SET.unit",
    "STRING.base2string",
    "STRING.chr",
    "STRING.concat",
    "STRING.countAllOccurrences",
    "STRING.eq",
    "STRING.find",
    "STRING.ge",
    "STRING.gt",
    "STRING.int2string",
    "STRING.le",
    "STRING.length",
    "STRING.lt",
    "STRING.ne",
    "STRING.ord",
    "STRING.replaceAll",
    "STRING.rfind",
    "STRING.string2base",
    "STRING.string2int",
    "STRING.string2token",
    "STRING.substr",
    "STRING.token2string",
    "SUBSTITUTION.substMany",
    "SUBSTITUTION.substOne",
];

/// The hook literals of match arms in `text`: a `"NAMESPACE.name"` literal followed, after
/// spaces, by `=>` or `|`.
fn dispatch_arm_hooks(text: &str) -> BTreeSet<String> {
    let mut hooks = BTreeSet::new();
    let mut rest = text;
    while let Some(start) = rest.find('"') {
        let after = &rest[start + 1..];
        let Some(end) = after.find('"') else { break };
        let literal = &after[..end];
        let tail = after[end + 1..].trim_start();
        let (namespace, name) = literal.split_once('.').unwrap_or(("", ""));
        if !namespace.is_empty()
            && namespace
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            && namespace.starts_with(|c: char| c.is_ascii_uppercase())
            && !name.is_empty()
            && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && (tail.starts_with("=>") || tail.starts_with('|'))
        {
            hooks.insert(literal.to_owned());
        }
        rest = &after[end + 1..];
    }
    hooks
}

/// Every `hook(NAMESPACE.name)` attribute in `text`, however many a line holds (`smt-hook(..)`
/// is not one: its argument has no namespace).
fn hook_attributes(text: &str) -> BTreeSet<String> {
    text.match_indices("hook(")
        .filter_map(|(at, _)| {
            let start = at + "hook(".len();
            let end = text[start..].find(')')? + start;
            let hook = &text[start..end];
            let (namespace, name) = hook.split_once('.')?;
            (!namespace.is_empty()
                && namespace
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
                && !name.is_empty()
                && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
            .then(|| hook.to_owned())
        })
        .collect()
}

/// Re-pin R0c-fix-2 deliverable 7 (R0c-fix-1 review minor): a hook k-rust evaluates that no
/// builtin file it ships documents has a value the definition does not specify, so it is on the
/// census list (`UNDOCUMENTED_EVALUATED_HOOKS`: the `KRYPTO`, `HASH` and `SECP256K1` hooks). The
/// evaluated set is read from k-rust-backend's dispatch source (every hook literal of a match
/// arm in `builtin.rs` and `builtin/`) and pinned, so a re-pin that adds an evaluated hook fails
/// here; the documented set is every `hook(..)` the builtin files declare.
#[test]
fn evaluated_hooks_no_builtin_file_documents_are_open() {
    let backend = k_rust_backend().join("src");
    let mut files = vec![backend.join("builtin.rs")];
    let mut pending = vec![backend.join("builtin")];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                files.push(path);
            }
        }
    }
    let evaluated = files
        .iter()
        .flat_map(|path| dispatch_arm_hooks(&std::fs::read_to_string(path).unwrap()))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        evaluated,
        K_RUST_EVALUATED_HOOKS
            .iter()
            .map(|hook| (*hook).to_owned())
            .collect::<BTreeSet<_>>(),
        "k-rust's evaluated hooks changed: sweep them again"
    );
    let dir = k_rust_backend().join("../k-rust/builtin");
    let documented = BUILTIN_FILES
        .iter()
        .flat_map(|(name, _)| hook_attributes(&std::fs::read_to_string(dir.join(name)).unwrap()))
        .collect::<BTreeSet<_>>();
    let undocumented = evaluated
        .difference(&documented)
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        undocumented,
        UNDOCUMENTED_EVALUATED_HOOKS
            .iter()
            .map(|hook| (*hook).to_owned())
            .collect::<BTreeSet<_>>()
    );
    for hook in UNDOCUMENTED_EVALUATED_HOOKS {
        assert!(IMPLEMENTATION_CHOSEN_HOOKS.contains(hook), "{hook}");
    }
}

/// The quoted strings of the Rust array literal `const {name}: ... = &[ ... ];` in `source`.
fn array_strings(source: &str, head: &str) -> Vec<String> {
    let start = source.find(head).unwrap_or_else(|| panic!("no {head}")) + head.len();
    let end = source[start..].find("\n];").expect("the array ends") + start;
    source[start..end]
        .split('"')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// The hooks of k-rust's test `unsupported_hook_positions.rs` `CASES`: the first string of each
/// `(hook, application)` entry, whether the entry is on one line or spread over several.
fn unsupported_hook_cases(source: &str) -> Vec<String> {
    let head = "pub const CASES: &[(&str, &str)] = &[";
    let start = source.find(head).expect("CASES") + head.len();
    let end = source[start..].find("\n];").expect("CASES ends") + start;
    let mut lines = source[start..end].lines().map(str::trim);
    let mut hooks = Vec::new();
    while let Some(line) = lines.next() {
        let entry = if line == "(" {
            lines.next().expect("an entry's hook")
        } else if let Some(rest) = line.strip_prefix('(') {
            rest
        } else {
            continue;
        };
        let hook = entry
            .strip_prefix('"')
            .and_then(|rest| rest.split('"').next())
            .unwrap_or_else(|| panic!("an entry starts with its hook: {entry}"));
        hooks.push(hook.to_owned());
    }
    hooks
}

/// KINK-CENSUS-RUNLIST (fz26): `RUN_LIST_HOOKS` is exactly the open hooks
/// (`IMPLEMENTATION_CHOSEN_HOOKS`) that k-rust cannot evaluate in an execute request, less those of
/// its `chosen_value` classes, derived from the k-rust source the workspace builds against:
/// - its hook capability inventory (`crates/k-rust/tests/fixtures/hook-capabilities.toml`, every
///   hook of the prelude and what it requires): `execution_only` (the console operations, which
///   need a console) and the `unsupported` groups (no evaluator);
/// - for an open hook the inventory does not hold (the builtin files the prelude does not require:
///   `substitution.md`, `unification.k`, `json.md`, `timer.md`, `ffi.md`), the evaluator's own
///   test: no evaluator for its namespace (`HookName::kind` is `Other`), or its name on
///   `NOT_EVALUATED` (k-rust-backend `builtin/evaluated.rs`).
///
/// For every open hook the inventory does hold, both readings agree. Every census hook but the
/// console operation `IO.read` has a dispatch arm (`K_RUST_EVALUATED_HOOKS`), and a run-list hook
/// has none unless it is a console operation or on `NOT_EVALUATED` (an arm that answers
/// unsupported, as `substMany`'s). What stays in the census is exactly k-rust's
/// `chosen_value` hooks, the `String2Bytes`/`Bytes2String` pair and the hooks no builtin file
/// documents. Every run-list hook is a case of k-rust's `unsupported_hook_positions.rs`, which
/// checks the contract the list rests on in each position (compatibility.md 117, pinned below);
/// `IO.read` is a case there too, and stays in the census for its class.
#[test]
fn the_run_list_hooks_are_k_rusts_unevaluated_open_hooks() {
    use k_rust_backend::term::names::{HookName, HookNamespace};

    let backend = k_rust_backend();
    let inventory: toml::Value = toml::from_str(
        &std::fs::read_to_string(backend.join("../k-rust/tests/fixtures/hook-capabilities.toml"))
            .unwrap(),
    )
    .unwrap();
    let strings = |value: &toml::Value| {
        value
            .as_array()
            .unwrap()
            .iter()
            .map(|hook| hook.as_str().unwrap().to_owned())
            .collect::<Vec<_>>()
    };
    let groups = |value: &toml::Value| {
        value
            .as_array()
            .unwrap()
            .iter()
            .flat_map(|group| strings(&group["hooks"]))
            .collect::<Vec<_>>()
    };
    let execution_only = strings(&inventory["execution_only"])
        .into_iter()
        .collect::<BTreeSet<_>>();
    let unsupported = groups(&inventory["unsupported"])
        .into_iter()
        .chain(groups(&inventory["crypto"]["unsupported"]))
        .collect::<BTreeSet<_>>();
    let inventoried = strings(&inventory["implemented"])
        .into_iter()
        .chain(strings(&inventory["structural"]))
        .chain(groups(&inventory["equation_defined"]))
        .chain(strings(&inventory["crypto"]["implemented"]))
        .chain(execution_only.iter().cloned())
        .chain(unsupported.iter().cloned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        execution_only,
        BTreeSet::from(["IO.getc", "IO.putc", "IO.read", "IO.write"].map(str::to_owned))
    );
    let evaluated_rs = std::fs::read_to_string(backend.join("src/builtin/evaluated.rs")).unwrap();
    let not_evaluated = array_strings(&evaluated_rs, "const NOT_EVALUATED: &[&str] = &[")
        .into_iter()
        .collect::<BTreeSet<_>>();
    assert!(not_evaluated.contains("STRING.float2string"));
    // k-rust's `evaluated::evaluates`, which is crate-private there.
    let evaluator_has_none = |hook: &str| {
        matches!(
            HookName::parse(hook).map(HookName::kind),
            None | Some(HookNamespace::Other)
        ) || not_evaluated.contains(hook)
    };
    let unevaluated = |hook: &str| {
        execution_only.contains(hook)
            || if inventoried.contains(hook) {
                assert_eq!(
                    unsupported.contains(hook),
                    evaluator_has_none(hook),
                    "{hook}: the inventory and the evaluator disagree"
                );
                unsupported.contains(hook)
            } else {
                evaluator_has_none(hook)
            }
    };
    let derived = IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .copied()
        .filter(|hook| unevaluated(hook) && !K_RUST_IMPLEMENTATION_CHOSEN_HOOKS.contains(hook))
        .collect::<Vec<_>>();
    assert_eq!(derived, RUN_LIST_HOOKS);
    for hook in RUN_LIST_HOOKS {
        assert!(!census_hook(hook), "{hook}");
        // A dispatch arm for one answers unsupported (`substMany`'s, which k-rust checks
        // `NOT_EVALUATED` against) or needs a console.
        assert!(
            execution_only.contains(*hook)
                || not_evaluated.contains(*hook)
                || !K_RUST_EVALUATED_HOOKS.contains(hook),
            "{hook} is evaluated"
        );
    }
    let census = IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .copied()
        .filter(|hook| census_hook(hook))
        .collect::<BTreeSet<_>>();
    for hook in &census {
        assert!(
            execution_only.contains(*hook) || K_RUST_EVALUATED_HOOKS.contains(hook),
            "{hook} is not evaluated"
        );
    }
    assert_eq!(
        census,
        K_RUST_IMPLEMENTATION_CHOSEN_HOOKS
            .iter()
            .copied()
            .chain(["BYTES.string2bytes", "BYTES.bytes2string"])
            .chain(UNDOCUMENTED_EVALUATED_HOOKS.iter().copied())
            .collect::<BTreeSet<_>>()
    );
    assert!(census_hook("IO.read") && execution_only.contains("IO.read"));
    assert_eq!(
        census.len() + RUN_LIST_HOOKS.len(),
        IMPLEMENTATION_CHOSEN_HOOKS.len()
    );
    // Every moved hook is a case of k-rust's per-position test.
    let cases = unsupported_hook_cases(
        &std::fs::read_to_string(backend.join("../k-rust/tests/unsupported_hook_positions.rs"))
            .unwrap(),
    );
    assert_eq!(cases.len(), 52, "{cases:?}");
    for hook in RUN_LIST_HOOKS {
        assert!(cases.iter().any(|case| case == hook), "{hook} has no case");
    }
    assert!(cases.iter().any(|case| case == "IO.read"));
}

/// KINK-CENSUS-RUNLIST (fz26): the k-rust passage `RUN_LIST_HOOKS` rests on,
/// `docs/compatibility.md` line 117 ("Backend scope", the console paragraph, added by
/// K-RUST-CONSOLE-PIN): an execute request has no console, evaluates no console operation and no
/// hook without an evaluator, and lists an application of one whose value the run needs on
/// `unsupportedHooks`, wherever it sits. Pinned by the digest of the line without its newline; a
/// re-pin that moves or changes it fails here, and the run list is read again against it.
#[test]
fn the_console_passage_the_run_list_rests_on_is_pinned() {
    let text =
        std::fs::read_to_string(k_rust_backend().join("../../docs/compatibility.md")).unwrap();
    let line = text.split('\n').nth(116).expect("line 117");
    assert!(
        line.starts_with("Given the console of the request, `#getc`, `#putc` and `#write` are"),
        "{line}"
    );
    assert_eq!(
        kink_patch::sha256(line.as_bytes()).to_string(),
        "0e21af4d52506fe9e9cdfae85637b1613bc289ac3859c2b4a86dad061e2ee85b"
    );
}

/// Re-pin R0c-fix-1 deliverable 4 (R0c review 1 minor, decision 1): an undefined step of a rule
/// whose right-hand side applies a short-circuit operator over an operand that may be undefined
/// is excluded. On 0, `go` (`false andBool 10 /Int I >Int 0`), `fn` (the same through a function),
/// `at` and `oe` (`andThenBool`, `orElseBool`, which domains.md calls short-circuiting), `cond`
/// (`#if`) and `imp` (`impliesBool`) are each a `Trivial` leaf naming the rule in k-rust, where
/// a short-circuiting backend gives `res(..)`; before R0c-fix-1 each was a complete terminal. On
/// 1 each is a defined value and not excluded by its leaves. `rqa`, whose condition is a
/// top-level conjunction, `gd`, whose condition calls a conjunctive guard
/// (`I =/=Int 0 andBool 10 /Int I >Int 0`), and `ctl`, whose operands are total, are not
/// flagged. Since re-pin R0c-fix-2 the flagged rules exclude the definition as a whole.
#[test]
fn a_short_circuit_step_over_an_undefined_operand_is_excluded() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "scrhs");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        assert!(
            exclusions.short_circuit_conditions.is_empty(),
            "{exclusions:?}"
        );
        // Re-pin R0c-fix-2 deliverable 6: any such rule excludes the whole definition too (an
        // undefined candidate beside a defined same-priority sibling leaves no leaf). Before:
        // no definition exclusion.
        assert_eq!(
            exclusions.definition_exclusion(),
            Some(Exclusion::ShortCircuitReading)
        );
        let catalog = backend(&side, &module).rule_catalog(None).unwrap();
        let id = |label: &str| {
            catalog
                .iter()
                .find(|rule| rule.label.as_deref() == Some(label))
                .unwrap_or_else(|| panic!("{label}"))
                .id
                .clone()
        };
        let flagged = ["go", "fn", "at", "oe", "cond", "imp"];
        assert_eq!(
            exclusions.short_circuit_rules,
            flagged
                .iter()
                .map(|label| id(&format!("SCRHS.{label}")))
                .collect::<BTreeSet<_>>()
        );
        assert_eq!(
            exclusions
                .short_circuit_results
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>(),
            exclusions.short_circuit_rules
        );
        // The leaf check stays: a Trivial leaf of a flagged rule names its rule.
        let leaf_only = DefinitionExclusions {
            short_circuit_results: Vec::new(),
            ..exclusions.clone()
        };
        for label in flagged {
            let symbol = format!("Lbl{label}");
            let undefined = run(&side, &module, support::app(&symbol, vec![support::int(0)]));
            let [leaf] = undefined.leaves() else {
                panic!("{label}(0): one leaf")
            };
            assert_eq!(leaf.halt, HaltClass::Trivial, "{label}(0)");
            assert!(leaf.contradicted_total.is_none(), "{label}(0)");
            assert_eq!(
                leaf_only.run_exclusion(&undefined),
                Some(Exclusion::ShortCircuitReading),
                "{label}(0)"
            );
            let defined = run(&side, &module, support::app(&symbol, vec![support::int(1)]));
            assert_eq!(leaf_only.run_exclusion(&defined), None, "{label}(1)");
            assert_eq!(
                exclusions.run_exclusion(&defined),
                Some(Exclusion::ShortCircuitReading),
                "{label}(1)"
            );
        }
        for label in ["rqa", "ctl", "gd"] {
            let symbol = format!("Lbl{label}");
            let execution = run(&side, &module, support::app(&symbol, vec![support::int(0)]));
            assert_eq!(leaf_only.run_exclusion(&execution), None, "{label}(0)");
        }
    });
}

/// Re-pin R0c-fix-1 deliverable 4: a condition that depends on the short-circuit reading leaves
/// no leaf to read. `rq`'s condition `true orBool 10 /Int I >Int 0` is undefined on 0 in k-rust,
/// so `rq(0)` is a Stuck leaf naming no rule, where a short-circuiting backend steps to
/// `res(true)`; `vg` applies `g`, whose first equation has that condition, so `vg(0)` gives
/// `num(2)` in k-rust and `num(1)` in the other reading, with complete leaves. Both rules are
/// named, and every run on the definition is excluded.
#[test]
fn a_condition_that_depends_on_the_short_circuit_reading_excludes_the_definition() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "screq");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        assert_eq!(
            exclusions.definition_exclusion(),
            Some(Exclusion::ShortCircuitReading)
        );
        let catalog = backend(&side, &module).rule_catalog(None).unwrap();
        let named = |label: &str| {
            let rule = catalog
                .iter()
                .find(|rule| rule.label.as_deref() == Some(label))
                .unwrap_or_else(|| panic!("{label}"));
            exclusions.short_circuit_conditions.contains(&rule.id)
        };
        assert!(named("SCREQ.rq") && named("SCREQ.vg"), "{exclusions:?}");
        assert!(exclusions.short_circuit_symbols.contains("Lblg"));
        let stuck = run(&side, &module, support::app("Lblrq", vec![support::int(0)]));
        let [leaf] = stuck.leaves() else {
            panic!("rq(0): one leaf")
        };
        assert_eq!(
            (leaf.halt, leaf.undefined_rule.is_none()),
            (HaltClass::Stuck, true)
        );
        assert_eq!(
            exclusions.run_exclusion(&stuck),
            Some(Exclusion::ShortCircuitReading)
        );
        let value = run(&side, &module, support::app("Lblvg", vec![support::int(0)]));
        let [leaf] = value.leaves() else {
            panic!("vg(0): one leaf")
        };
        assert_eq!(leaf.halt, HaltClass::Stuck);
        assert!(leaf.branch.state.to_string().contains(r#""2""#));
        assert_eq!(
            exclusions.run_exclusion(&value),
            Some(Exclusion::ShortCircuitReading)
        );
    });
}

/// KINK-SC-DEFINED (fz26 P7-SIMPLE-KINK design): the prelude equation of `findChar` skips
/// operands over the partial `findString` and `findChar`, but every such application in a
/// skipped operand is also evaluated by an operand that runs whenever it is skipped (an `#if`
/// condition or the other branch), so neither reading leaves one undefined where the other gives
/// a value: `findChar` does not depend on the reading, the rule applying it is not flagged, and
/// `fc("xb")` is evidence. Before KINK-SC-DEFINED `findChar` was reading-dependent and the
/// definition was excluded.
///
/// `replace` and `replaceAll` (prelude `STRING-COMMON`) stay reading-dependent: `replace`'s
/// `owise` equation negates `Count >Int 0 andBool findString(Source, ToReplace, 0) >=Int 0`,
/// whose skippable `findString` application, of a function declared partial, no other operand
/// evaluates; at `Count` 0 a short-circuiting backend takes the `owise` equation whatever
/// `findString` is, where k-rust's reading needs it defined. `replaceAll` applies `replace`.
/// Neither is applied here, so nothing is excluded.
#[test]
fn a_skipped_operand_whose_partial_terms_another_operand_evaluates_flags_nothing() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "scstr");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let flagged = exclusions
            .short_circuit_symbols
            .iter()
            .map(|symbol| {
                symbol
                    .split_once("'LPar")
                    .map_or(symbol.as_str(), |(head, _)| head)
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            flagged,
            BTreeSet::from(["Lblreplace", "LblreplaceAll"]),
            "{exclusions:?}"
        );
        assert!(
            exclusions.short_circuit_conditions.is_empty()
                && exclusions.short_circuit_results.is_empty(),
            "{exclusions:?}"
        );
        assert_eq!(exclusions.definition_exclusion(), None);
        let string = parse_pattern(r#"\dv{SortString{}}("xb")"#).unwrap();
        let execution = run(&side, &module, support::app("Lblfc", vec![string]));
        let [leaf] = execution.leaves() else {
            panic!("fc(\"xb\"): one leaf")
        };
        assert_eq!(leaf.halt, HaltClass::Stuck);
        assert!(leaf.branch.state.to_string().contains(r#""1""#));
        assert_eq!(exclusions.run_exclusion(&execution), None);
    });
}

/// KINK-SC-DEFINED: the prelude's stdin rules, which kompile copies into a definition with a
/// `stdin` stream cell, have `requires` clauses over `findChar`; with `findChar` no longer
/// reading-dependent, no rule of such a definition is a short-circuit row. Before, three rules
/// were (stock SIMPLE's `short-circuit-reading` exclusion). The prelude's `replace` and
/// `replaceAll` stay reading-dependent (above), but no rule applies them. Since
/// KINK-CENSUS-RUNLIST the copied rules' console operation (`#getc`) is on the run list, so the
/// definition is not excluded at all; before, the census of `IO.getc` excluded it.
#[test]
fn the_prelude_stdin_rules_are_no_short_circuit_row() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "scin");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        assert!(
            exclusions.short_circuit_conditions.is_empty()
                && exclusions.short_circuit_results.is_empty()
                && exclusions
                    .short_circuit_symbols
                    .iter()
                    .all(|symbol| symbol.starts_with("Lblreplace")),
            "{exclusions:?}"
        );
        assert_eq!(exclusions.definition_exclusion(), None, "{exclusions:?}");
    });
}

/// KINK-SC-DEFINED (fz26 P7-SIMPLE-KINK review B3 and round 2): `f(A) => #if A >=Int 0 #then A
/// #else pd(A) #fi`, with `pd` defined exactly on negatives, skips `pd(A)` where a guard holds,
/// and `pd(A)` occurs in no other operand: `f(3)` is undefined in k-rust's reading and `3` in a
/// short-circuiting one, so `f` stays reading-dependent whatever the guard says. In the covered
/// variant (`scpdc`, `#if pd(A) >Int 0 #then pd(A) #else 0 #fi`) the condition, evaluated on every
/// path, evaluates the skippable `pd(A)` too, so where it is undefined both readings are: `f` is
/// not flagged, `go(-3)` reaches `res(3)` and is evidence, and `go(3)`, where `pd(3)` is undefined
/// in both readings, is not excluded for the reading. Before KINK-SC-DEFINED the covered variant
/// was flagged too.
#[test]
fn a_skipped_operand_no_other_operand_evaluates_stays_flagged() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "scpd");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        assert!(
            exclusions.short_circuit_symbols.contains("Lblf"),
            "{exclusions:?}"
        );
        assert_eq!(
            exclusions.definition_exclusion(),
            Some(Exclusion::ShortCircuitReading)
        );
        let (side, module) = fixture("r0c", "scpdc");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        assert!(
            exclusions.short_circuit_symbols.is_empty(),
            "{exclusions:?}"
        );
        assert_eq!(exclusions.definition_exclusion(), None);
        let value = run(
            &side,
            &module,
            support::app("Lblgo", vec![support::int(-3)]),
        );
        let [leaf] = value.leaves() else {
            panic!("go(-3): one leaf")
        };
        assert_eq!(leaf.halt, HaltClass::Stuck);
        assert!(leaf.branch.state.to_string().contains(r#""3""#));
        assert_eq!(exclusions.run_exclusion(&value), None);
        let undefined = run(&side, &module, support::app("Lblgo", vec![support::int(3)]));
        assert!(
            undefined
                .leaves()
                .iter()
                .any(|leaf| leaf.halt == HaltClass::Trivial),
            "go(3): an undefined step"
        );
        assert_ne!(
            exclusions.run_exclusion(&undefined),
            Some(Exclusion::ShortCircuitReading)
        );
    });
}

/// KINK-SC-DEFINED: the short-circuit analysis takes the terms every evaluation of an operator
/// evaluates as its non-skippable operands' plus those common to all its skippable ones. That
/// under-approximates every evaluation only if each operator of `SHORT_CIRCUIT_HOOKS` evaluates
/// at least one of its skippable positions, and every other position whenever one is skipped.
/// Checked here from each operator's meaning, read on `Bool` (an instance of `#if`'s sort):
/// - its arity is that of the prelude production with its hook, and its skippable positions are
///   distinct positions of it;
/// - for every value of its other positions, its result is no constant of the skippable ones, so
///   no evaluation can give it without reading one of them;
/// - its other positions are `#if`'s condition alone, which both prelude rules of `#if` read
///   (`requires C`, `requires notBool C`), so every evaluation evaluates it.
#[test]
fn every_short_circuit_operator_evaluates_a_skippable_operand_and_every_other_one() {
    type Meaning = fn(&[bool]) -> bool;
    let meaning = |hook: &str| -> Meaning {
        match hook {
            "BOOL.and" | "BOOL.andThen" => |v| v[0] && v[1],
            "BOOL.or" | "BOOL.orElse" => |v| v[0] || v[1],
            "BOOL.implies" => |v| !v[0] || v[1],
            "KEQUAL.ite" => |v| if v[0] { v[1] } else { v[2] },
            other => panic!("{other}: no meaning given; check the invariant for it first"),
        }
    };
    let domains =
        std::fs::read_to_string(k_rust_backend().join("../k-rust/builtin/domains.md")).unwrap();
    // The number of non-terminals of the production that declares `hook`.
    let arity = |hook: &str| -> usize {
        let line = domains
            .lines()
            .find(|line| line.contains(&format!("hook({hook})")))
            .unwrap_or_else(|| panic!("domains.md declares {hook}"));
        let body = line.split_once("::=").map_or(line, |(_, body)| body);
        let body = &body[..body.rfind('[').unwrap()];
        let mut quoted = false;
        let mut unquoted = String::new();
        for character in body.chars() {
            if character == '"' {
                quoted = !quoted;
            } else if !quoted {
                unquoted.push(character);
            }
        }
        unquoted
            .split_whitespace()
            .filter(|word| word.starts_with(|c: char| c.is_ascii_uppercase()))
            .count()
    };
    for (hook, skippable) in SHORT_CIRCUIT_HOOKS {
        let n = arity(hook);
        let positions = skippable.iter().copied().collect::<BTreeSet<_>>();
        assert!(
            !positions.is_empty()
                && positions.len() == skippable.len()
                && positions.iter().all(|p| *p < n),
            "{hook}: {skippable:?} of arity {n}"
        );
        let meaning = meaning(hook);
        let others = (0..n)
            .filter(|p| !positions.contains(p))
            .collect::<Vec<_>>();
        for fixed in 0..1u32 << others.len() {
            let results = (0..1u32 << positions.len())
                .map(|free| {
                    let mut values = vec![false; n];
                    for (bit, position) in others.iter().enumerate() {
                        values[*position] = fixed >> bit & 1 == 1;
                    }
                    for (bit, position) in positions.iter().enumerate() {
                        values[*position] = free >> bit & 1 == 1;
                    }
                    meaning(&values)
                })
                .collect::<BTreeSet<_>>();
            assert_eq!(
                results.len(),
                2,
                "{hook}: constant in its skippable positions at {fixed:b}"
            );
        }
        if *hook == "KEQUAL.ite" {
            assert_eq!(others, [0], "{hook}");
            for rule in [
                "rule #if C:Bool #then B1::K #else _ #fi => B1 requires C\n",
                "rule #if C:Bool #then _ #else B2::K #fi => B2 requires notBool C\n",
            ] {
                assert!(domains.contains(rule), "domains.md: {rule}");
            }
        } else {
            assert!(others.is_empty(), "{hook}: {others:?}");
        }
    }
}

/// Re-pin R0c deliverable 2 (the R0b reviewer's probe): a rule that applies `Base2String`, whose
/// letter case domains.md leaves to the backend, flags its definition, so every run on it is
/// excluded; before R0c the census flagged nothing and the run of `start(255)` was one complete
/// Stuck leaf `str("ff")`.
#[test]
fn a_base2string_rule_flags_the_definition() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "base16");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let [reference] = exclusions.implementation_chosen.as_slice() else {
            panic!("{exclusions:?}")
        };
        assert_eq!(reference.hook, "STRING.base2string");
        assert_eq!(reference.module, "BASE16");
        let execution = run(
            &side,
            &module,
            support::app("Lblstart", vec![support::int(255)]),
        );
        assert_eq!(
            execution
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>(),
            [HaltClass::Stuck]
        );
        assert_eq!(
            exclusions.run_exclusion(&execution),
            Some(Exclusion::ImplementationChosenHook)
        );
    });
}

/// Decision 1: a rule that lists a map's keys flags its definition, so every run on it is
/// excluded, one that never lists keys included; a test's initial state that applies such a hook
/// flags its run; a definition that only imports MAP is not flagged.
#[test]
fn an_implementation_chosen_hook_flags_the_definition_or_the_state() {
    on_a_big_stack(|| {
        let (side, module) = r0b("implchosen");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let [reference] = exclusions.implementation_chosen.as_slice() else {
            panic!("{exclusions:?}")
        };
        assert_eq!(reference.hook, "MAP.keys_list");
        assert_eq!(reference.module, "IMPLCHOSEN");
        assert_eq!(
            exclusions.definition_exclusion(),
            Some(Exclusion::ImplementationChosenHook)
        );
        let execution = run(
            &side,
            &module,
            support::app("Lblcount", vec![support::int(3)]),
        );
        assert_eq!(
            exclusions.run_exclusion(&execution),
            Some(Exclusion::ImplementationChosenHook)
        );

        let (free, free_module) = r0b("keysfree");
        let exclusions = DefinitionExclusions::of_validated(&free, &free_module).unwrap();
        assert!(
            exclusions.implementation_chosen.is_empty(),
            "{exclusions:?}"
        );
        assert_eq!(exclusions.definition_exclusion(), None);
        let execution = run(
            &free,
            &free_module,
            support::app("Lblstart", vec![support::int(3)]),
        );
        assert_eq!(exclusions.run_exclusion(&execution), None);
        let keys = parse_pattern(
            r#"Lblkeys{}(Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))))"#,
        )
        .unwrap();
        let plain = support::app("Lblstart", vec![support::int(3)]);
        let (listed, unlisted) = backend(&free, &free_module)
            .with_solver(None, |definition, _| {
                Ok::<_, k_rust::backend::BackendError>((
                    state_references_implementation_chosen(
                        definition,
                        &support::initial_state(keys.clone(), "SortProg"),
                    ),
                    state_references_implementation_chosen(
                        definition,
                        &support::initial_state(plain.clone(), "SortProg"),
                    ),
                ))
            })
            .unwrap();
        assert!(listed && !unlisted);
    });
}

/// Decision 2 (finding A-13), k-rust's tdiv/td shape: an undefined step through a `total`
/// function whose equation is undefined there names the contradicted claim, and an undefined step
/// of a `preserves-definedness` rule names that rule; both runs are excluded. An undefined step of
/// a rule that makes no claim is a complete terminal and is not excluded, nor is a defined run.
#[test]
fn an_undefined_step_that_contradicts_a_claim_excludes_the_run() {
    on_a_big_stack(|| {
        let (side, module) = r0b("tdiv");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let catalog = backend(&side, &module).rule_catalog(None).unwrap();
        let id = |label: &str| {
            catalog
                .iter()
                .find(|rule| rule.label.as_deref() == Some(label))
                .unwrap_or_else(|| panic!("{label}"))
                .id
                .clone()
        };
        assert!(exclusions.preserves_definedness.contains(&id("TDIV.pd")));
        assert!(!exclusions.preserves_definedness.contains(&id("TDIV.half")));
        let leaf = |symbol: &str, argument: i64| {
            let execution = run(
                &side,
                &module,
                support::app(symbol, vec![support::int(argument)]),
            );
            let [leaf] = execution.leaves() else {
                panic!("{symbol}({argument}): {execution:?}")
            };
            (leaf.clone(), exclusions.run_exclusion(&execution))
        };
        let (td, excluded) = leaf("Lbltdiv", -1);
        assert_eq!(td.halt, HaltClass::Trivial);
        let contradicted = td.contradicted_total.as_ref().expect("names the claim");
        assert_eq!(contradicted.symbol, "Lbltd");
        assert_eq!(contradicted.rule_id, id("TDIV.tdeq"));
        assert_eq!(excluded, Some(Exclusion::ContradictedClaim));
        let (pd, excluded) = leaf("Lblpd", -1);
        assert_eq!(pd.halt, HaltClass::Trivial);
        assert_eq!(pd.contradicted_total, None);
        assert_eq!(
            pd.undefined_rule.as_ref().map(|rule| &rule.id),
            Some(&id("TDIV.pd"))
        );
        assert_eq!(excluded, Some(Exclusion::ContradictedClaim));
        let (half, excluded) = leaf("Lblhalf", 0);
        assert_eq!(half.halt, HaltClass::Trivial);
        assert_eq!(
            half.undefined_rule.as_ref().map(|rule| &rule.id),
            Some(&id("TDIV.half"))
        );
        assert_eq!(excluded, None);
        // The one reading of an undefined step's rule (fz26 FZ-COMPARABLE-B), which the leaf
        // predicates and kink-flow's witness filter share.
        assert_eq!(
            exclusions.undefined_step_exclusions(&id("TDIV.pd")),
            [Exclusion::ContradictedClaim]
        );
        assert!(
            exclusions
                .undefined_step_exclusions(&id("TDIV.half"))
                .is_empty()
        );
        assert!(exclusions.contradicts_a_claim(&pd) && !exclusions.contradicts_a_claim(&half));
        let short = DefinitionExclusions {
            short_circuit_rules: std::iter::once(id("TDIV.half")).collect(),
            ..exclusions.clone()
        };
        assert_eq!(
            short.undefined_step_exclusions(&id("TDIV.half")),
            [Exclusion::ShortCircuitReading]
        );
        assert!(short.short_circuit_step(&half) && !short.short_circuit_step(&pd));
        for (symbol, argument) in [("Lbltdiv", 0), ("Lblpd", 0)] {
            let (defined, excluded) = leaf(symbol, argument);
            assert_eq!(defined.halt, HaltClass::Stuck, "{symbol}");
            assert_eq!(excluded, None, "{symbol}");
        }
    });
}

/// `deep(N)` recurses `N` levels, not in tail position (k-rust tests/execution_stack_stops.rs).
const DEEP: &str = r#"[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    sort SortS{} []
    symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
endmodule []"#;

/// Finding A-06: a run that met a stop for lack of native stack reports it (`stackStops`), both
/// adapter entry points keep the count, and the run is excluded; the same run with the default
/// stack budget reports none and is not excluded.
///
/// `deep(12000)`: with a zero simplification stack budget the run first meets a stack stop at
/// 4,000 to 6,000 levels (measured 2026-10-22 at the dev profile's opt-level 1 on an 8 MiB
/// thread, after backend sorts became interned `Copy` handles, which more than halved a level's
/// frame: 4,000 levels do not stop, 6,000 do; about 2,000 before), so 12,000 keeps a factor of
/// two; the run with the default budget then costs less than half the former `deep(30000)`.
#[test]
fn a_run_with_a_stack_stop_is_excluded() {
    let result = |stack_budget: Option<usize>| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(move || {
                let mut backend = Backend::new(DEEP, "MAIN", BackendOptions::default()).unwrap();
                if let Some(stack_budget) = stack_budget {
                    backend.set_simplification_stack_budget(stack_budget);
                }
                let state = parse_pattern(r#"done{}(deep{}(\dv{SortInt{}}("12000")))"#).unwrap();
                let bounds = ExecutionBudget {
                    max_depth: Some(0),
                    ..budget()
                };
                let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
                let unobserved = adapter
                    .execute_unobserved(&mut backend, &state, bounds)
                    .unwrap();
                let adapted = adapter.execute(&mut backend, &state, bounds).unwrap();
                (unobserved.stack_stops, adapted)
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let (unobserved, stopped) = result(Some(0));
    assert!(unobserved >= 1 && stopped.stack_stops() >= 1, "{stopped:?}");
    assert_eq!(
        DefinitionExclusions::default().run_exclusion(&stopped),
        Some(Exclusion::StackStop)
    );
    let (unobserved, clean) = result(None);
    assert_eq!((unobserved, clean.stack_stops()), (0, 0));
    assert_eq!(DefinitionExclusions::default().run_exclusion(&clean), None);
}

/// k-rust's confluence_budget fixture (k-rust-backend tests/backend/confluence_budget.rs): a
/// partial `p` with the ceil equation `\ceil(p(X)) = (hk(n) == n)` and the rewrite rule
/// `state => done(p(0))`, whose definedness the load discharges by simplifying `hk(n) == n`, which
/// recurses `n` levels.
fn partial_definition(n: u64) -> String {
    let int = |value: u64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
    let equation = |pattern: &str, right: &str, requires: &str| {
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, {pattern}), \top{{R}}())), \equals{{SortInt{{}}, R}}(hk{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}({right}, \top{{SortInt{{}}}}()))) []"
        )
    };
    let axioms = [
        equation(&int(0), &int(0), r"\top{R}()"),
        equation(
            "VarN:SortInt{}",
            &format!(
                "addInt{{}}(hk{{}}(subInt{{}}(VarN:SortInt{{}}, {})), {})",
                int(1),
                int(1)
            ),
            &format!(
                r#"\equals{{SortBool{{}}, R}}(gtInt{{}}(VarN:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true"))"#,
                int(0)
            ),
        ),
        format!(
            r"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{R, R}}(\ceil{{SortInt{{}}, R}}(p{{}}(X:SortInt{{}})), \equals{{SortInt{{}}, R}}(hk{{}}({}), {}))) []",
            int(n),
            int(n)
        ),
        r#"axiom{} \rewrites{SortS{}}(\and{SortS{}}(state{}(), \top{SortS{}}()), done{}(p{}(\dv{SortInt{}}("0")))) [label{}("advance")]"#.to_owned(),
    ];
    format!(
        r#"[] module MAIN
    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
    hooked-symbol subInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.sub"), smt-hook{{}}("-")]
    hooked-symbol addInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
    hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
    hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
    hooked-symbol hk{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), hook{{}}("MYHOOK.hk")]
    symbol p{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
    sort SortS{{}} []
    symbol state{{}}() : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
    symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
    {}
endmodule []"#,
        axioms.join("\n    ")
    )
}

/// Finding A-08: a load whose discharge of rewrite-rule definedness runs out of stack counts the
/// stop, read through `select_definition` on the backend, and excludes every run on it; a shallow
/// discharge on the same thread counts nothing.
#[test]
fn a_load_with_a_stack_stop_excludes_every_run() {
    let exclusions = |n: u64| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(move || {
                let kore = parse_definition(&partial_definition(n)).unwrap();
                with_simplification_stack_budget(0, || {
                    let mut backend =
                        Backend::from_definition(kore.clone(), "MAIN", BackendOptions::default())
                            .unwrap();
                    let selected = backend.select_definition(None).unwrap();
                    DefinitionExclusions::of(&kore, &selected, &[])
                })
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let deep = exclusions(100_000);
    assert!(deep.load_stack_stops >= 1, "{deep:?}");
    assert_eq!(deep.definition_exclusion(), Some(Exclusion::LoadStackStop));
    let shallow = exclusions(100);
    assert_eq!(shallow.load_stack_stops, 0);
    assert_eq!(shallow.definition_exclusion(), None);
}

/// A hooked division: partial with the ceil equation `\ceil(mydiv(X, Y)) = (Y =/= 0)`, or
/// declared `total`.
fn division(total: bool) -> String {
    format!(
        r#"[] module MAIN
    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
    hooked-symbol mydiv{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), {}hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
    sort SortS{{}} []
    symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
    {}
endmodule []"#,
        if total { "total{}(), " } else { "" },
        if total {
            ""
        } else {
            r#"axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortInt{}, R}(mydiv{}(X:SortInt{}, Y:SortInt{})), \not{R}(\equals{SortInt{}, R}(Y:SortInt{}, \dv{SortInt{}}("0"))))) []"#
        }
    )
}

/// Re-pin R0b deliverable 5 (finding A-12): since 501f18b9 k-rust's admission restates a
/// pattern's definedness from the admitting definition. A mutant that declares a partial hooked
/// division `total` can leave a leaf `done(X) /\ mydiv(X, 0) = 1`. Admitted under the baseline,
/// whose ceil equation makes `mydiv(X, 0)` undefined, the leaf gains the conjunct `false`, and
/// with Z3 it is refuted (`Unsat`, so the mutant leaf would be discarded) although the mutant has
/// instances of it. The decider for a mutant's leaves decides their feasibility on the mutant's
/// own definition, where the leaf is not refuted; the baseline's own leaves are still decided on
/// the baseline. Without a solver neither is decided.
#[test]
fn a_mutant_leaf_is_admitted_under_the_mutant_definition() {
    use kink_native::feasibility::LeafFeasibility;
    let state = k_rust::kore::codec::to_value(
        &parse_pattern(
            r#"\and{SortS{}}(done{}(VarX:SortInt{}), \equals{SortInt{}, SortS{}}(mydiv{}(VarX:SortInt{}, \dv{SortInt{}}("0")), \dv{SortInt{}}("1")))"#,
        )
        .unwrap(),
    )
    .unwrap();
    let mut baseline = Backend::new(&division(false), "MAIN", BackendOptions::default()).unwrap();
    let mut mutant = Backend::new(&division(true), "MAIN", BackendOptions::default()).unwrap();
    let initial = parse_pattern("done{}(VarX:SortInt{})").unwrap();
    let (own, shared) = baseline
        .with_solver(None, |definition, solver| {
            let own =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&initial))
                    .shared_leaf_feasibility(&state);
            let shared = mutant.with_solver(None, |leaf_definition, leaf_solver| {
                Ok::<_, k_rust::backend::BackendError>(
                    ObservationDecider::for_leaves_of(
                        definition,
                        leaf_definition,
                        leaf_solver,
                        TestInitialState::of_test(&initial),
                    )
                    .shared_leaf_feasibility(&state),
                )
            })?;
            Ok::<_, k_rust::backend::BackendError>((own, shared))
        })
        .unwrap();
    if SolverProfile::BUILD == SolverProfile::Z3 {
        assert_eq!(own, LeafFeasibility::Unsat);
        assert_ne!(shared, LeafFeasibility::Unsat, "{shared:?}");
    } else {
        assert_eq!(
            (own, shared),
            (LeafFeasibility::Unknown, LeafFeasibility::Unknown)
        );
    }
}

mod kink_tier {
    use super::*;

    /// Decision 4 / finding C-09: census rule C stays exercised by a definition k-rust 501f18b9
    /// compiles: a well-sorted List whose role symbols carry no role hook is flagged under rule C for
    /// each of its three roles, so kink-corpus admission refuses it (`vi-t13`).
    #[test]
    #[ignore = "kink"]
    fn a_compiling_hookless_role_is_refused_by_census_rule_c() {
        on_a_big_stack(|| {
            let (side, _) = r0b("hooklessrole");
            let census = kink_native::declaration_census(&side).unwrap();
            assert_eq!(census.verdict(), kink_native::CensusVerdict::Flagged);
            let findings = census
                .findings()
                .iter()
                .map(|finding| (finding.class, finding.symbol.clone()))
                .collect::<Vec<_>>();
            eprintln!("HOOKLESS {}", census.text());
            assert_eq!(findings.len(), 3, "{}", census.text());
            assert!(
                findings
                    .iter()
                    .all(|(class, _)| *class == kink_native::CensusClass::C),
                "{}",
                census.text()
            );
        });
    }

    /// Re-pin R0c-fix-3 deliverable 5 (R0c-fix-2 review minor 3, `r0c/eqcond.k`): k-rust 501f18b9
    /// names an `\equals` between two possibly undefined terms in a rule or equation condition as a
    /// gap of its own answers ("Two gaps remain", `docs/compatibility.md`): its SMT translation has no
    /// model where both sides are undefined, so answers may wrongly be empty, `valid` or `proven`.
    /// `go`'s condition `{ 10 /Int I #Equals 10 /Int I }` is one, and excludes the definition; the K
    /// Bool conditions kompile states as `\equals(C, true)` are not.
    #[test]
    #[ignore = "kink"]
    fn a_condition_that_equates_two_terms_excludes_the_definition() {
        on_a_big_stack(|| {
            let (side, module) = fixture("r0c", "eqcond");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let go = backend(&side, &module)
                .rule_catalog(None)
                .unwrap()
                .into_iter()
                .find(|rule| rule.label.as_deref() == Some("EQCOND.go"))
                .expect("go")
                .id;
            assert_eq!(exclusions.equals_conditions, [go]);
            assert_eq!(
                exclusions.definition_exclusion(),
                Some(Exclusion::EqualsCondition)
            );
            let (side, module) = fixture("r0c", "nomatch");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert!(exclusions.equals_conditions.is_empty());
            assert_eq!(exclusions.definition_exclusion(), None);
        });
    }

    /// Re-pin R0c-fix-2 deliverable 6 (R0c-fix-1 review major, the reviewer's `scsib.k`): `siba`'s
    /// right-hand side applies `andBool` over `10 /Int (I -Int 1) >Int 0` beside the same-priority
    /// sibling `sibb`. On `sib(1)` k-rust drops `siba`'s undefined candidate and the run is one
    /// complete Stuck leaf `other()` with no undefined-step leaf to read, where a short-circuiting
    /// backend also reaches `res(false)`: the leaf check misses it, and the definition-level rule
    /// excludes it. Before R0c-fix-2 the run was evidence.
    #[test]
    #[ignore = "kink"]
    fn a_short_circuit_candidate_beside_a_sibling_excludes_the_definition() {
        on_a_big_stack(|| {
            let (side, module) = fixture("r0c", "scsib");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let siba = backend(&side, &module)
                .rule_catalog(None)
                .unwrap()
                .into_iter()
                .find(|rule| rule.label.as_deref() == Some("SCSIB.siba"))
                .expect("siba")
                .id;
            assert_eq!(exclusions.short_circuit_results, [siba]);
            assert_eq!(
                exclusions.definition_exclusion(),
                Some(Exclusion::ShortCircuitReading)
            );
            let execution = run(
                &side,
                &module,
                support::app("Lblsib", vec![support::int(1)]),
            );
            let [leaf] = execution.leaves() else {
                panic!("sib(1): one leaf")
            };
            assert_eq!(leaf.halt, HaltClass::Stuck);
            let leaf_only = DefinitionExclusions {
                short_circuit_results: Vec::new(),
                ..exclusions.clone()
            };
            assert_eq!(leaf_only.run_exclusion(&execution), None);
            assert_eq!(
                exclusions.run_exclusion(&execution),
                Some(Exclusion::ShortCircuitReading)
            );
        });
    }

    /// Re-pin R0c-fix-1 deliverable 2 (R0c review 1 major 3, the reviewer's alpha-equivalence probe):
    /// beta reduction through `SUBSTITUTION.substOne`. On `run(app(lam(x, lam(y, x)), y))` the
    /// baseline gives `out(lam(y0, y))` and the mutant, which routes the substitution through `y0`,
    /// the alpha-equivalent `out(lam(y1, y))`: the two differ only in the suffix k-rust mints
    /// (substitution.md 83-88 leaves it to the backend). Both definitions are flagged, so neither
    /// run is evidence; before R0c-fix-1 neither was flagged and the pair distinguished.
    #[test]
    #[ignore = "kink"]
    fn a_substitution_rule_flags_the_definition() {
        on_a_big_stack(|| {
            let program = parse_pattern(
                r#"Lblrun{}(Lblapp{}(Lbllam{}(\dv{SortKVar{}}("x"), Lbllam{}(\dv{SortKVar{}}("y"), inj{SortKVar{}, SortExp{}}(\dv{SortKVar{}}("x")))), inj{SortKVar{}, SortExp{}}(\dv{SortKVar{}}("y"))))"#,
            )
            .unwrap();
            let mut finals = Vec::new();
            for name in ["lam", "lamm"] {
                let (side, module) = fixture("r0c", name);
                let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
                assert!(
                    exclusions
                        .implementation_chosen
                        .iter()
                        .any(|reference| reference.hook == "SUBSTITUTION.substOne"),
                    "{name}: {exclusions:?}"
                );
                let execution = run(&side, &module, program.clone());
                let [leaf] = execution.leaves() else {
                    panic!("{name}: one leaf")
                };
                assert_eq!(leaf.halt, HaltClass::Stuck, "{name}");
                finals.push(leaf.branch.state.to_string());
                assert_eq!(
                    exclusions.run_exclusion(&execution),
                    Some(Exclusion::ImplementationChosenHook),
                    "{name}"
                );
            }
            // The two finals differ, by the minted suffix alone.
            assert!(finals[0].contains(r#""y0""#), "{}", finals[0]);
            assert!(finals[1].contains(r#""y1""#), "{}", finals[1]);
            assert_eq!(finals[0].replace(r#""y0""#, r#""y1""#), finals[1]);
        });
    }

    /// Finding C-10: an equation rooted at a collection role symbol (reported by the load as
    /// `IndexedAt(List)`) or a simplification rooted at one (which the load does not report) makes no
    /// collection term of the definition a terminal value; without the flag the same decider gives
    /// the canonical value.
    #[test]
    #[ignore = "kink"]
    fn an_axiom_rooted_at_a_role_symbol_distrusts_collection_terminals() {
        on_a_big_stack(|| {
            for (name, element) in [("rolerooted", "LblListItem"), ("rolesimp", "LblSetItem")] {
                let (side, module) = r0b(name);
                let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
                assert!(!exclusions.collections_trusted(), "{name}: {exclusions:?}");
                assert_eq!(exclusions.definition_exclusion(), None, "{name}");
                let execution = run(
                    &side,
                    &module,
                    support::app("Lblstart", vec![support::int(5)]),
                );
                assert_eq!(exclusions.run_exclusion(&execution), None, "{name}");
                let [leaf] = execution.leaves() else {
                    panic!("{name}: {execution:?}")
                };
                let state = k_rust::kore::codec::from_value(&leaf.branch.state).unwrap();
                let term = match &state {
                    Pattern::And { arguments, .. } => arguments[0].clone(),
                    term => term.clone(),
                };
                assert!(format!("{term:?}").contains(element), "{name}: {term:?}");
                let initial = support::initial_state(
                    support::app("Lblstart", vec![support::int(5)]),
                    "SortProg",
                );
                backend(&side, &module)
                    .with_solver(None, |definition, solver| {
                        let trusted = ObservationDecider::new(
                            definition,
                            solver,
                            TestInitialState::of_test(&initial),
                        );
                        assert!(trusted.terminal_value(&term).is_some(), "{name}");
                        let distrusted = ObservationDecider::new(
                            definition,
                            solver,
                            TestInitialState::of_test(&initial),
                        )
                        .trusting_collections(exclusions.collections_trusted());
                        assert_eq!(distrusted.terminal_value(&term), None, "{name}");
                        Ok::<_, k_rust::backend::BackendError>(())
                    })
                    .unwrap();
            }
        });
    }

    /// Re-pin R0c-fix-4 (R0c-fix-3 review minor 6, `r0c/eqlemma.k`): the scan reads every axiom's
    /// antecedents and both sides of its conclusion, whatever its left-hand side: the requires of a
    /// `#Ceil` lemma, an equation's `ensures` and a rewrite rule's `ensures` each hold
    /// `{ I #Equals .. }`, and each is listed; the equation `f` without one is not.
    #[test]
    #[ignore = "kink"]
    fn an_equality_in_a_lemma_or_an_ensures_excludes_the_definition() {
        on_a_big_stack(|| {
            let (side, module) = fixture("r0c", "eqlemma");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let catalog = backend(&side, &module).rule_catalog(None).unwrap();
            let id = |label: &str| {
                catalog
                    .iter()
                    .find(|rule| rule.label.as_deref() == Some(label))
                    .unwrap_or_else(|| panic!("{label}"))
                    .id
                    .clone()
            };
            let mut expected = ["EQLEMMA.fceil", "EQLEMMA.g", "EQLEMMA.go"]
                .map(id)
                .to_vec();
            expected.sort();
            let mut found = exclusions.equals_conditions.clone();
            found.sort();
            assert_eq!(found, expected);
            assert!(!found.contains(&id("EQLEMMA.f")));
            assert_eq!(
                exclusions.definition_exclusion(),
                Some(Exclusion::EqualsCondition)
            );
        });
    }

    /// Re-pin R0-tail (R0c-fix-4 review minor 1, `r0c/eqexists.k`): a rewrite rule with an
    /// existential variable has its right-hand side under `\exists ?Y`, and the scan reads its
    /// `ensures` there too. `go`'s `{ ?Y #Equals 10 /Int I }` and `gy`'s two equalities are each
    /// listed, and `plain` is not. At 1ee9955 the scan read only an `\and` at the top of the right-hand
    /// side, and this definition was compared (the reviewer's probe: `equals_conditions []`).
    #[test]
    #[ignore = "kink"]
    fn an_equality_in_an_existential_ensures_excludes_the_definition() {
        on_a_big_stack(|| {
            let (side, module) = fixture("r0c", "eqexists");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let catalog = backend(&side, &module).rule_catalog(None).unwrap();
            let id = |label: &str| {
                catalog
                    .iter()
                    .find(|rule| rule.label.as_deref() == Some(label))
                    .unwrap_or_else(|| panic!("{label}"))
                    .id
                    .clone()
            };
            let mut expected = ["EQEXISTS.go", "EQEXISTS.gy"].map(id).to_vec();
            expected.sort();
            let mut found = exclusions.equals_conditions.clone();
            found.sort();
            assert_eq!(found, expected);
            assert!(!found.contains(&id("EQEXISTS.plain")));
            assert_eq!(
                exclusions.definition_exclusion(),
                Some(Exclusion::EqualsCondition)
            );
        });
    }

    /// Re-pin R0c-fix-1 deliverable 3 (R0c review 1 minor, the reviewer's probe): a definition with a
    /// `stdout` stream cell gets the prelude's stream rules, which apply `#write` (`IO.write`) and
    /// `Float2String`, with their prelude `Source`. The census reads every rewrite rule whatever its
    /// source; R0c-fix-1 flagged the definition (before, the rules' source,
    /// `krust-builtin://domains.md`, hid them). Since KINK-CENSUS-RUNLIST both hooks are on the run
    /// list: k-rust cannot evaluate either in an execute request, and a run that needs one lists it
    /// on `unsupportedHooks`. So the census holds neither, and the definition is not excluded,
    /// though the copied rules are still there (the stdout rules of the compiled definition apply
    /// both hooks).
    #[test]
    #[ignore = "kink"]
    fn prelude_stream_rules_no_longer_flag_a_stream_definition() {
        on_a_big_stack(|| {
            let (side, module) = fixture("r0c", "outs");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert!(
                exclusions.implementation_chosen.is_empty(),
                "{exclusions:?}"
            );
            assert_eq!(exclusions.definition_exclusion(), None);
            let rules = backend(&side, &module).rule_catalog(None).unwrap();
            assert!(
                rules
                    .iter()
                    .any(|rule| rule.label.as_deref() == Some("STDOUT-STREAM.stdoutWrite")),
                "{rules:?}"
            );
        });
    }

    /// KINK-CENSUS-RUNLIST (fz26): the census reads only the open hooks k-rust evaluates without a
    /// run-level record. Fixtures in `testdata/k/runlist` (also run end to end by kink-flow's
    /// `census_runlist` tests):
    /// - `iopw` applies `#write` and `#getc` in right-hand sides: nothing in the census, no
    ///   definition exclusion (before: `IO.getc` and `IO.write`, `implementation-chosen-hook`);
    /// - `lhsio` applies `#getc` in a left-hand-side map key: the same (before: `IO.getc`);
    /// - `iop` (`iopw` with a rule applying `Bytes2String(String2Bytes("ab"))`) and `lhs` (the pair
    ///   in a left-hand-side map key) stay excluded by the bytes pair alone;
    /// - stock SIMPLE (untyped, K's pl-tutorial `simple-untyped.md`, unedited), whose stream cells
    ///   get the prelude's stream rules: no definition exclusion (before: `IO.getc`, `IO.write` and
    ///   `STRING.float2string` in the copied rules).
    #[test]
    #[ignore = "kink"]
    fn the_census_reads_only_open_hooks_k_rust_evaluates_without_a_record() {
        on_a_big_stack(|| {
            let census = |side: &ValidatedDefinition, module: &str| {
                let exclusions = DefinitionExclusions::of_validated(side, module).unwrap();
                let hooks = exclusions
                    .implementation_chosen
                    .iter()
                    .map(|reference| reference.hook.clone())
                    .collect::<BTreeSet<_>>();
                (hooks, exclusions.definition_exclusion())
            };
            let bytes =
                BTreeSet::from(["BYTES.bytes2string", "BYTES.string2bytes"].map(str::to_owned));
            for (name, expected) in [
                ("iopw", BTreeSet::new()),
                ("lhsio", BTreeSet::new()),
                ("iop", bytes.clone()),
                ("lhs", bytes.clone()),
            ] {
                let (side, module) = fixture("runlist", name);
                let (hooks, exclusion) = census(&side, &module);
                assert_eq!(hooks, expected, "{name}");
                assert_eq!(
                    exclusion,
                    (!expected.is_empty()).then_some(Exclusion::ImplementationChosenHook),
                    "{name}"
                );
            }
            let loaded = support::load_path(
                &Path::new(support::DIR).join("runlist/simple-untyped.md"),
                "SIMPLE-UNTYPED",
            );
            let side = NativeValidator::bind(loaded, CompileOptions::default())
                .compile_baseline()
                .unwrap();
            let module = k_rust::kast::identifier::encode("SIMPLE-UNTYPED");
            let (hooks, exclusion) = census(&side, &module);
            assert!(hooks.is_empty(), "{hooks:?}");
            assert_eq!(exclusion, None);
        });
    }
}

/// KINK-PATHSET-FALLBACK (D39), the counterexample of k-rust's merge differential at kink's
/// level (`testdata/k/stateset/remainder.k`; k-rust
/// `a_refuted_remainder_below_a_merged_state_names_the_witness_paths_producing_rule`). The
/// remainder of `pr` below the merged `p(X)` is refuted by its own normalization, so its `Trivial`
/// leaf names the rule that produced `p(X)`: the state set names the witness path's `g1`, the path
/// set `g1` and `g2`. `g2` carries `preserves-definedness`, so the path set's leaf rule reads a
/// contradiction that nothing shows (`g2`'s result is defined); the state set reads none.
///
/// - REMAINDER (no record on the list): the path set is excluded with a leaf contradiction; the
///   state set is not excluded, which is the first-principles answer.
/// - REMAINDER-RECORD (a covered candidate contradicts `tz`'s `total` claim, a record on the list
///   that no leaf carries): both are excluded; only the path set has a leaf contradiction, so
///   kink-campaign keeps a path-set baseline per test and refuses a state-set one (fail-closed).
///
/// A remainder exists only where the solver finds it satisfiable, so the test is Z3-only.
#[cfg(feature = "z3")]
#[test]
fn a_refuted_remainder_below_a_merged_state_is_read_on_the_state_set() {
    use kink_native::execution::{ResultModality, ResultRun};
    on_a_big_stack(|| {
        for (module, record) in [("REMAINDER", false), ("REMAINDER-RECORD", true)] {
            let loaded = support::load_path(
                &Path::new(support::DIR).join("stateset/remainder.k"),
                module,
            );
            let side = NativeValidator::bind(loaded, CompileOptions::default())
                .compile_baseline()
                .unwrap_or_else(|e| panic!("{module}: {e}"));
            let module = k_rust::kast::identifier::encode(module);
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let catalog = backend(&side, &module).rule_catalog(None).unwrap();
            let label = |id: &str| {
                catalog
                    .iter()
                    .find(|rule| rule.id == id)
                    .and_then(|rule| rule.label.clone())
                    .unwrap_or_default()
            };
            let condition = parse_pattern(
                r#"\equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), Lbl'UndsEqlsSlshEqls'Int'Unds'{}(Lblh{}(VarX:SortInt{}), \dv{SortInt{}}("3")))"#,
            )
            .unwrap();
            let state = Pattern::And {
                sort: k_rust::kore::ast::Sort::Application {
                    name: "SortGeneratedTopCell".into(),
                    arguments: Vec::new(),
                },
                arguments: vec![
                    support::initial_state(
                        support::app("Lblx", vec![support::var("VarX", "SortInt")]),
                        "SortProg",
                    ),
                    condition,
                ],
            };
            let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
            let read = |modality| {
                let execution = adapter
                    .execute_result(
                        &mut backend(&side, &module),
                        &state,
                        budget(),
                        ResultRun {
                            modality,
                            max_work: None,
                        },
                    )
                    .unwrap();
                assert_eq!(execution.modality(), modality, "{module}");
                let named = execution
                    .leaves()
                    .iter()
                    .filter(|leaf| leaf.halt == HaltClass::Trivial)
                    .map(|leaf| label(&leaf.undefined_rule.as_ref().expect("names a rule").id))
                    .collect::<Vec<_>>();
                (
                    named,
                    exclusions.contradiction_on_a_leaf(&execution),
                    exclusions.run_exclusion(&execution),
                )
            };
            let excluded = record.then_some(Exclusion::ContradictedClaim);
            assert_eq!(
                read(ResultModality::StateSet),
                (vec!["REMAINDER.g1".to_owned()], false, excluded),
                "{module}"
            );
            assert_eq!(
                read(ResultModality::PathSet),
                (
                    vec!["REMAINDER.g1".to_owned(), "REMAINDER.g2".to_owned()],
                    true,
                    Some(Exclusion::ContradictedClaim)
                ),
                "{module}"
            );
        }
    });
}

/// fz26 KINK-PATHSET-FALLBACK, the soundness guards (`testdata/k/stateset/guards.k`): each leaf
/// kind kink reads, reached by two converging paths, gives the same exclusion and the same leaf
/// contradiction (which admission reads) on the state set as on the path set of the same request,
/// and every state-set leaf without a configuration is one of the path set's.
/// - `two(0)`: one `Trivial` leaf naming the `preserves-definedness` rule `join` (no producing
///   rule) against two; excluded with a leaf contradiction.
/// - `tc(0)`: one `Trivial` leaf with `contradictedTotal` against two; excluded with a leaf
///   contradiction.
/// - `ab(0)`: the record is on an absorbed arrival's prefix only: the state set's one leaf is clean
///   and the run's list holds the record, so the run is excluded with no leaf contradiction, as the
///   path set's, whose leaf of that path carries the record only as a diagnostic.
#[test]
fn a_state_set_with_converging_undefined_leaves_is_excluded_as_its_path_set() {
    use kink_native::execution::{ResultModality, ResultRun};
    on_a_big_stack(|| {
        let (side, module) = fixture("stateset", "guards");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let catalog = backend(&side, &module).rule_catalog(None).unwrap();
        let label = |id: &str| {
            catalog
                .iter()
                .find(|rule| rule.id == id)
                .and_then(|rule| rule.label.clone())
                .unwrap_or_default()
        };
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        for (symbol, leaves, rule, leaf_contradiction) in [
            ("Lbltwo", 1, Some("GUARDS.join"), true),
            ("Lbltc", 1, Some("GUARDS.tmv"), true),
            ("Lblab", 1, None, false),
        ] {
            let state =
                support::initial_state(support::app(symbol, vec![support::int(0)]), "SortProg");
            let read = |modality| {
                adapter
                    .execute_result(
                        &mut backend(&side, &module),
                        &state,
                        budget(),
                        ResultRun {
                            modality,
                            max_work: None,
                        },
                    )
                    .unwrap()
            };
            let (state_set, path_set) = (
                read(ResultModality::StateSet),
                read(ResultModality::PathSet),
            );
            assert_eq!(state_set.modality(), ResultModality::StateSet, "{symbol}");
            assert_eq!(state_set.leaves().len(), leaves, "{symbol}");
            assert_eq!(path_set.leaves().len(), 2 * leaves, "{symbol}");
            for leaf in state_set.leaves() {
                assert_eq!(
                    leaf.undefined_rule
                        .as_ref()
                        .map(|r| label(&r.id))
                        .as_deref(),
                    rule,
                    "{symbol}"
                );
                if leaf.halt == HaltClass::Trivial {
                    assert!(path_set.leaves().contains(leaf), "{symbol}: {leaf:?}");
                }
            }
            for execution in [&state_set, &path_set] {
                assert_eq!(
                    exclusions.contradiction_on_a_leaf(execution),
                    leaf_contradiction,
                    "{symbol} {:?}",
                    execution.modality()
                );
                assert_eq!(
                    exclusions.run_exclusion(execution),
                    Some(Exclusion::ContradictedClaim),
                    "{symbol} {:?}",
                    execution.modality()
                );
                assert!(
                    !execution.facts().contradicted_claims.is_empty(),
                    "{symbol}"
                );
            }
            if symbol == "Lbltc" {
                assert!(state_set.leaves()[0].contradicted_total.is_some());
            }
        }
    });
}

/// fz26 KINK-PATHSET-FALLBACK, the `Vacuous` guard (`testdata/k/stateset/remainder.k` with the
/// initial condition on `g`): a remainder below the merged `p(X)` that its normalization refutes with no
/// undefined term is a `Vacuous` leaf, one in the state set and one per path in the path set; the
/// bridge discards it, and neither run is excluded. Z3-only, as the remainder needs a solver.
#[cfg(feature = "z3")]
#[test]
fn a_vacuous_remainder_below_a_merged_state_excludes_neither_run() {
    use kink_native::execution::{ResultModality, ResultRun};
    on_a_big_stack(|| {
        let loaded = support::load_path(
            &Path::new(support::DIR).join("stateset/remainder.k"),
            "REMAINDER",
        );
        let side = NativeValidator::bind(loaded, CompileOptions::default())
            .compile_baseline()
            .unwrap();
        let module = k_rust::kast::identifier::encode("REMAINDER");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let condition = parse_pattern(
            r#"\equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), Lbl'UndsEqlsSlshEqls'Int'Unds'{}(Lblg{}(VarX:SortInt{}), \dv{SortInt{}}("3")))"#,
        )
        .unwrap();
        let state = Pattern::And {
            sort: k_rust::kore::ast::Sort::Application {
                name: "SortGeneratedTopCell".into(),
                arguments: Vec::new(),
            },
            arguments: vec![
                support::initial_state(
                    support::app("Lblx", vec![support::var("VarX", "SortInt")]),
                    "SortProg",
                ),
                condition,
            ],
        };
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        for (modality, vacuous) in [(ResultModality::StateSet, 1), (ResultModality::PathSet, 2)] {
            let execution = adapter
                .execute_result(
                    &mut backend(&side, &module),
                    &state,
                    budget(),
                    ResultRun {
                        modality,
                        max_work: None,
                    },
                )
                .unwrap();
            assert_eq!(
                execution
                    .leaves()
                    .iter()
                    .filter(|leaf| leaf.halt == HaltClass::Vacuous)
                    .count(),
                vacuous,
                "{modality:?}"
            );
            assert!(!exclusions.contradiction_on_a_leaf(&execution));
            assert_eq!(exclusions.run_exclusion(&execution), None, "{modality:?}");
        }
    });
}

/// A KNOWN GAP, not desired behaviour (KINK-PD-SYMBOLIC-INSTANCE, D40; the KINK-PATHSET-FALLBACK
/// review's probe, `testdata/k/stateset/rpd.k`). `g1` carries `preserves-definedness` but its
/// result is undefined at X = 0. On the symbolic `a(X)` (RPD-LATER) the run reaches that
/// instance only through `pz`'s narrowing, one step later: its leaves are a `Trivial` leaf naming
/// `pz` and a `Stuck` leaf, it carries no contradicted-claim record, no leaf names a
/// `preserves-definedness` rule, and so it is not excluded, though g1's claim is false on an
/// instance it reaches. On the ground `a(0)` (RPD-GROUND) g1's own step shows the `\bottom`, and
/// the record excludes the run. Both readings are the same in either modality, so the gap does
/// not depend on the state set. This test pins today's behaviour so that a fix (k-rust recording
/// the contradiction, or kink deciding it) shows up here; it is a gap to close, not a guarantee.
/// Z3-only: the `Stuck` remainder needs a solver.
#[cfg(feature = "z3")]
#[test]
fn known_gap_a_pd_claim_false_at_a_narrowed_symbolic_instance_is_not_excluded() {
    use kink_native::execution::{ResultModality, ResultRun};
    on_a_big_stack(|| {
        for (module, argument, excluded) in [
            ("RPD-LATER", support::var("VarX", "SortInt"), None),
            (
                "RPD-GROUND",
                support::int(0),
                Some(Exclusion::ContradictedClaim),
            ),
        ] {
            let loaded =
                support::load_path(&Path::new(support::DIR).join("stateset/rpd.k"), module);
            let side = NativeValidator::bind(loaded, CompileOptions::default())
                .compile_baseline()
                .unwrap_or_else(|e| panic!("{module}: {e}"));
            let encoded = k_rust::kast::identifier::encode(module);
            let exclusions = DefinitionExclusions::of_validated(&side, &encoded).unwrap();
            let catalog = backend(&side, &encoded).rule_catalog(None).unwrap();
            let label = |id: &str| {
                catalog
                    .iter()
                    .find(|rule| rule.id == id)
                    .and_then(|rule| rule.label.clone())
                    .unwrap_or_default()
            };
            let state =
                support::initial_state(support::app("Lbla", vec![argument.clone()]), "SortProg");
            let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
            let read = |modality| {
                let execution = adapter
                    .execute_result(
                        &mut backend(&side, &encoded),
                        &state,
                        budget(),
                        ResultRun {
                            modality,
                            max_work: None,
                        },
                    )
                    .unwrap();
                let mut leaves = execution
                    .leaves()
                    .iter()
                    .map(|leaf| {
                        (
                            leaf.halt,
                            leaf.undefined_rule.as_ref().map(|rule| label(&rule.id)),
                        )
                    })
                    .collect::<Vec<_>>();
                leaves.sort_by_key(|(halt, _)| format!("{halt:?}"));
                (
                    leaves,
                    execution.facts().contradicted_claims.len(),
                    exclusions.contradiction_on_a_leaf(&execution),
                    exclusions.run_exclusion(&execution),
                )
            };
            let state_set = read(ResultModality::StateSet);
            assert_eq!(state_set, read(ResultModality::PathSet), "{module}");
            assert_eq!(state_set.3, excluded, "{module}: {state_set:?}");
            if module == "RPD-LATER" {
                assert_eq!(
                    state_set,
                    (
                        vec![
                            (HaltClass::Stuck, None),
                            (HaltClass::Trivial, Some("RPD-LATER.pz".to_owned())),
                        ],
                        0,
                        false,
                        None
                    ),
                    "{module}"
                );
            } else {
                assert!(state_set.1 > 0, "{module}: the record");
            }
        }
    });
}
