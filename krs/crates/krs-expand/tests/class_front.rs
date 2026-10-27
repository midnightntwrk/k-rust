//! The fast tier of the class tests: every generated case (`krs_test_support::class_matrix`)
//! expanded in-process by [`whole_file::expand_file`], the expansion the proc macros perform.
//!
//! - **K2 at the front.** A case the front refuses is judged by the five table-free invariants
//!   (`class_matrix::invariants`), and by `expected.toml` where a rule covers it: an accepted
//!   case must not be refused, and a refused one must answer with its class's code, exactly
//!   located inside the rule's range. A case the front accepts is decided after rustc, by the
//!   full tier (`krs-class`); here it conforms. So is a case at a position rustc parses that the
//!   front refuses with the Rust parse error rustc also reports there (`krs::expand::parse` at
//!   the construct): the front ran no macro, so KRS's own answer is the full tier's to judge
//!   (`class_matrix::invariants`, "Positions rustc parses").
//! - **K1 on payload forms.** For every descriptor factory the front writes, an initializer's
//!   payload function included: each key its payload names has exactly one anchor in the
//!   factory's own `__KRS_AUTHORED` table, no two anchors share a key, every anchor is exact, and
//!   every anchor lies inside the invocation that wrote it. A key is injective on authored nodes,
//!   not on payload fields: several fields may name one node (an application's `reference.key`
//!   and `path_key`, a declaration's key and its owner's). An anchor without a payload key (a
//!   declaration's) is not a defect; whether every anchor is used, and whether the semantic keys
//!   lowering derives are injective, is checked on the collected bundle, in the full tier.
//!
//! A case that deviates passes only when `pending.toml` records it with the same deviation (the
//! PENDING rules, `class_matrix::pending`). A pending case that the front accepts with sound keys
//! was recorded by the full tier and is left to it.
//!
//! Every case must be covered by the table ([`UNCOVERED_IS_TABLE_ERROR`]).
//!
//! The cases run on every available thread: `proc_macro2`'s fallback spans are per thread, and
//! each thread drops its spans after every case. The generator caps the number of cases
//! ([`class_matrix::FRONT_CASE_CAP`]); no time is asserted.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::ops::Range;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use krs_diagnostic::{Code, untag_rustc_message};
use krs_expand::sink::{ByteRange, InvocationId, MappingClass};
use krs_expand::whole_file::{self, ExpandDiagnostic, FileExpansion, FileRequest, Selection};
use krs_ir::ProvenanceRole;
use krs_test_support::class_matrix::invariants::{
    Observed, ObservedDiagnostic, Severity, front_stops_at_rustc_parse, registry_kind, signature,
    violations,
};
use krs_test_support::class_matrix::pending::{Judgement, Observation, Pending, UNASSIGNED};
use krs_test_support::class_matrix::table::{Expected, Table, TableError};
use krs_test_support::class_matrix::{self, Base, Placed};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use serde_json::Value;

/// Whether a case that no entry of `expected.toml` covers fails the suite: the table covers
/// every generated case, so a new case needs its entry.
const UNCOVERED_IS_TABLE_ERROR: bool = true;

fn expand(source: &str) -> Result<FileExpansion, Vec<ExpandDiagnostic>> {
    let module_path = vec!["krs_class_case".to_owned()];
    whole_file::expand_file(&FileRequest {
        display_file: "src/lib.rs",
        source,
        generated_file: "/work/expanded/class-case/src/lib.rs",
        facade_alias: "k",
        facade_path: syn::parse_str("::k").expect("the facade path parses"),
        module_path: &module_path,
        selection: &Selection::WholeFile,
    })
}

fn read_class_matrix(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn range(range: ByteRange) -> Range<usize> {
    range.start()..range.end()
}

/// What the front did with one case.
struct Front {
    /// The front's verdict and diagnostics. An expansion that succeeds but writes a
    /// `compile_error!` is refused: rustc reports that error before anything else runs. A
    /// panicking expansion is refused with its panic.
    observed: Observed,
    /// Whether every error is exactly located (`MappingClass::ExactAuthored`).
    exact: bool,
    /// K1 over the accepted expansion's descriptor factories.
    keys: KeyCheck,
}

/// What K1 saw in one expansion.
#[derive(Default)]
struct KeyCheck {
    /// The defects, as signature parts.
    defects: Vec<String>,
    /// The case's own descriptor factories, their payload keys, and their anchors.
    factories: usize,
    payload_keys: usize,
    anchors: usize,
}

fn run_front(placed: &Placed<'_>, source: &str) -> Front {
    let expanded = std::panic::catch_unwind(|| expand(source));
    match expanded {
        Err(panic) => Front {
            exact: false,
            observed: Observed {
                accepted: false,
                diagnostics: Vec::new(),
                panic: Some(
                    panic
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
                        .unwrap_or_else(|| "a panic without a message".to_owned()),
                ),
            },
            keys: KeyCheck::default(),
        },
        Ok(Err(diagnostics)) => Front {
            exact: diagnostics
                .iter()
                .all(|diagnostic| diagnostic.class == MappingClass::ExactAuthored),
            observed: Observed {
                accepted: false,
                diagnostics: diagnostics
                    .into_iter()
                    .map(|diagnostic| ObservedDiagnostic {
                        severity: Severity::Error,
                        code: Some(diagnostic.code.to_string()),
                        kind: Some(diagnostic.code.kind()),
                        range: diagnostic.authored.map(range),
                        labels: Vec::new(),
                        message: diagnostic.message,
                    })
                    .collect(),
                panic: None,
            },
            keys: KeyCheck::default(),
        },
        Ok(Ok(expansion)) => {
            let written = written_errors(&expansion);
            let keys = keys(&expansion, source, placed);
            Front {
                exact: written.iter().all(|(_, exact)| *exact),
                observed: Observed {
                    accepted: written.is_empty(),
                    diagnostics: written.into_iter().map(|(error, _)| error).collect(),
                    panic: None,
                },
                keys,
            }
        }
    }
}

/// The root invocation of every invocation: the outermost one whose expansion contains it.
fn roots(expansion: &FileExpansion) -> Vec<InvocationId> {
    let invocations = &expansion.generated.map.invocations;
    invocations
        .iter()
        .map(|invocation| {
            let mut root = invocation;
            while let Some(parent) = root.parent {
                root = &invocations[parent.0];
            }
            root.id
        })
        .collect()
}

/// The `compile_error!`s a successful expansion writes, each with whether it is exactly
/// located: at its own authored tokens, or else at its invocation's call site.
fn written_errors(expansion: &FileExpansion) -> Vec<(ObservedDiagnostic, bool)> {
    let mut errors = Vec::new();
    for output in &expansion.expansions {
        let call_site = expansion.generated.map.invocations[output.id.0].call_site;
        let mut found = Vec::new();
        compile_errors(&output.output, &mut found);
        for (message, span) in found {
            let exact = expansion.authored.byte_range(span);
            let (code, message) = match untag_rustc_message(&message) {
                Some((code, rest)) => (Some(code), rest.to_owned()),
                None => (None, message),
            };
            errors.push((
                ObservedDiagnostic {
                    severity: Severity::Error,
                    kind: code.as_ref().map(Code::kind),
                    code: code.as_ref().map(Code::to_string),
                    range: Some(range(exact.unwrap_or(call_site))),
                    labels: Vec::new(),
                    message,
                },
                exact.is_some(),
            ));
        }
    }
    errors
}

/// Every `compile_error!("…")` in `stream`: its message and the span of the message literal.
fn compile_errors(stream: &TokenStream, found: &mut Vec<(String, proc_macro2::Span)>) {
    let trees = stream.clone().into_iter().collect::<Vec<_>>();
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Ident(ident) if ident == "compile_error" => {
                if let (Some(TokenTree::Punct(bang)), Some(TokenTree::Group(group))) =
                    (trees.get(index + 1), trees.get(index + 2))
                    && bang.as_char() == '!'
                    && let Some(TokenTree::Literal(literal)) = group.stream().into_iter().next()
                {
                    found.push((string_literal(&literal), literal.span()));
                }
            }
            TokenTree::Group(group) => compile_errors(&group.stream(), found),
            _ => {}
        }
    }
}

fn string_literal(literal: &proc_macro2::Literal) -> String {
    syn::parse2::<syn::LitStr>(TokenTree::Literal(literal.clone()).into())
        .expect("a generated string literal parses")
        .value()
}

/// One provenance key, its role spelled as in a payload.
type Key = (&'static str, u32);

/// One anchor of a factory's `__KRS_AUTHORED` table.
struct Anchor {
    key: Key,
    /// 1-based line and column of the start and the end, as the provenance records them.
    start: (usize, usize),
    end: (usize, usize),
    exact: bool,
}

/// One descriptor factory of an expansion.
#[derive(Default)]
struct Factory {
    name: String,
    /// The payload JSON strings (`__krs_host_payload`, `__krs_fixed_configuration`).
    payloads: Vec<String>,
    anchors: Vec<Anchor>,
}

/// K1 over every factory the expansion writes, in the case's invocations and in the base's
/// alike: a factory's anchors must lie inside the outermost invocation that wrote it.
fn keys(expansion: &FileExpansion, source: &str, placed: &Placed<'_>) -> KeyCheck {
    let roots = roots(expansion);
    let lines = LineIndex::new(source);
    let mut keys = KeyCheck::default();
    let mut defects = BTreeSet::new();
    for output in &expansion.expansions {
        let root = &expansion.generated.map.invocations[roots[output.id.0].0];
        let inside = range(root.replaced);
        let owner = if placed.item.start <= inside.start && inside.end <= placed.item.end {
            "case"
        } else {
            "base"
        };
        let mut factories = Vec::new();
        factories_in(&output.output, &mut factories);
        for factory in &factories {
            let (defects_of, payload_keys) = factory_defects(factory, &lines, &inside);
            for defect in defects_of {
                defects.insert(format!("K1 {owner} {}: {defect}", factory.name));
            }
            if owner == "case" {
                keys.factories += 1;
                keys.payload_keys += payload_keys;
                keys.anchors += factory.anchors.len();
            }
        }
    }
    keys.defects = defects.into_iter().collect();
    keys
}

/// The K1 defects of one factory, and the number of distinct keys its payloads hold.
fn factory_defects(
    factory: &Factory,
    lines: &LineIndex,
    inside: &Range<usize>,
) -> (Vec<String>, usize) {
    let mut defects = Vec::new();
    let mut payload_keys = BTreeSet::<Key>::new();
    for payload in &factory.payloads {
        match serde_json::from_str::<Value>(payload) {
            Ok(json) => payload_keys_of(&json, &mut payload_keys, &mut defects),
            Err(error) => defects.push(format!("the payload is not JSON: {error}")),
        }
    }
    let mut anchors = BTreeMap::<Key, usize>::new();
    for anchor in &factory.anchors {
        *anchors.entry(anchor.key).or_default() += 1;
        let (role, ordinal) = anchor.key;
        if !anchor.exact {
            defects.push(format!("the anchor {role} {ordinal} is not exact"));
        }
        match (lines.offset(anchor.start), lines.offset(anchor.end)) {
            (Some(start), Some(end)) if inside.start <= start && end <= inside.end => {}
            (start, end) => defects.push(format!(
                "the anchor {role} {ordinal} at {start:?}..{end:?} lies outside its invocation"
            )),
        }
    }
    for (&(role, ordinal), &count) in &anchors {
        if count > 1 {
            defects.push(format!("{count} anchors share the key {role} {ordinal}"));
        }
    }
    for &(role, ordinal) in &payload_keys {
        if !anchors.contains_key(&(role, ordinal)) {
            defects.push(format!("the payload key {role} {ordinal} has no anchor"));
        }
    }
    (defects, payload_keys.len())
}

/// Collects the provenance keys of a payload: the objects that are exactly `{role, ordinal}`.
/// Several fields may name one authored node (an application's `reference.key` and its
/// `path_key`, a declaration's own key and its owner's), so a key may occur more than once.
fn payload_keys_of(json: &Value, keys: &mut BTreeSet<Key>, defects: &mut Vec<String>) {
    match json {
        Value::Object(object) => {
            if object.len() == 2
                && let (Some(Value::String(role)), Some(Value::Number(ordinal))) =
                    (object.get("role"), object.get("ordinal"))
            {
                match (
                    ProvenanceRole::from_spelling(role),
                    ordinal
                        .as_u64()
                        .and_then(|ordinal| u32::try_from(ordinal).ok()),
                ) {
                    (Some(role), Some(ordinal)) => {
                        keys.insert((role.as_str(), ordinal));
                    }
                    _ => defects.push(format!("the payload key {role} {ordinal} is malformed")),
                }
                return;
            }
            for value in object.values() {
                payload_keys_of(value, keys, defects);
            }
        }
        Value::Array(values) => {
            for value in values {
                payload_keys_of(value, keys, defects);
            }
        }
        _ => {}
    }
}

/// Collects the descriptor factories of `stream`: every `fn NAME(..) .. { body }` whose body,
/// outside the functions nested in it, holds a payload or an anchor table.
fn factories_in(stream: &TokenStream, factories: &mut Vec<Factory>) {
    let trees = stream.clone().into_iter().collect::<Vec<_>>();
    let mut index = 0;
    while index < trees.len() {
        if let Some((name, body)) = function_at(&trees, index) {
            let TokenTree::Group(group) = &trees[body] else {
                unreachable!("a function's body is a group");
            };
            let mut factory = Factory {
                name,
                ..Factory::default()
            };
            factory_parts(group, &mut factory, factories);
            if !factory.payloads.is_empty() || !factory.anchors.is_empty() {
                factories.push(factory);
            }
            index = body + 1;
            continue;
        }
        if let TokenTree::Group(group) = &trees[index] {
            factories_in(&group.stream(), factories);
        }
        index += 1;
    }
}

/// The name of the function whose `fn` keyword is `trees[index]`, and the index of its body.
fn function_at(trees: &[TokenTree], index: usize) -> Option<(String, usize)> {
    let (TokenTree::Ident(keyword), Some(TokenTree::Ident(name))) =
        (&trees[index], trees.get(index + 1))
    else {
        return None;
    };
    if keyword != "fn" {
        return None;
    }
    let body = trees[index + 2..].iter().position(
        |tree| matches!(tree, TokenTree::Group(group) if group.delimiter() == Delimiter::Brace),
    )?;
    Some((name.to_string(), index + 2 + body))
}

/// Collects the payloads and anchors of one factory body; a function nested in it is a factory
/// of its own. A payload is the JSON string argument of `__krs_host_payload` or
/// `__krs_fixed_configuration`, or the first element of the `(wire, slots, provenance)` triple
/// an initializer's payload function returns.
fn factory_parts(body: &proc_macro2::Group, factory: &mut Factory, factories: &mut Vec<Factory>) {
    let trees = body.stream().into_iter().collect::<Vec<_>>();
    let mut index = 0;
    while index < trees.len() {
        if let Some((_, nested)) = function_at(&trees, index) {
            factories_in(&trees[index..=nested].iter().cloned().collect(), factories);
            index = nested + 1;
            continue;
        }
        match &trees[index] {
            TokenTree::Ident(ident)
                if ident == "__krs_host_payload" || ident == "__krs_fixed_configuration" =>
            {
                if let Some(TokenTree::Group(arguments)) = trees.get(index + 1)
                    && let Some(TokenTree::Literal(json)) = arguments.stream().into_iter().next()
                {
                    factory.payloads.push(string_literal(&json));
                }
            }
            TokenTree::Ident(ident) if ident == "Ok" => {
                if let Some(TokenTree::Group(arguments)) = trees.get(index + 1)
                    && let Some(TokenTree::Group(triple)) = arguments.stream().into_iter().next()
                    && triple.delimiter() == Delimiter::Parenthesis
                    && let Some(TokenTree::Literal(json)) = triple.stream().into_iter().next()
                {
                    factory.payloads.push(string_literal(&json));
                }
            }
            TokenTree::Ident(ident) if ident == "__KRS_AUTHORED" => {
                // `__KRS_AUTHORED: TYPE = &[(ROLE, ORDINAL, ANCHOR), ..]`: the table is the
                // bracket group after the `=`.
                if let Some(TokenTree::Group(table)) = trees[index..]
                    .iter()
                    .skip_while(|tree| !matches!(tree, TokenTree::Punct(punct) if punct.as_char() == '='))
                    .find(|tree| matches!(tree, TokenTree::Group(group) if group.delimiter() == Delimiter::Bracket))
                {
                    for entry in table.stream() {
                        if let TokenTree::Group(entry) = entry {
                            factory.anchors.push(anchor(&entry.stream()));
                        }
                    }
                }
            }
            _ => {}
        }
        if let TokenTree::Group(group) = &trees[index] {
            factory_parts(group, factory, factories);
        }
        index += 1;
    }
}

/// One `(facade::ProvenanceRole::Role, ORDINAL, facade::__KrsRawAnchor::new(FILE, ABSOLUTE,
/// (LINE, COLUMN), (LINE, COLUMN), EXACT))` entry.
fn anchor(entry: &TokenStream) -> Anchor {
    let fields = split_commas(entry);
    let [role, ordinal, raw] = fields.as_slice() else {
        panic!("an anchor entry has three fields: {entry}");
    };
    let variant = match role.last() {
        Some(TokenTree::Ident(ident)) => ident.to_string(),
        _ => panic!("an anchor's role is a path: {entry}"),
    };
    let role = ProvenanceRole::ALL
        .iter()
        .find(|role| role.variant_ident() == variant)
        .unwrap_or_else(|| panic!("{variant} is a provenance role"))
        .as_str();
    let ordinal = number(&ordinal[0]);
    let Some(TokenTree::Group(arguments)) = raw.last() else {
        panic!("an anchor ends with its constructor's arguments: {entry}");
    };
    let arguments = split_commas(&arguments.stream());
    let position = |field: &[TokenTree]| -> (usize, usize) {
        let [TokenTree::Group(pair)] = field else {
            panic!("an anchor position is a pair: {entry}");
        };
        let pair = split_commas(&pair.stream());
        (number(&pair[0][0]), number(&pair[1][0]))
    };
    Anchor {
        key: (role, u32::try_from(ordinal).expect("an ordinal is a u32")),
        start: position(&arguments[2]),
        end: position(&arguments[3]),
        exact: matches!(&arguments[4][..], [TokenTree::Ident(exact)] if exact == "true"),
    }
}

fn split_commas(stream: &TokenStream) -> Vec<Vec<TokenTree>> {
    let mut fields = vec![Vec::new()];
    for tree in stream.clone() {
        match &tree {
            TokenTree::Punct(punct) if punct.as_char() == ',' => fields.push(Vec::new()),
            _ => fields.last_mut().expect("a field is open").push(tree),
        }
    }
    if fields.last().is_some_and(Vec::is_empty) {
        fields.pop();
    }
    fields
}

/// An integer literal, without its suffix.
fn number(tree: &TokenTree) -> usize {
    let TokenTree::Literal(literal) = tree else {
        panic!("{tree} is an integer literal");
    };
    let text = literal.to_string();
    let digits = text
        .find(|character: char| !character.is_ascii_digit())
        .map_or(text.as_str(), |end| &text[..end]);
    digits
        .parse()
        .unwrap_or_else(|error| panic!("{text} is an integer literal: {error}"))
}

/// Byte offsets of 1-based lines and columns (`char` columns, plus one, as the whole-file
/// expander records them).
struct LineIndex<'a> {
    source: &'a str,
    starts: Vec<usize>,
}

impl<'a> LineIndex<'a> {
    fn new(source: &'a str) -> Self {
        let starts = std::iter::once(0)
            .chain(source.match_indices('\n').map(|(index, _)| index + 1))
            .collect();
        Self { source, starts }
    }

    fn offset(&self, (line, column): (usize, usize)) -> Option<usize> {
        let start = *self.starts.get(line.checked_sub(1)?)?;
        let text = &self.source[start..];
        let chars = column.checked_sub(1)?;
        match text.char_indices().nth(chars) {
            Some((index, _)) => Some(start + index),
            None => (text.chars().count() == chars).then_some(self.source.len()),
        }
    }
}

/// The test a deviation belongs to.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Test {
    K1,
    K2Front,
}

impl Test {
    const fn name(self) -> &'static str {
        match self {
            Self::K1 => "K1",
            Self::K2Front => "K2 front",
        }
    }
}

/// One case's verdict in this tier.
enum Verdict {
    /// The front accepted the case with sound keys, or stopped at rustc's parse error at a
    /// position rustc parses: the full tier decides it.
    Deferred,
    Conforms,
    Deviates(Test, String),
}

/// The front's verdict against the invariants and the table.
fn judge(placed: &Placed<'_>, front: &Front, expected: Option<&Expected<'_>>) -> Verdict {
    if !front.observed.refused() {
        return if front.keys.defects.is_empty() {
            Verdict::Deferred
        } else {
            Verdict::Deviates(Test::K1, front.keys.defects.join("; "))
        };
    }
    if front_stops_at_rustc_parse(&front.observed, placed) {
        return Verdict::Deferred;
    }
    let site = expected.map_or(&placed.entry, |expected| expected.site(placed));
    let broken = !violations(&front.observed, site, registry_kind).is_empty();
    let off_table = match expected {
        None => false,
        Some(Expected::Accept(_)) => true,
        Some(Expected::Refuse { rule, class }) => {
            let site = rule.at.range(placed);
            let first = front.observed.errors().next();
            !(front.exact
                && first.and_then(|error| error.code.as_deref()) == Some(class.code.as_str())
                && first.is_some_and(|error| error.located_inside(site)))
        }
    };
    if broken || off_table {
        Verdict::Deviates(Test::K2Front, signature(&front.observed, placed))
    } else {
        Verdict::Conforms
    }
}

/// One case's outcome in this tier.
struct Ran {
    refused: bool,
    /// The case's own factories, payload keys, and anchors that K1 checked.
    keyed: [usize; 3],
    verdict: Verdict,
}

/// Runs every case through the front on every available thread, in case order, and returns the
/// outcomes and the number of threads.
fn run_cases(
    cases: &[class_matrix::Case],
    expected: &BTreeMap<String, Expected<'_>>,
) -> (Vec<Ran>, usize) {
    let threads = std::thread::available_parallelism().map_or(1, usize::from);
    let next = AtomicUsize::new(0);
    let mut ran = std::thread::scope(|scope| {
        let workers = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some(case) = cases.get(index) else {
                            break;
                        };
                        let rendered = case.render();
                        let placed = &rendered.cases[0];
                        let front = run_front(placed, &rendered.source);
                        let verdict = judge(placed, &front, expected.get(&case.id));
                        proc_macro2::extra::invalidate_current_thread_spans();
                        let keyed = [
                            front.keys.factories,
                            front.keys.payload_keys,
                            front.keys.anchors,
                        ];
                        done.push((
                            index,
                            Ran {
                                refused: front.observed.refused(),
                                keyed,
                                verdict,
                            },
                        ));
                    }
                    done
                })
            })
            .collect::<Vec<_>>();
        workers
            .into_iter()
            .flat_map(|worker| worker.join().expect("a front worker panicked"))
            .collect::<Vec<_>>()
    });
    ran.sort_by_key(|(index, _)| *index);
    (ran.into_iter().map(|(_, ran)| ran).collect(), threads)
}

/// The failures, and the `pending.toml` entries that would record their new deviations.
fn failure_message(failures: &[(&str, Option<Test>, Judgement)]) -> String {
    let mut message = format!("{} class-test cases fail at the front:\n", failures.len());
    for (id, test, judgement) in failures {
        writeln!(
            message,
            "  {id} ({}): {judgement}",
            test.map_or("conforms", Test::name)
        )
        .expect("writing to a String");
    }
    message.push_str("\nTo record the new deviations in pending.toml:\n\n");
    for (id, _, judgement) in failures {
        if let Judgement::Unexpected { observed } | Judgement::DeviationChanged { observed, .. } =
            judgement
        {
            writeln!(
                message,
                "[{id:?}]\nfinding = \"{UNASSIGNED}\"\ndeviation = {observed:?}\n"
            )
            .expect("writing to a String");
        }
    }
    message
}

#[test]
fn every_case_meets_the_front_invariants_and_keys_its_payloads() {
    let started = Instant::now();
    let table = Table::parse(&read_class_matrix("expected.toml"))
        .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let pending = Pending::parse(&read_class_matrix("pending.toml"))
        .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let ids = cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    let resolution = table.resolve(&ids, registry_kind);
    let mut table_errors = resolution
        .errors
        .iter()
        .filter(|error| UNCOVERED_IS_TABLE_ERROR || !matches!(error, TableError::Uncovered { .. }))
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let uncovered = resolution
        .errors
        .iter()
        .filter(|error| matches!(error, TableError::Uncovered { .. }))
        .count();

    let (ran, threads) = run_cases(&cases, &resolution.expected);
    let elapsed = started.elapsed();
    assert!(
        ran.iter().any(|ran| ran.keyed[1] > 0),
        "K1 found no payload key: the factory scan reads nothing"
    );

    let mut refused = 0;
    let mut keyed = [0; 3];
    let mut deferred_pending = 0;
    let mut red = Vec::new();
    let mut red_by_test = BTreeMap::<(&str, &str), usize>::new();
    let mut failures = Vec::new();
    for (case, ran) in cases.iter().zip(&ran) {
        refused += usize::from(ran.refused);
        for (total, count) in keyed.iter_mut().zip(ran.keyed) {
            *total += count;
        }
        let (test, observation) = match &ran.verdict {
            Verdict::Deferred => {
                deferred_pending += usize::from(pending.entries.contains_key(&case.id));
                continue;
            }
            Verdict::Conforms => (None, Observation::Conforms),
            Verdict::Deviates(test, signature) => (Some(*test), Observation::Deviates(signature)),
        };
        match pending.judge(&case.id, observation) {
            Judgement::Conforms => {}
            Judgement::Red => {
                red.push(case.id.as_str());
                *red_by_test
                    .entry((test.map_or("", Test::name), case.family.name()))
                    .or_default() += 1;
            }
            judgement => failures.push((case.id.as_str(), test, judgement)),
        }
    }

    let tally = pending.tally(red.iter().copied());
    let mut report = format!(
        "class front: {} cases on {threads} threads in {:.2} s: {} accepted at the front, \
         {refused} refused; {uncovered} not covered by expected.toml; {} red as pending.toml \
         records; {deferred_pending} pending cases accepted at the front, left to krs-class; \
         K1 over {} case factories, {} payload keys, {} anchors\n",
        cases.len(),
        elapsed.as_secs_f64(),
        cases.len() - refused,
        red.len(),
        keyed[0],
        keyed[1],
        keyed[2],
    );
    for ((test, family), count) in &red_by_test {
        writeln!(report, "  red {test} {family}: {count}").expect("writing to a String");
    }
    for (finding, count) in &tally.by_finding {
        writeln!(report, "  red by finding {finding}: {count}").expect("writing to a String");
    }
    for (step, count) in &tally.by_step {
        writeln!(report, "  red by step {step}: {count}").expect("writing to a String");
    }
    eprint!("{report}");

    if !failures.is_empty() {
        table_errors.push(failure_message(&failures));
    }
    assert!(table_errors.is_empty(), "{}", table_errors.join("\n"));
}

#[test]
fn every_base_keys_its_payloads() {
    for base in Base::ALL {
        let source = base.preamble();
        let expansion = expand(&source)
            .unwrap_or_else(|diagnostics| panic!("the {base:?} base expands: {diagnostics:#?}"));
        let roots = roots(&expansion);
        let lines = LineIndex::new(&source);
        let mut factories_seen = 0;
        let mut defects = Vec::new();
        for output in &expansion.expansions {
            let root = &expansion.generated.map.invocations[roots[output.id.0].0];
            let mut factories = Vec::new();
            factories_in(&output.output, &mut factories);
            factories_seen += factories.len();
            for factory in &factories {
                for defect in factory_defects(factory, &lines, &range(root.replaced)).0 {
                    defects.push(format!("{}: {defect}", factory.name));
                }
            }
        }
        proc_macro2::extra::invalidate_current_thread_spans();
        assert!(
            factories_seen > 0,
            "the {base:?} base writes descriptor factories"
        );
        assert!(defects.is_empty(), "the {base:?} base: {defects:#?}");
    }
}

#[test]
fn k1_reports_each_defect_of_a_factory() {
    let source = "abcdefgh\nijklmnop\n";
    let anchor = |role: &str, line: u32, exact: bool| {
        format!(
            "(::k::ProvenanceRole::{role}, 0u32, ::k::__KrsRawAnchor::new(0usize, false, \
             ({line}u32, 1u32), ({line}u32, 3u32), {exact}))"
        )
    };
    let payload = r#""{\"pattern_key\":{\"role\":\"rule_pattern\",\"ordinal\":0},\"result_key\":{\"role\":\"rule_result\",\"ordinal\":0},\"again\":{\"role\":\"rule_pattern\",\"ordinal\":0}}""#;
    let stream = format!(
        "fn __krs_factory() -> Result {{ fn nested() {{}} let payload = \
         ::k::__krs_host_payload({payload}, slots); \
         const __KRS_AUTHORED: &[()] = &[{}, {}]; }}",
        anchor("RulePattern", 1, true),
        anchor("RulePattern", 2, false),
    )
    .parse::<TokenStream>()
    .expect("the factory lexes");
    let mut factories = Vec::new();
    factories_in(&stream, &mut factories);
    proc_macro2::extra::invalidate_current_thread_spans();
    let [factory] = factories.as_slice() else {
        panic!("one factory is found");
    };
    assert_eq!(factory.name, "__krs_factory");
    let (mut defects, payload_keys) = factory_defects(factory, &LineIndex::new(source), &(0..8));
    defects.sort();
    assert_eq!(payload_keys, 2, "a key named twice is one key");
    assert_eq!(
        defects,
        [
            "2 anchors share the key rule_pattern 0",
            "the anchor rule_pattern 0 at Some(9)..Some(11) lies outside its invocation",
            "the anchor rule_pattern 0 is not exact",
            "the payload key rule_result 0 has no anchor",
        ]
    );
}

#[test]
fn the_table_decides_a_front_refusal_by_code_class_and_site() {
    let table = Table::parse(
        r#"
[class.claim-only]
code = "krs::expand::claim-only-term"
doc = "`k::or_bool!` outside a claim"

[class.other]
code = "krs::analysis::invalid-term"
doc = "another mistake"

[class.local-rewrite]
code = "krs::syntax::invalid-local-rewrite"
doc = "a predicate in a local rule's subject"

[[refuse]]
match = "terms/{init,equation}/{item,guard}/k::or_bool!(true, false)"
class = "claim-only"
at = "spelling"

[[refuse]]
match = "terms/init/item-depth-2/k::or_bool!(true, false)"
class = "other"
at = "spelling"

[[refuse]]
match = "terms/local-rule/subject/k::ml::exists(|v: Int| k::ml::equals(v, 0))"
class = "local-rewrite"
at = "spelling"

[accept."terms/init/item/1"]
k = ""
"#,
    )
    .unwrap_or_else(|errors| panic!("{errors:#?}"));
    let cases = class_matrix::cases();
    let ids = cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    let resolution = table.resolve(&ids, registry_kind);
    let verdict = |id: &str| {
        let case = cases
            .iter()
            .find(|case| case.id == id)
            .unwrap_or_else(|| panic!("{id} is generated"));
        let rendered = case.render();
        let front = run_front(&rendered.cases[0], &rendered.source);
        let verdict = judge(&rendered.cases[0], &front, resolution.expected.get(id));
        proc_macro2::extra::invalidate_current_thread_spans();
        match verdict {
            Verdict::Deferred => "deferred".to_owned(),
            Verdict::Conforms => "conforms".to_owned(),
            Verdict::Deviates(test, signature) => format!("{}: {signature}", test.name()),
        }
    };
    // Exactly located inside the spelling, with the class's code.
    for id in [
        "terms/init/item/k::or_bool!(true, false)",
        "terms/equation/guard/k::or_bool!(true, false)",
    ] {
        assert_eq!(verdict(id), "conforms", "{id}");
    }
    // The class's code, but outside the spelling.
    assert_eq!(
        verdict("terms/local-rule/subject/k::ml::exists(|v: Int| k::ml::equals(v, 0))"),
        "K2 front: krs::syntax::invalid-local-rewrite @ item"
    );
    // Located, but with another class's code.
    assert_eq!(
        verdict("terms/init/item-depth-2/k::or_bool!(true, false)"),
        "K2 front: krs::expand::claim-only-term @ spelling"
    );
    // Accepted at the front: decided after rustc.
    assert_eq!(verdict("terms/init/item/1"), "deferred");
}
