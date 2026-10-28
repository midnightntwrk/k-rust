//! The position table (`krs_syntax::positions`) against the class tests' spec: the product's
//! classes are those of `krs/tests/class-matrix/expected.toml`, with the same codes; the
//! oracle's (`class_matrix::oracle`) are too, and cover the product's; and the product's table,
//! written per position, decides every generated term case as the oracle, written per
//! construct, does, from the case's own position and nodes. The cases on which the two disagree
//! are exactly the known findings ([`KNOWN`]), each on the red list (`pending.toml`) under its
//! finding, so the spec and the product cannot drift apart silently.
//!
//! The coverage tests: every form of the product's table has a generated position, every slot of
//! every form its root and an argument, and every construct of the table and every notation form
//! of `krs_syntax::notation` a spelling, apart from the listed exceptions with their reasons.

use std::collections::BTreeSet;
use std::path::Path;

use krs_ir::BuiltinOperator;
use krs_syntax::positions::{
    self as product_table, Admission, Class, Construct, Form, Nesting, Position, RootConstruct,
    Rule, Slot, admits,
};
use krs_test_support::class_matrix::invariants::registry_kind;
use krs_test_support::class_matrix::oracle::{self, Stage};
use krs_test_support::class_matrix::pending::Pending;
use krs_test_support::class_matrix::positions::{
    self as model, Entry, Kind, LocalPattern, Notation, Opening, PatternRoot, RewriteSide,
};
use krs_test_support::class_matrix::table::{Glob, TERM_ACCEPTS_FILE, Table};
use krs_test_support::class_matrix::{self, Case, Family};

/// The cases on which the product's table and the oracle disagree, as globs over case IDs, and
/// the finding of each.
const KNOWN: [(&str, &str); 21] = [
    (
        r"terms/cells/map-key/{k::is!(Int\, x),k::project!(Int\, x)}",
        "NT-1-1",
    ),
    (
        r"terms/{readable/map-key,rule/subject/set-element}/{Cmd::Pair \{ a: x\, ..x \},k::is!(Int\, x),k::matches!(x\, Cmd::Hold(_)),k::project!(Int\, x),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \}}",
        "NT-1-1",
    ),
    (
        r"terms/readable/map-key/function-argument/{Cmd::Go() | Cmd::Hold(_),Cmd::Pair \{ a: x\, ..x \},_,k::is!(Int\, x),k::matches!(x\, Cmd::Hold(_)),k::ml::exists(|v: Int| k::ml::equals(v\, 0)),k::project!(Int\, x),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \}}",
        "NT-1-1",
    ),
    (
        r#"terms/{readable/map-key/let-body,readable/map-key/update-field}/{!(x < 1),"s",-(x + 1),-1,1,1.5,Cmd::Go,Cmd::Go(),Cmd::Go() | Cmd::Hold(_),Cmd::Hold(x),Cmd::Pair \{ a: x\, .. \},Cmd::Pair \{ a: x\, ..x \},Size(x),Wrap::<KItem>(x),[x\, ..],_,k::anonymous!(Int\, "_V"),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1),k::builtin::set::item(x),k::bytes!(b"ab"),k::fragment![crate::Frame \{ ret: 1 \}],k::id!("$x"),k::is!(Int\, x),k::lexeme!(Word\, "word"),k::map![x -> 1],k::matches!(x\, Cmd::Hold(_)),k::ml::exists(|v: Int| k::ml::equals(v\, 0)),k::or_bool!(true\, false),k::project!(Int\, x),k::rewrite!(_ => 1),map![x -> 1],true,x,x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x | 1,x || true,x.add::<Int>(1),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \}}"#,
        "NT-1-1",
    ),
    (
        r#"terms/readable/map-key/let-pattern/{"s",-1,1,1.5,Cmd::Go,Cmd::Go(),Cmd::Go() | Cmd::Hold(_),Cmd::Hold(x),Cmd::Pair \{ a: x\, .. \},Size(x),Wrap::<KItem>(x),[x\, ..],_,k::anonymous!(Int\, "_V"),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1),k::builtin::set::item(x),k::bytes!(b"ab"),k::fragment![crate::Frame \{ ret: 1 \}],k::id!("$x"),k::is!(Int\, x),k::lexeme!(Word\, "word"),k::map![x -> 1],k::matches!(x\, Cmd::Hold(_)),k::or_bool!(true\, false),k::project!(Int\, x),k::rewrite!(_ => 1),map![x -> 1],true,x,y @ Cmd::Hold(_)}"#,
        "NT-1-1",
    ),
    (
        r#"terms/readable/map-key/matches-pattern/{"s",-1,1,1.5,Cmd::Go,Cmd::Go(),Cmd::Go() | Cmd::Hold(_),Cmd::Hold(x),Cmd::Pair \{ a: x\, .. \},Size(x),Wrap::<KItem>(x),[x\, ..],_,k::anonymous!(Int\, "_V"),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1),k::builtin::set::item(x),k::bytes!(b"ab"),k::fragment![crate::Frame \{ ret: 1 \}],k::id!("$x"),k::is!(Int\, x),k::lexeme!(Word\, "word"),k::map![x -> 1],k::or_bool!(true\, false),k::project!(Int\, x),k::rewrite!(_ => 1),map![x -> 1],true,x,x | 1,y @ Cmd::Hold(_)}"#,
        "NT-1-1",
    ),
    (
        r"terms/{cells/map-value,readable/collection-child,readable/cons-element,readable/list-element}/{Size(x),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1)}",
        "NT-1-2",
    ),
    (
        r"terms/{alias/subject,cells-claim/item-root,cells-claim/subject,claim/item-root,claim/subject,desugar/subject,simplification/subject}/{k::is!(Int\, x),k::project!(Int\, x)}",
        "NT-1-3",
    ),
    (
        r"terms/{rule/guard/let-pattern,rule/guard/matches-pattern,sort-rule/result/let-pattern,sort-rule/result/matches-pattern}/{Size(x),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1)}",
        "NT-2-1",
    ),
    (
        r"terms/readable/map-key/function-argument/Cmd::Pair \{ a: x\, .. \}",
        "NT-2-2",
    ),
    (
        r"terms/{context-alias/item-root,context-alias/subject}/{Size(x),k::builtin::int::add(1\, 2)}",
        "NT-2-3",
    ),
    (
        r"terms/context/subject/{Size(x),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1)}",
        "NT-2-3",
    ),
    (
        r"terms/{alias/result,alias/result-root,cells-claim/guard,cells-claim/guard/closure-body,claim/result,claim/result-item-root,context/guard,desugar/result,desugar/result-root,equation/guard,equation/result,local-rule/subject/rewrite-right,readable/guard,readable/result,readable/result-item-root,readable/result-list-element,rule/guard,rule/guard/closure-body,rule/guard/let-body,rule/result,rule/result-root,shorthand/result,shorthand/result-root,simplification/guard,simplification/result,simplification/result-root,sort-rule/result,sort-rule/result-root,sort-rule/result/function-argument,sort-rule/result/let-body,sort-rule/result/update-field,table/result}/Cmd::Pair \{ a: x\, .. \}",
        "NT-2-4",
    ),
    (
        r"terms/cells/map-key/{!(x < 1),-(x + 1),x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x || true,x.add::<Int>(1)}",
        "NT-2-5",
    ),
    (
        r"terms/{readable/map-key/function-argument,readable/map-key/let-body,readable/map-key/update-field}/y @ Cmd::Hold(_)",
        "NT-2-6",
    ),
    (
        r"terms/readable/map-key/let-pattern/{!(x < 1),-(x + 1),Cmd::Pair \{ a: x\, ..x \},k::ml::exists(|v: Int| k::ml::equals(v\, 0)),x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x || true,x.add::<Int>(1)}",
        "NT-2-6",
    ),
    (
        r"terms/readable/map-key/matches-pattern/{!(x < 1),-(x + 1),Cmd::Pair \{ a: x\, ..x \},k::ml::exists(|v: Int| k::ml::equals(v\, 0)),x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x || true,x.add::<Int>(1),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \}}",
        "NT-2-6",
    ),
    (
        r"terms/{sort-rule/subject-root,sort-rule/subject-root-term}/_",
        "NT-2-9",
    ),
    (r"terms/readable/map-key/let-pattern/x | 1", "NT-2-25"),
    (
        r"terms/{context-alias/item-root,context-alias/subject}/k::builtin::int::add(x\, 1)",
        "NT-2-27",
    ),
    (
        r"terms/{readable/map-key/as-body,readable/map-key/or-branch}/{Size(x),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1)}",
        "S0-14",
    ),
];

/// The disagreements a reader of the product decides before the table's row, which are not red:
/// the table reads a readable key's `let` block, `k::matches!` and record update as a pattern,
/// and refuses them, while the term reader refuses the construct inside first, with the class the
/// oracle gives it (`_`, a map literal, a rest outside a pattern), or a name rule of the class
/// table does (`x | 1`'s alternatives binding other names in a `k::matches!` pattern).
const DECIDED_BEFORE_THE_TABLE: [&str; 18] = [
    "terms/readable/map-key/function-argument/Cmd::Go() | Cmd::Hold(_)",
    "terms/readable/map-key/function-argument/_",
    "terms/readable/map-key/function-argument/k::ml::exists(|v: Int| k::ml::equals(v, 0))",
    "terms/readable/map-key/let-body/Cmd::Go() | Cmd::Hold(_)",
    "terms/readable/map-key/let-body/[x, ..]",
    "terms/readable/map-key/let-body/_",
    "terms/readable/map-key/let-body/k::map![x -> 1]",
    "terms/readable/map-key/let-body/map![x -> 1]",
    "terms/readable/map-key/let-pattern/k::map![x -> 1]",
    "terms/readable/map-key/let-pattern/map![x -> 1]",
    "terms/readable/map-key/matches-pattern/k::map![x -> 1]",
    "terms/readable/map-key/matches-pattern/map![x -> 1]",
    "terms/readable/map-key/matches-pattern/x | 1",
    "terms/readable/map-key/update-field/Cmd::Go() | Cmd::Hold(_)",
    "terms/readable/map-key/update-field/[x, ..]",
    "terms/readable/map-key/update-field/_",
    "terms/readable/map-key/update-field/k::map![x -> 1]",
    "terms/readable/map-key/update-field/map![x -> 1]",
];

fn read_class_matrix(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn spec() -> Table {
    Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"))
}

/// The names of every class the table refuses with or leaves to the compiler.
fn table_class_names() -> BTreeSet<&'static str> {
    Class::ALL
        .iter()
        .map(|class| class.name())
        .chain(Rule::ALL.iter().map(|rule| rule.name()))
        .collect()
}

#[test]
fn every_class_of_the_table_is_a_spec_class_with_its_code() {
    let spec = spec();
    let mut drift = Vec::new();
    for class in Class::ALL {
        match spec.classes.get(class.name()) {
            None => drift.push(format!("{} is no class of expected.toml", class.name())),
            Some(expected) if expected.code != class.code().as_str() => drift.push(format!(
                "{} has the code {} in the table and {} in expected.toml",
                class.name(),
                class.code().as_str(),
                expected.code
            )),
            Some(_) => {}
        }
    }
    for rule in Rule::ALL {
        if !spec.classes.contains_key(rule.name()) {
            drift.push(format!("{} is no class of expected.toml", rule.name()));
        }
    }
    assert!(drift.is_empty(), "{drift:#?}");
}

#[test]
fn every_class_of_the_oracle_is_a_spec_class_and_covers_the_table() {
    let spec = spec();
    let oracle = oracle::Class::ALL
        .iter()
        .map(|class| class.name())
        .collect::<BTreeSet<_>>();
    let undeclared = oracle
        .iter()
        .filter(|class| !spec.classes.contains_key(**class))
        .collect::<Vec<_>>();
    assert!(undeclared.is_empty(), "{undeclared:#?}");
    let uncovered = table_class_names()
        .into_iter()
        .filter(|class| !oracle.contains(class))
        .collect::<Vec<_>>();
    assert!(uncovered.is_empty(), "{uncovered:#?}");
}

/// The product's form of a model form: the two enums name the same forms.
fn product_form(form: model::Form) -> Form {
    Form::ALL
        .into_iter()
        .find(|product| format!("{product:?}") == format!("{form:?}"))
        .unwrap_or_else(|| panic!("the product's table has no form {form:?}"))
}

/// The product's position of a model position.
fn product_position(position: model::Position) -> Position {
    let form = product_form(position.form);
    let slot = match position.slot {
        model::Slot::Subject => Slot::Subject,
        model::Slot::Result => Slot::Result,
        model::Slot::Requires => Slot::Requires,
        model::Slot::Value if form == Form::Constant => Slot::ConstantValue,
        model::Slot::Value => Slot::InitializerValue,
    };
    let nesting = position.nesting;
    let entries = nesting.entries;
    let product = Position {
        form,
        slot,
        nesting: Nesting {
            in_matches_pattern: nesting.local == Some(LocalPattern::Matches),
            in_let_pattern: nesting.local == Some(LocalPattern::Let),
            in_rewrite: nesting.rewrite.is_some(),
            // The computation cell's items are no collection's entries to the table.
            in_collection_entry: entries.contains(Entry::MapKey)
                || entries.contains(Entry::MapValue)
                || entries.contains(Entry::ListElement)
                || entries.contains(Entry::SetElement),
            in_map_key: entries.contains(Entry::MapKey),
        },
    };
    if nesting.rewrite == Some(RewriteSide::Right) {
        product.rewrite_right()
    } else {
        product
    }
}

/// The product's construct of a model construct; `None` for a construct the table has no row
/// for: a binder and a constructor application, which stand wherever a term does below a
/// pattern's root, and list brackets, whose sort the compiler judges.
const fn product_construct(construct: model::Construct) -> Option<Construct> {
    use model::Construct as M;
    Some(match construct {
        M::Reference | M::Constructor | M::ListBrackets => return None,
        M::Turbofish => Construct::Turbofish,
        M::Literal => Construct::Literal,
        M::FunctionApplication
        | M::BuiltinApplication
        | M::Notation(_)
        | M::MapLiteral
        | M::Rest => Construct::FunctionApplication,
        M::Wildcard => Construct::Wildcard,
        M::As => Construct::As,
        M::Or => Construct::Or,
        M::Matches => Construct::Matches,
        M::Let => Construct::Let,
        M::MlPredicate => Construct::MlPredicate,
        M::Rewrite => Construct::Rewrite,
        M::SortTest => Construct::SortTest,
        M::Anonymous => Construct::Anonymous,
        M::OrBool => Construct::OrBool,
        M::Fragment => Construct::Fragment,
        M::RecordUpdate => Construct::RecordUpdate,
        M::OpenRecord => Construct::OpenRecord,
        M::IdToken => Construct::IdToken,
        M::BytesToken => Construct::BytesToken,
        M::Lexeme => Construct::Lexeme,
    })
}

/// What a reader of the product answers before its table.
enum Read {
    /// The reader refuses the construct with the class.
    Refuses(&'static str),
    /// The reader admits the construct.
    Admits,
    /// The table decides.
    Table,
}

/// The product's own rules outside the table, which its readers apply before it:
/// - `krs_syntax::positions::PatternRoot::admits`, the pattern reader's rule for a subject's
///   whole root ([`root_rule`]);
/// - `krs_syntax::notation::notation_in_pattern`: where a pattern is parsed, a subject, a local
///   pattern or a `cells!` map's key (a readable map read parses its key as an expression), a
///   notation form is no pattern; elsewhere it is the application it denotes, which the table's
///   application row decides;
/// - a constant's value reader refuses an operator and a map literal as no ground term;
/// - the term reader takes no macro but the compiler-owned islands, so a map literal is refused
///   at every term position;
/// - list notation: an anonymous `..` keeps a rest only in a pattern;
/// - a readable map read's value is a binder or `_`.
fn reader(construct: model::Construct, position: model::Position) -> Read {
    use model::Construct as M;
    if let Some(refused) = root_rule(construct, position) {
        return Read::Refuses(refused);
    }
    let pattern = matches!(position.kind, Kind::Matched | Kind::Evaluated);
    // A readable map read's key is read as an expression, a `cells!` map's as a pattern.
    let parsed_as_pattern = position.kind == Kind::Matched
        || (position.kind == Kind::Evaluated && position.form.writes_cells());
    let readable_value = matches!(
        position.form,
        model::Form::ReadableRule | model::Form::ReadableClaim
    ) && position.nesting.entries.innermost() == Some(Entry::MapValue)
        && position.kind == Kind::Matched;
    if readable_value && !matches!(construct, M::Reference | M::Wildcard) {
        return Read::Refuses("map-read-value-binder");
    }
    let constant = position.form == model::Form::Constant;
    match construct {
        M::Notation(Notation::BitwiseOr) if parsed_as_pattern => Read::Table,
        M::Notation(_) if parsed_as_pattern => Read::Refuses("notation-in-pattern"),
        M::Notation(_) | M::MapLiteral | M::Rest if constant => {
            Read::Refuses("constant-not-ground")
        }
        M::MapLiteral => Read::Refuses("map-literal-in-term"),
        M::Rest if pattern => Read::Admits,
        M::Rest => Read::Refuses("rest-outside-pattern"),
        _ => Read::Table,
    }
}

/// The pattern reader's rule for a construct standing for a subject's whole root: an alias, `_`
/// and a compiler-owned island stand below the root of a fn's, a table row's, a context's or a
/// static clause's subject, and a `for Sort` clause's root reads a bare name, an alias or an
/// island as a readable record's value does.
fn root_rule(construct: model::Construct, position: model::Position) -> Option<&'static str> {
    use model::Construct as M;
    let root = match position.root? {
        PatternRoot::Subject => product_table::PatternRoot::Subject,
        PatternRoot::Clause => product_table::PatternRoot::Clause,
        PatternRoot::Value => product_table::PatternRoot::Value,
    };
    let (root_construct, class) = match construct {
        M::As => (RootConstruct::As, "alias-at-subject-root"),
        M::Wildcard => (RootConstruct::Wildcard, "wildcard-at-subject-root"),
        construct if construct.is_island() => (RootConstruct::Island, "island-at-subject-root"),
        _ => return None,
    };
    let holds_name_or_island = !matches!(root_construct, RootConstruct::Wildcard);
    (!root.at(holds_name_or_island).admits(root_construct)).then_some(class)
}

/// A table's answer for one case: the first refusal in preorder, and the classes it leaves to
/// the compiler before it below a pattern's root. At a subject's root the compiler judges the
/// root's head (an equation's function, a static clause's production), which the table leaves
/// alone, so those answers are the class tests' (`expected.toml`) to compare.
#[derive(Debug, Default, Eq, PartialEq)]
struct Answer {
    refused: Option<&'static str>,
    after: BTreeSet<&'static str>,
}

/// The product's answer for `nodes` at `hole`: its readers' rules, then its table.
fn product(hole: model::Position, nodes: &[model::Node]) -> Answer {
    let mut answer = Answer::default();
    for node in nodes {
        let position = hole.enter_all(&node.path);
        match reader(node.construct, position) {
            Read::Refuses(refused) => {
                answer.refused = Some(refused);
                break;
            }
            Read::Admits => continue,
            Read::Table => {}
        }
        // Where a pattern is parsed, `x | 1` is alternatives, the table's `|` row.
        let parsed_as_pattern = position.kind == Kind::Matched
            || (position.kind == Kind::Evaluated && position.form.writes_cells());
        let read = match node.construct {
            model::Construct::Notation(Notation::BitwiseOr) if parsed_as_pattern => {
                model::Construct::Or
            }
            construct => construct,
        };
        let Some(construct) = product_construct(read) else {
            continue;
        };
        match admits(product_position(position), construct) {
            Admission::Refuse(class) => {
                answer.refused = Some(class.name());
                break;
            }
            Admission::After(rule) if position.root.is_none() => {
                answer.after.insert(rule.name());
            }
            Admission::Admit | Admission::After(_) => {}
        }
    }
    answer
}

/// The oracle's answer for `nodes` at `hole`, in the same shape: its first placement refusal,
/// and its resolution refusals before it below a pattern's root.
fn oracle(hole: model::Position, nodes: &[model::Node]) -> Answer {
    let mut answer = Answer::default();
    for node in nodes {
        let position = hole.enter_all(&node.path);
        match oracle::admits(node.construct, position) {
            Some(refusal) if refusal.stage == Stage::Placement => {
                answer.refused = Some(refusal.class.name());
                break;
            }
            Some(refusal) if position.root.is_none() => {
                answer.after.insert(refusal.class.name());
            }
            None | Some(_) => {}
        }
    }
    answer
}

fn term_cases(cases: &[Case]) -> impl Iterator<Item = &Case> {
    cases
        .iter()
        .filter(|case| matches!(case.family, Family::Terms | Family::Import))
}

#[test]
fn the_table_decides_every_term_case_as_the_oracle_does() {
    let pending = Pending::parse(&read_class_matrix("pending.toml"))
        .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let mut disagreements = Vec::new();
    let mut judged = 0;
    for case in term_cases(&cases) {
        let term = case.term.as_ref().expect("a term case has a position");
        let product = product(term.position, &term.nodes);
        let oracle = oracle(term.position, &term.nodes);
        // The product refuses where the oracle tells a placement mistake, and leaves to the
        // compiler what the oracle refuses by resolution. Which class the compiler then answers
        // with, and what more it is left (a predicate in a claim's condition, which it tells from
        // an operand), the full tier judges end to end.
        let deferred = !product.after.is_empty() || product.refused.is_some();
        if product.refused != oracle.refused || (!oracle.after.is_empty() && !deferred) {
            disagreements.push((
                case.id.as_str(),
                format!("the table says {product:?}, the oracle says {oracle:?}"),
            ));
        }
        judged += 1;
    }
    assert!(judged > 4000, "only {judged} term cases were judged");
    let known = KNOWN.map(|(pattern, finding)| {
        let glob = Glob::parse(pattern).unwrap_or_else(|reason| panic!("{pattern}: {reason}"));
        (pattern, glob, finding)
    });
    let unknown = disagreements
        .iter()
        .filter(|(id, _)| !known.iter().any(|(_, glob, _)| glob.matches(id)))
        .map(|(id, line)| format!("{id}: {line}"))
        .collect::<Vec<_>>();
    assert!(
        unknown.is_empty(),
        "{} disagreements:\n{}",
        unknown.len(),
        unknown.join("\n")
    );
    let gone = known
        .iter()
        .filter(|(_, glob, _)| !disagreements.iter().any(|(id, _)| glob.matches(id)))
        .map(|(pattern, _, _)| *pattern)
        .collect::<Vec<_>>();
    assert!(
        gone.is_empty(),
        "known disagreements that agree now: {gone:?}"
    );
    // A disagreement that is red is pending under its finding. One that is not is decided before
    // the table's row: by a name or sort rule of the table, met before the oracle's resolution
    // refusal, or by a reader of the product that refuses an inner construct the oracle refuses
    // too (the table reads a readable key's `let` block as a pattern, the term reader refuses
    // the `_` or the map literal in it first); the full tier checks the latter end to end, and
    // the list of such cases is pinned here.
    let table = spec();
    let overridden = table.resolve_cases(&cases, registry_kind).overridden;
    let mut misfiled = Vec::new();
    let mut decided_before_the_table = Vec::new();
    for (id, _) in &disagreements {
        let (pattern, _, finding) = known
            .iter()
            .find(|(_, glob, _)| glob.matches(id))
            .expect("every disagreement is known");
        let filed = pending.entries.get(*id).map(|entry| entry.finding.as_str());
        if filed.is_some_and(|filed| filed != *finding) {
            misfiled.push(format!(
                "{id} ({pattern}): pending as {filed:?}, not {finding}"
            ));
        }
        if filed.is_none() && !overridden.contains_key(*id) {
            decided_before_the_table.push(*id);
        }
    }
    assert!(misfiled.is_empty(), "{misfiled:#?}");
    assert_eq!(
        decided_before_the_table, DECIDED_BEFORE_THE_TABLE,
        "disagreements neither red nor overridden"
    );
}

/// Every form of the product's table has a generated position.
#[test]
fn every_form_of_the_table_has_a_generated_position() {
    let cases = class_matrix::cases();
    let generated = term_cases(&cases)
        .filter_map(|case| case.term.as_ref())
        .map(|term| format!("{:?}", term.position.form))
        .collect::<BTreeSet<_>>();
    let missing = Form::ALL
        .iter()
        .map(|form| format!("{form:?}"))
        .filter(|form| !generated.contains(form))
        .collect::<Vec<_>>();
    assert!(missing.is_empty(), "forms without a case: {missing:?}");
}

/// The slot roots no case is generated at, and why.
const ROOTS_NOT_GENERATED: [(model::Form, model::Slot, &str); 3] = {
    use model::Form as F;
    use model::Slot as S;
    [
        (
            F::CellsLocalRule,
            S::Subject,
            "a single-body rule whose computation item holds no rewrite changes nothing there",
        ),
        (
            F::EquationTable,
            S::Subject,
            "a row's subject is the function its header names, applied to the row's arguments",
        ),
        (
            F::EquationTable,
            S::Result,
            "a row's result has its function's sort, `Int`; the shorthand's result root is an equation's at `KItem`",
        ),
    ]
};

/// The conditions no case is generated in, and the condition that reads alike, whose cases
/// stand for them: a condition is a guard in every form, and differs only by whether the form
/// admits a predicate, whether it is a claim (`k::or_bool!` and, as boundary NT-Q1, `let` and
/// `k::matches!` depend on it) and whether it is a `cells!` value's; each listed form shares all
/// three with the form named. A simplification's condition shares none with a claim's but the
/// first, so it is generated.
const CONDITIONS_NOT_GENERATED: [(model::Form, &str); 6] = {
    use model::Form as F;
    [
        (F::ReadableClaim, "a `cells!` claim's"),
        (F::SortRule, "a readable rule's"),
        (F::EquationTable, "an equation fn's"),
        (F::LocalRule, "a rule fn's"),
        (F::CellsRule, "a rule fn's"),
        (F::CellsLocalRule, "a rule fn's"),
    ]
};

/// A slot's root or a position below it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Depth {
    Root,
    Argument,
}

/// The path of a slot's term root: the computation item for a record's slot, whose own root
/// holds cell entries (the readable, `cells!` and initializer families'), and the slot's root
/// otherwise.
fn root_path(form: model::Form, slot: model::Slot) -> &'static [Opening] {
    use model::Form as F;
    match (form, slot) {
        (
            F::ReadableRule
            | F::ReadableClaim
            | F::CellsRule
            | F::CellsLocalRule
            | F::CellsClaim
            | F::ContextAlias,
            model::Slot::Subject | model::Slot::Result,
        )
        | (F::Initializer, _) => &[Opening::ComputationItem],
        _ => &[],
    }
}

/// Every slot of every form has a case at its root and one below it, but the listed ones.
#[test]
fn every_slot_has_a_root_and_an_argument_case() {
    let cases = class_matrix::cases();
    let mut reached = BTreeSet::new();
    for term in term_cases(&cases).filter_map(|case| case.term.as_ref()) {
        let (form, slot) = (term.position.form, term.position.slot);
        for node in &term.nodes {
            let path = term
                .path
                .iter()
                .chain(&node.path)
                .copied()
                .collect::<Vec<_>>();
            let depth = if path == root_path(form, slot) {
                Depth::Root
            } else {
                Depth::Argument
            };
            reached.insert((form, slot, depth));
        }
    }
    let mut excepted = ROOTS_NOT_GENERATED
        .iter()
        .map(|(form, slot, _)| (*form, *slot, Depth::Root))
        .collect::<BTreeSet<_>>();
    for (form, _) in CONDITIONS_NOT_GENERATED {
        excepted.insert((form, model::Slot::Requires, Depth::Root));
        excepted.insert((form, model::Slot::Requires, Depth::Argument));
    }
    let mut missing = Vec::new();
    let mut stale = Vec::new();
    for form in model::Form::ALL {
        for slot in form.slots() {
            for depth in [Depth::Root, Depth::Argument] {
                let key = (form, *slot, depth);
                match (reached.contains(&key), excepted.contains(&key)) {
                    (false, false) => missing.push(key),
                    (true, true) => stale.push(key),
                    _ => {}
                }
            }
        }
    }
    assert!(missing.is_empty(), "positions without a case: {missing:?}");
    assert!(
        stale.is_empty(),
        "excepted positions that have a case: {stale:?}"
    );
}

/// The notation form a builtin operator's spelling is, by its symbol.
fn notation_of(operator: BuiltinOperator) -> Option<model::Construct> {
    Some(match operator.symbol() {
        "+" | "-" if operator.arity() == 2 => model::Construct::Notation(Notation::Arithmetic),
        "*" | "/" | "%" => model::Construct::Notation(Notation::Arithmetic),
        "&" | "^" => model::Construct::Notation(Notation::Bitwise),
        "|" => model::Construct::Notation(Notation::BitwiseOr),
        "<<" | ">>" => model::Construct::Notation(Notation::Shift),
        "<" | "<=" | ">" | ">=" => model::Construct::Notation(Notation::Comparison),
        "==" | "!=" => model::Construct::Notation(Notation::Equality),
        "!" => model::Construct::Notation(Notation::Not),
        "-" => model::Construct::Notation(Notation::Negation),
        _ => return None,
    })
}

/// Every construct of the product's table and of the model, every notation form and every
/// builtin operator has a spelling, and so do the collection forms.
#[test]
fn every_construct_and_notation_has_a_spelling() {
    let cases = class_matrix::cases();
    let spelled = term_cases(&cases)
        .filter_map(|case| case.term.as_ref())
        .flat_map(|term| term.nodes.iter().map(|node| node.construct))
        .collect::<BTreeSet<_>>();
    let mut missing = model::Construct::ALL
        .iter()
        .filter(|construct| !spelled.contains(construct))
        .map(|construct| format!("{construct:?}"))
        .collect::<Vec<_>>();
    let products = spelled
        .iter()
        .filter_map(|construct| product_construct(*construct))
        .collect::<BTreeSet<_>>();
    missing.extend(
        Construct::ALL
            .iter()
            .filter(|construct| !products.contains(construct))
            .map(|construct| format!("the table's {construct:?}")),
    );
    for operator in BuiltinOperator::ALL {
        match notation_of(operator) {
            Some(construct) if spelled.contains(&construct) => {}
            _ => missing.push(format!("the operator `{}`", operator.symbol())),
        }
    }
    let constructs = cases
        .iter()
        .map(|case| case.construct.as_str())
        .collect::<BTreeSet<_>>();
    for collection in ["k::map![", "map![", "[x, ..]", "k::builtin::set::item("] {
        if !constructs.iter().any(|text| text.starts_with(collection)) {
            missing.push(format!("the collection form `{collection}`"));
        }
    }
    let notations = Notation::ALL
        .iter()
        .filter(|notation| !spelled.contains(&model::Construct::Notation(**notation)))
        .map(|notation| format!("the notation {notation:?}"));
    missing.extend(notations);
    // The product's own predicate of notation (`krs_syntax::is_expression_notation`), asked of
    // every expression shape: each it calls notation is a form of the model with a spelling. The
    // product exposes no table of its forms, so the shapes are listed here: a notation NT-5 or
    // NT-6 adds over a shape not listed (an index `m[k]` is) must add its shape.
    for (shape, notation) in EXPRESSION_SHAPES {
        let expression =
            syn::parse_str::<syn::Expr>(shape).unwrap_or_else(|error| panic!("{shape}: {error}"));
        match (krs_syntax::is_expression_notation(&expression), notation) {
            (true, Some(notation)) if spelled.contains(&model::Construct::Notation(notation)) => {}
            (true, Some(_)) => missing.push(format!("the notation form `{shape}`")),
            (true, None) if COMPOUND_ASSIGNMENTS.contains(&shape) => {}
            (true, None) => missing.push(format!("the notation form `{shape}`, of no model form")),
            (false, _) => {}
        }
    }
    assert!(missing.is_empty(), "without a spelling: {missing:#?}");
}

/// Expression shapes, and the model's notation form of each the product reads as notation.
const EXPRESSION_SHAPES: [(&str, Option<Notation>); 37] = [
    ("a + b", Some(Notation::Arithmetic)),
    ("a - b", Some(Notation::Arithmetic)),
    ("a * b", Some(Notation::Arithmetic)),
    ("a / b", Some(Notation::Arithmetic)),
    ("a % b", Some(Notation::Arithmetic)),
    ("a & b", Some(Notation::Bitwise)),
    ("a ^ b", Some(Notation::Bitwise)),
    ("a | b", Some(Notation::BitwiseOr)),
    ("a << b", Some(Notation::Shift)),
    ("a >> b", Some(Notation::Shift)),
    ("a == b", Some(Notation::Equality)),
    ("a != b", Some(Notation::Equality)),
    ("a < b", Some(Notation::Comparison)),
    ("a <= b", Some(Notation::Comparison)),
    ("a > b", Some(Notation::Comparison)),
    ("a >= b", Some(Notation::Comparison)),
    ("a && b", Some(Notation::AndThen)),
    ("a || b", Some(Notation::OrElse)),
    ("!a", Some(Notation::Not)),
    ("-a", Some(Notation::Negation)),
    ("a.add::<Int>(b)", Some(Notation::Method)),
    ("a += b", None),
    ("a -= b", None),
    ("a *= b", None),
    ("a /= b", None),
    ("a %= b", None),
    ("a &= b", None),
    ("a |= b", None),
    ("a ^= b", None),
    ("a <<= b", None),
    ("a >>= b", None),
    ("*a", None),
    ("a[b]", None),
    ("a as T", None),
    ("a..b", None),
    ("a.b", None),
    ("f(a)", None),
];

/// The shapes the product reads as notation though they denote none: a compound assignment
/// (`a += b`), which a term has nothing to assign to, and which the product refuses as notation.
const COMPOUND_ASSIGNMENTS: [&str; 10] = [
    "a += b", "a -= b", "a *= b", "a /= b", "a %= b", "a &= b", "a |= b", "a ^= b", "a <<= b",
    "a >>= b",
];
