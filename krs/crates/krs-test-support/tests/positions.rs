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
const KNOWN: [(&str, &str); 20] = [
    // A pattern's key holds no `let` block or `k::matches!` (NT-3-2's boundary), so a construct in
    // one's body, pattern or matched pattern there is refused with it; the collection notation and
    // its calls are such constructs. Where a `let` or `k::matches!` pattern holds the notation, no
    // Rust parser reads the pattern first (NT-2-6).
    ("notation/readable/map-key/let-body/*", "NT-3-2"),
    (
        r"notation/readable/map-key/{let-pattern,matches-pattern}/k::builtin::{list::get,list::size,map::get,map::in_keys,map::update,set::to_list}(*",
        "NT-3-2",
    ),
    (
        r"notation/readable/map-key/{let-pattern,matches-pattern}/k::builtin::{list::item(x)[0],list::item(x).len(),map::empty()[x],map::empty().contains_key(x),map::empty().update(x\, 1),set::item(x).to_list()}",
        "NT-2-6",
    ),
    // The collection literals and the calls they denote are such constructs too; a literal is a
    // macro, which a Rust pattern reads, so the boundary is met first.
    (
        r"notation/readable/map-key/{let-pattern,matches-pattern}/{map![*,set![*,k::builtin::map::empty(),k::builtin::set::empty(),k::builtin::set::item(x),k::builtin::set::union(*}",
        "NT-3-2",
    ),
    (
        r"terms/readable/set-instance-child/{k::matches!(x\, Cmd::Hold(_)),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}",
        "NT-3-2",
    ),
    (
        r"terms/rule/subject/set-element-beside-fresh/Cmd::Pair \{ a: x\, ..x \}",
        "NT-3-1",
    ),
    (
        r"terms/rule/subject/set-element-beside-fresh/{k::is!(Int\, x),k::project!(Int\, x)}",
        "NT-3-1",
    ),
    (
        r"terms/{alias/result,alias/result-root,cells-claim/guard,cells-claim/guard/closure-body,claim/result,claim/result-item-root,context/guard,desugar/result,desugar/result-root,equation/guard,equation/result,local-rule/subject/rewrite-right,readable/guard,readable/result,readable/result-item-root,readable/result-list-element,rule/guard,rule/guard/closure-body,rule/guard/let-body,rule/result,rule/result-root,shorthand/result,shorthand/result-root,simplification/guard,simplification/result,simplification/result-root,sort-rule/result,sort-rule/result-root,sort-rule/result/function-argument,sort-rule/result/let-body,sort-rule/result/update-field,table/result}/Cmd::Pair \{ a: x\, .. \}",
        "NT-2-4",
    ),
    (
        r"terms/readable/map-key/function-argument/y @ Cmd::Hold(_)",
        "NT-2-6",
    ),
    (
        r"terms/readable/map-key/let-body/y @ Cmd::Hold(_)",
        "NT-2-6",
    ),
    (
        r"terms/readable/map-key/let-pattern/{!(x < 1),-(x + 1),Cmd::Pair \{ a: x\, ..x \},k::ml::exists(|v: Int| k::ml::equals(v\, 0)),x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x || true,x.add::<Int>(1)}",
        "NT-2-6",
    ),
    (
        r"terms/readable/map-key/matches-pattern/{!(x < 1),-(x + 1),Cmd::Pair \{ a: x\, ..x \},k::ml::exists(|v: Int| k::ml::equals(v\, 0)),x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x || true,x.add::<Int>(1),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}",
        "NT-2-6",
    ),
    (r"terms/readable/map-key/let-pattern/x | 1", "NT-2-25"),
    // A set's element reads as a constructor's argument to the product, which cannot tell
    // `set::item` before resolution (NT-3-1).
    (
        r"terms/rule/subject/set-element/{Cmd::Pair \{ a: x\, ..x \},k::is!(Int\, x),k::matches!(x\, Cmd::Hold(_)),k::project!(Int\, x),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}",
        "NT-3-1",
    ),
    // A pattern's key holds no `let` block or `k::matches!` (NT-3-2's boundary), which the oracle
    // admits as a computed key.
    (
        r"terms/readable/map-key/function-argument/{k::matches!(x\, Cmd::Hold(_)),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}",
        "NT-3-2",
    ),
    (
        r"terms/readable/map-key/{k::matches!(x\, Cmd::Hold(_)),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}",
        "NT-3-2",
    ),
    (
        r#"terms/readable/map-key/let-body/{!(x < 1),"s",-(x + 1),-1,1,1.5,Cmd::Go,Cmd::Go(),Cmd::Go() | Cmd::Hold(_),Cmd::Hold(x),Cmd::Pair \{ a: x\, .. \},Cmd::Pair \{ a: x\, ..x \},Size(x),Wrap::<KItem>(x),[x\, ..],_,k::anonymous!(Int\, "_V"),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1),k::builtin::set::item(x),k::bytes!(b"ab"),k::fragment![crate::Frame \{ ret: 1 \}],k::id!("$x"),k::is!(Int\, x),k::lexeme!(Word\, "word"),k::map![x -> 1],k::matches!(x\, Cmd::Hold(_)),k::ml::exists(|v: Int| k::ml::equals(v\, 0)),k::or_bool!(true\, false),k::project!(Int\, x),k::rewrite!(_ => 1),map![x -> 1],true,x,x & 1,x && true,x + 1,x < 1,x << 1,x == 1,x | 1,x || true,x.add::<Int>(1),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}"#,
        "NT-3-2",
    ),
    (
        r#"terms/readable/map-key/let-pattern/{"s",-1,1,1.5,Cmd::Go,Cmd::Go(),Cmd::Go() | Cmd::Hold(_),Cmd::Hold(x),Cmd::Pair \{ a: x\, .. \},Size(x),Wrap::<KItem>(x),[x\, ..],_,k::anonymous!(Int\, "_V"),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1),k::builtin::set::item(x),k::bytes!(b"ab"),k::fragment![crate::Frame \{ ret: 1 \}],k::id!("$x"),k::is!(Int\, x),k::lexeme!(Word\, "word"),k::map![x -> 1],k::matches!(x\, Cmd::Hold(_)),k::or_bool!(true\, false),k::project!(Int\, x),k::rewrite!(_ => 1),map![x -> 1],true,x,y @ Cmd::Hold(_)}"#,
        "NT-3-2",
    ),
    (
        r#"terms/readable/map-key/matches-pattern/{"s",-1,1,1.5,Cmd::Go,Cmd::Go(),Cmd::Go() | Cmd::Hold(_),Cmd::Hold(x),Cmd::Pair \{ a: x\, .. \},Size(x),Wrap::<KItem>(x),[x\, ..],_,k::anonymous!(Int\, "_V"),k::builtin::int::add(1\, 2),k::builtin::int::add(x\, 1),k::builtin::set::item(x),k::bytes!(b"ab"),k::fragment![crate::Frame \{ ret: 1 \}],k::id!("$x"),k::is!(Int\, x),k::lexeme!(Word\, "word"),k::map![x -> 1],k::or_bool!(true\, false),k::project!(Int\, x),k::rewrite!(_ => 1),map![x -> 1],true,x,x | 1,y @ Cmd::Hold(_)}"#,
        "NT-3-2",
    ),
    (
        r"terms/readable/map-key/update-field/{k::matches!(x\, Cmd::Hold(_)),\{ let (Cmd::Go() | Cmd::Hold(_)) = x; x \},\{ let y = x; y \},\{ let y @ Cmd::Hold(_) = x; y \},\{ let Cmd::Pair \{ a: _\, b \} = x; Cmd::Pair \{ a: 1\, b \} \}}",
        "NT-3-2",
    ),
];

/// The disagreements that are no finding's, as globs over case IDs, and why: the product decides
/// them outside its table, where the oracle's answer is met.
const NOT_RED: [(&str, &str); 2] = [
    (
        r"terms/readable/map-key/function-argument/{Cmd::Go() | Cmd::Hold(_),Cmd::Pair \{ a: x\, .. \},_,k::ml::exists(|v: Int| k::ml::equals(v\, 0))}",
        "a function's argument in a key is built, and the table cannot tell it from a constructor's before resolution: the compiler refuses the open record there (`key_names`), and the readable key's reader, which reads an expression, refuses `_`, alternatives and a closure first",
    ),
    (
        "terms/desugar/subject/[x, ..]",
        "a list's brackets in a desugar's `KItem` argument are refused by their sort (`list-notation-sort`), which the compiler meets before the oracle's `collection-in-static-subject` and the table overrides it with",
    ),
];

/// The disagreements the product decides before or outside the table's row, which are not red:
/// the table refuses a `let` block and `k::matches!` in a readable key (NT-3-2), and the term
/// reader refuses the construct inside first, with the class the oracle gives it (`_`, a rest
/// outside a pattern), or a name rule of the class table does (`x | 1`'s
/// alternatives binding other names in a `k::matches!` pattern); the readable key's reader, which
/// reads an expression, refuses `_`, alternatives and a closure below a function's application;
/// and the compiler refuses an open record there (`key_names`), which the table cannot tell from a
/// constructor's argument before resolution; a sort test in a set's element beside a name bound
/// nowhere else is refused with its class at placement, as in a constructor's field (NT-3-1), where
/// the oracle tells it once the element's names are known.
const DECIDED_BEFORE_THE_TABLE: [&str; 10] = [
    "terms/readable/map-key/function-argument/Cmd::Go() | Cmd::Hold(_)",
    "terms/readable/map-key/function-argument/Cmd::Pair { a: x, .. }",
    "terms/readable/map-key/function-argument/_",
    "terms/readable/map-key/function-argument/k::ml::exists(|v: Int| k::ml::equals(v, 0))",
    "terms/readable/map-key/let-body/Cmd::Go() | Cmd::Hold(_)",
    "terms/readable/map-key/let-body/[x, ..]",
    "terms/readable/map-key/let-body/_",
    "terms/readable/map-key/matches-pattern/x | 1",
    "terms/rule/subject/set-element-beside-fresh/k::is!(Int, x)",
    "terms/rule/subject/set-element-beside-fresh/k::project!(Int, x)",
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

/// The product's position of a model position, with the key reading the walker gives it from the
/// constructs above it ([`KeyReading`]).
fn product_position(position: model::Position, reading: KeyReading) -> Position {
    let form = product_form(position.form);
    let slot = match position.slot {
        model::Slot::Subject => Slot::Subject,
        model::Slot::Result => Slot::Result,
        model::Slot::Requires => Slot::Requires,
        model::Slot::Value if form == Form::Constant => Slot::ConstantValue,
        model::Slot::Value => Slot::InitializerValue,
    };
    let nesting = position.nesting;
    // A set's element is an application's argument to the table, which resolution alone tells
    // from a constructor's.
    let in_map_key = nesting.entries.contains(Entry::MapKey) && slot == Slot::Subject;
    let product = Position {
        form,
        slot,
        nesting: Nesting {
            in_matches_pattern: nesting.local == Some(LocalPattern::Matches),
            in_let_pattern: nesting.local == Some(LocalPattern::Let),
            in_rewrite: nesting.rewrite.is_some(),
            in_map_key,
            in_computed_key: in_map_key && reading.computed,
            in_selected_key: in_map_key && reading.selected && nesting.local.is_none(),
            // The walker knows an instance's braces, but not whose collection they write.
            in_braced_instance: nesting.entries.contains(Entry::Instance) && slot == Slot::Subject,
        },
    };
    if nesting.rewrite == Some(RewriteSide::Right) {
        product.rewrite_right()
    } else {
        product
    }
}

/// How the walker reads a key above a node, from the openings from the key to the node: below a
/// construct whose syntax computes (a `let` block, `k::matches!`, a sort test, a record update,
/// notation's operands), built; below `@` or `|` where nothing computes yet, a selection. A
/// function's application computes too, but resolution alone tells it from a constructor's, so
/// the walker reads its arguments as the key.
#[derive(Clone, Copy, Default)]
struct KeyReading {
    computed: bool,
    selected: bool,
}

fn key_reading(path: &[Opening], node: &model::Node, nodes: &[model::Node]) -> KeyReading {
    let mut reading = KeyReading::default();
    let mut in_key = false;
    let operand_of_notation = |depth: usize| {
        nodes.iter().any(|parent| {
            parent.path == node.path[..depth]
                && matches!(parent.construct, model::Construct::Notation(notation)
                    if notation != Notation::BitwiseOr && notation.applies_operation())
        })
    };
    for (index, opening) in path.iter().chain(&node.path).enumerate() {
        if *opening == Opening::MapKey {
            in_key = true;
            continue;
        }
        if !in_key {
            continue;
        }
        let depth = index.checked_sub(path.len());
        let computes = matches!(
            opening,
            Opening::LetValue
                | Opening::LetBody
                | Opening::MatchesSubject
                | Opening::SortTestOperand
                | Opening::UpdateField
                | Opening::UpdateBase
                | Opening::PredicateBody
                | Opening::PredicateOperand
        ) || (*opening == Opening::FunctionArgument
            && depth.is_some_and(operand_of_notation));
        if computes {
            reading.computed = true;
        } else if matches!(opening, Opening::AsBody | Opening::OrBranch) && !reading.computed {
            reading.selected = true;
        }
    }
    reading
}

/// The product's construct of a model construct; `None` for a construct the table has no row
/// for: a binder and a constructor application, which stand wherever a term does below a
/// pattern's root, a collection literal that denotes a value (`map![]`, `set![x]`), as its call
/// does, and list brackets, whose sort the compiler judges.
const fn product_construct(construct: model::Construct) -> Option<Construct> {
    use model::Construct as M;
    Some(match construct {
        M::Reference
        | M::Fresh
        | M::Constructor
        | M::CollectionValue
        | M::StaticApplication
        | M::ListBrackets
        | M::Notation(Notation::CollectionValue) => return None,
        M::Turbofish => Construct::Turbofish,
        M::Literal => Construct::Literal,
        // A static production's application the compiler cannot expand is refused after
        // resolution, which alone tells it from a constructor's, as a function's is.
        M::FunctionApplication
        | M::BuiltinApplication
        | M::Concatenation
        | M::OpenStaticApplication
        | M::Notation(_) => Construct::FunctionApplication,
        M::Rest => Construct::Rest,
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
    /// The table decides.
    Table,
}

/// The product's own rules outside the table, which its readers apply before it:
/// - `krs_syntax::positions::PatternRoot::admits`, the pattern reader's rule for a subject's
///   whole root ([`root_rule`]);
/// - `krs_syntax::notation::notation_in_pattern`: where a pattern is parsed, a subject or a local
///   pattern, a notation form is no pattern; elsewhere it is the application it denotes, which
///   the table's application row decides, in a key too (a readable map read parses its key as an
///   expression, and a `cells!` map's as a pattern or else an expression, as a braced collection
///   instance's cells are, a Set's or a Map's, which only resolution tells apart); an index or a
///   collection method is the application it denotes in a pattern too;
/// - a constant's value reader refuses an operator as no ground term, and reads an index, a
///   collection method or a collection literal as the calls it denotes;
/// - the term reader reads a collection literal (`map![..]`, `set![..]`) as the calls it denotes,
///   at every term position;
/// - list notation: an anonymous `..` keeps a rest only in a pattern, where the table judges it;
/// - a readable map read's value is a binder or `_`.
fn reader(construct: model::Construct, position: model::Position) -> Read {
    use model::Construct as M;
    if let Some(refused) = root_rule(construct, position) {
        return Read::Refuses(refused);
    }
    let pattern = matches!(position.kind, Kind::Matched | Kind::Evaluated);
    // A readable map read's key is read as an expression, a `cells!` map's as a pattern, or as
    // an expression where no pattern parses: `x | 1` is alternatives there, `x + 1` the call. So
    // is a braced collection instance's cell, a Set's or a Map's.
    let braced = position.nesting.entries.contains(Entry::Instance);
    let parsed_as_pattern = position.kind == Kind::Matched && !braced;
    let or_is_alternatives = position.kind == Kind::Matched
        || (position.kind == Kind::Evaluated && (position.form.writes_cells() || braced));
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
        M::Notation(Notation::BitwiseOr) if or_is_alternatives => Read::Table,
        // An index, a collection method or a collection literal is read as the calls it denotes
        // everywhere.
        M::Notation(notation) if notation.is_collection() => Read::Table,
        M::Notation(_) if parsed_as_pattern => Read::Refuses("notation-in-pattern"),
        M::Notation(_) | M::Rest if constant => Read::Refuses("constant-not-ground"),
        M::Rest if pattern => Read::Table,
        M::Rest => Read::Refuses("rest-outside-pattern"),
        _ => Read::Table,
    }
}

/// The pattern reader's rule for a construct standing for a subject's whole root: an alias, `_`
/// and a compiler-owned island stand below the root of a fn's, a table row's, a context's or a
/// static clause's subject, and a `for Sort` clause's root reads a bare name, `_`, an alias or
/// an island as a readable record's value does.
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
    (!root.at(true).admits(root_construct)).then_some(class)
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
fn product(hole: model::Position, path: &[Opening], nodes: &[model::Node]) -> Answer {
    let mut answer = Answer::default();
    for node in nodes {
        let position = hole.enter_all(&node.path);
        match reader(node.construct, position) {
            Read::Refuses(refused) => {
                answer.refused = Some(refused);
                break;
            }
            Read::Table => {}
        }
        // Where a pattern is parsed, `x | 1` is alternatives, the table's `|` row.
        let braced = position.nesting.entries.contains(Entry::Instance);
        let or_is_alternatives = position.kind == Kind::Matched
            || (position.kind == Kind::Evaluated && (position.form.writes_cells() || braced));
        let read = match node.construct {
            model::Construct::Notation(Notation::BitwiseOr) if or_is_alternatives => {
                model::Construct::Or
            }
            construct => construct,
        };
        let Some(construct) = product_construct(read) else {
            continue;
        };
        let reading = key_reading(path, node, nodes);
        match admits(product_position(position, reading), construct) {
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
    for (node, refusal) in nodes.iter().zip(oracle::refusals(hole, nodes)) {
        let position = hole.enter_all(&node.path);
        match refusal {
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
    cases.iter().filter(|case| {
        matches!(
            case.family,
            Family::Terms | Family::Import | Family::Notation
        )
    })
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
        let product = product(term.position, &term.path, &term.nodes);
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
    let known = KNOWN
        .iter()
        .map(|(pattern, finding)| (*pattern, Some(*finding)))
        .chain(NOT_RED.iter().map(|(pattern, _)| (*pattern, None)))
        .map(|(pattern, finding)| {
            let glob = Glob::parse(pattern).unwrap_or_else(|reason| panic!("{pattern}: {reason}"));
            (pattern, glob, finding)
        })
        .collect::<Vec<_>>();
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
    // the `_` in it first); the full tier checks the latter end to end, and
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
        if filed.is_some() && filed != *finding {
            misfiled.push(format!(
                "{id} ({pattern}): pending as {filed:?}, not {finding:?}"
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
/// admits a predicate, whether it is a claim (`k::or_bool!` depends on it) and whether it is a
/// `cells!` value's; each listed form shares all
/// three with the form named. A simplification's condition shares none with a claim's but the
/// first, so it is generated.
const CONDITIONS_NOT_GENERATED: [(model::Form, &str); 5] = {
    use model::Form as F;
    [
        (F::ReadableClaim, "a `cells!` claim's"),
        (F::SortRule, "a readable rule's"),
        (F::EquationTable, "an equation fn's"),
        (F::LocalRule, "a rule fn's"),
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
    for collection in [
        "k::map![",
        "map![",
        "set![",
        "[x, ..]",
        "k::builtin::set::item(",
    ] {
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
    // Every row of the collection-method catalog, written as its shape.
    let collection_shapes = krs_ir::CollectionMethod::ALL.map(|method| {
        let arguments = (1..method.arity())
            .map(|index| format!("b{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let shape = match method.spelling() {
            krs_ir::CollectionMethodSpelling::Index => format!("a[{arguments}]"),
            krs_ir::CollectionMethodSpelling::Method => {
                format!("a.{}({arguments})", method.rust_name())
            }
        };
        let notation = match method.spelling() {
            krs_ir::CollectionMethodSpelling::Index => Notation::Index,
            krs_ir::CollectionMethodSpelling::Method => Notation::CollectionMethod,
        };
        (shape, Some(notation))
    });
    let shapes = EXPRESSION_SHAPES
        .iter()
        .map(|(shape, notation)| ((*shape).to_owned(), *notation))
        .chain(collection_shapes);
    for (shape, notation) in shapes {
        let shape = shape.as_str();
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
    missing.extend(literal_forms_without_a_spelling(&spelled));
    assert!(missing.is_empty(), "without a spelling: {missing:#?}");
}

/// The collection literal shapes ([`LITERAL_SHAPES`]) without a spelling among `spelled`: the
/// product's own predicate (`krs_syntax::is_collection_literal`) is asked of each, and its model
/// form read from the call the product denotes it by: the empty collection and a set's singleton
/// are values, the other literals applications of `map::update` and `set::union`.
fn literal_forms_without_a_spelling(spelled: &BTreeSet<model::Construct>) -> Vec<String> {
    let mut missing = Vec::new();
    for shape in LITERAL_SHAPES {
        let mut expression =
            syn::parse_str::<syn::Expr>(shape).unwrap_or_else(|error| panic!("{shape}: {error}"));
        if !krs_syntax::is_collection_literal(&expression) {
            missing.push(format!(
                "the collection literal `{shape}`, which the product does not read"
            ));
            continue;
        }
        krs_syntax::denote_notation(&mut expression, &syn::parse_quote!(b));
        let syn::Expr::Call(call) = &expression else {
            panic!("{shape} denotes no call");
        };
        let syn::Expr::Path(head) = &*call.func else {
            panic!("{shape} denotes a call of no path");
        };
        let head = head
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");
        let notation = match head.as_str() {
            "b::map::update" => Notation::MapLiteral,
            "b::set::union" => Notation::SetLiteral,
            "b::map::empty" | "b::set::empty" | "b::set::item" => Notation::CollectionValue,
            other => panic!("{shape} denotes `{other}`, of no model form"),
        };
        if !spelled.contains(&model::Construct::Notation(notation)) {
            missing.push(format!("the collection literal `{shape}` ({notation:?})"));
        }
    }
    missing
}

/// The shapes of a collection literal: entries, a rest, the empty collection, a set's singleton.
const LITERAL_SHAPES: [&str; 8] = [
    "map![a -> b]",
    "k::map![a -> b, c -> d]",
    "map![a -> b, ..c]",
    "map![]",
    "set![a, b]",
    "k::set![a, ..c]",
    "set![a]",
    "set![]",
];

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
    ("a[b]", Some(Notation::Index)),
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
