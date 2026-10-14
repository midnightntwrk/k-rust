//! A collection hook reads an item or key operand declared at another sort than the collection's
//! element (key) sort as an element of the collection.
//!
//! KORE has no implicit subsorting: a collection of element sort `E` holds its elements as terms
//! of exactly `E`, a value of a strict subsort `S` being held as its injection `inj{S, E}(s)`.
//! A hooked symbol may declare its item operand (`SET.in`, `LIST.in`, `MAP.in_keys`) or its key
//! operand (`MAP.lookup`, `MAP.lookupOrDefault`, `MAP.remove`, `MAP.update`) at a sort `I` other
//! than `E`, and the application then asks about the item as the value it denotes:
//!
//! - `I` below `E`: the item `x` denotes the element `inj{I, E}(x)`, so `v in SetItem(v)` (the
//!   set holding `inj{Val, KItem}(v)`) is `true`;
//! - `E` below `I`: the item is an element only as the injection of one, so
//!   `inj{Val, KItem}(v) in valSetItem(v)` is `true`, and an item that differs from every element
//!   injected into `I` is no element;
//! - no subsort relation between `I` and `E`: no injection relates the item to the elements, so
//!   the hook does not decide the application, which stays unevaluated (never `false`, never a
//!   miss).
//!
//! The fixture declares `Small < Val < KItem` and `Int < KItem`, the builtin-named `KItem`
//! collections, collections of `Val`, and hooked symbols reading items of each relation.

use k_rust_backend::{
    definition::BackendDefinition,
    simplify::{SimplificationError, SimplificationOptions},
    term::Term,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped};

const FIXTURE: &str = r#"[]
module MAIN
  sort SortK{} []
  sort SortKItem{} []
  sort SortVal{} []
  sort SortSmall{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  symbol inj{From, To}(From) : To [sortInjection{}()]
  symbol v{}() : SortVal{} [constructor{}(), functional{}(), injective{}(), total{}()]
  symbol w{}() : SortVal{} [constructor{}(), functional{}(), injective{}(), total{}()]
  symbol s{}() : SortSmall{} [constructor{}(), functional{}(), injective{}(), total{}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortVal{}, SortKItem{}}(From:SortVal{})))
      [subsort{SortVal{}, SortKItem{}}()]
  axiom{R} \exists{R}(Value:SortVal{},
      \equals{SortVal{}, R}(Value:SortVal{}, inj{SortSmall{}, SortVal{}}(From:SortSmall{})))
      [subsort{SortSmall{}, SortVal{}}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortSmall{}, SortKItem{}}(From:SortSmall{})))
      [subsort{SortSmall{}, SortKItem{}}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
      [subsort{SortInt{}, SortKItem{}}()]

  hooked-sort SortList{}
    [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
     concat{}(Lbl'Unds'List'Unds'{}())]
  hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]

  hooked-sort SortSet{}
    [hook{}("SET.Set"), unit{}(Lbl'Stop'Set{}()), element{}(LblSetItem{}()),
     concat{}(Lbl'Unds'Set'Unds'{}())]
  hooked-symbol Lbl'Stop'Set{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol LblSetItem{}(SortKItem{}) : SortSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol Lbl'Unds'Set'Unds'{}(SortSet{}, SortSet{}) : SortSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

  hooked-sort SortMap{}
    [hook{}("MAP.Map"), unit{}(Lbl'Stop'Map{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
     concat{}(Lbl'Unds'Map'Unds'{}())]
  hooked-symbol Lbl'Stop'Map{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

  hooked-sort SortVals{}
    [hook{}("LIST.List"), unit{}(dotVals{}()), element{}(valsItem{}()), concat{}(valsConcat{}())]
  hooked-symbol dotVals{}() : SortVals{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol valsItem{}(SortVal{}) : SortVals{} [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol valsConcat{}(SortVals{}, SortVals{}) : SortVals{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]

  hooked-sort SortValSet{}
    [hook{}("SET.Set"), unit{}(dotValSet{}()), element{}(valSetItem{}()),
     concat{}(valSetConcat{}())]
  hooked-symbol dotValSet{}() : SortValSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol valSetItem{}(SortVal{}) : SortValSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol valSetConcat{}(SortValSet{}, SortValSet{}) : SortValSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

  hooked-sort SortValMap{}
    [hook{}("MAP.Map"), unit{}(dotValMap{}()), element{}(valMapItem{}()),
     concat{}(valMapConcat{}())]
  hooked-symbol dotValMap{}() : SortValMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol valMapItem{}(SortVal{}, SortVal{}) : SortValMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol valMapConcat{}(SortValMap{}, SortValMap{}) : SortValMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

  hooked-symbol inSet{}(SortKItem{}, SortSet{}) : SortBool{} [function{}(), total{}(), hook{}("SET.in")]
  hooked-symbol inList{}(SortKItem{}, SortList{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
  hooked-symbol inKeys{}(SortKItem{}, SortMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
  hooked-symbol lookup{}(SortMap{}, SortKItem{}) : SortKItem{} [function{}(), hook{}("MAP.lookup")]
  hooked-symbol lookupOrDefault{}(SortMap{}, SortKItem{}, SortKItem{}) : SortKItem{} [function{}(), total{}(), hook{}("MAP.lookupOrDefault")]
  hooked-symbol remove{}(SortMap{}, SortKItem{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.remove")]
  hooked-symbol update{}(SortMap{}, SortKItem{}, SortKItem{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.update")]

  hooked-symbol inSetOfVal{}(SortVal{}, SortSet{}) : SortBool{} [function{}(), total{}(), hook{}("SET.in")]
  hooked-symbol inListOfVal{}(SortVal{}, SortList{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
  hooked-symbol inKeysOfVal{}(SortVal{}, SortMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
  hooked-symbol lookupOfVal{}(SortMap{}, SortVal{}) : SortKItem{} [function{}(), hook{}("MAP.lookup")]
  hooked-symbol lookupOrDefaultOfVal{}(SortMap{}, SortVal{}, SortKItem{}) : SortKItem{} [function{}(), total{}(), hook{}("MAP.lookupOrDefault")]
  hooked-symbol removeOfVal{}(SortMap{}, SortVal{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.remove")]
  hooked-symbol updateOfVal{}(SortMap{}, SortVal{}, SortKItem{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.update")]

  hooked-symbol inValSetOfItem{}(SortKItem{}, SortValSet{}) : SortBool{} [function{}(), total{}(), hook{}("SET.in")]
  hooked-symbol inValsOfItem{}(SortKItem{}, SortVals{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
  hooked-symbol inValKeysOfItem{}(SortKItem{}, SortValMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
  hooked-symbol lookupValMapOfItem{}(SortValMap{}, SortKItem{}) : SortVal{} [function{}(), hook{}("MAP.lookup")]
  hooked-symbol lookupOrDefaultValMapOfItem{}(SortValMap{}, SortKItem{}, SortVal{}) : SortVal{} [function{}(), total{}(), hook{}("MAP.lookupOrDefault")]
  hooked-symbol removeValMapOfItem{}(SortValMap{}, SortKItem{}) : SortValMap{} [function{}(), total{}(), hook{}("MAP.remove")]

  hooked-symbol inValSetOfInt{}(SortInt{}, SortValSet{}) : SortBool{} [function{}(), total{}(), hook{}("SET.in")]
  hooked-symbol inValsOfInt{}(SortInt{}, SortVals{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
  hooked-symbol inValKeysOfInt{}(SortInt{}, SortValMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
  hooked-symbol lookupValMapOfInt{}(SortValMap{}, SortInt{}) : SortVal{} [function{}(), hook{}("MAP.lookup")]
  hooked-symbol lookupOrDefaultValMapOfInt{}(SortValMap{}, SortInt{}, SortVal{}) : SortVal{} [function{}(), total{}(), hook{}("MAP.lookupOrDefault")]
  hooked-symbol removeValMapOfInt{}(SortValMap{}, SortInt{}) : SortValMap{} [function{}(), total{}(), hook{}("MAP.remove")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("collection item fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("collection item fixture should internalize")
}

/// What an application simplifies to.
#[derive(Debug, PartialEq)]
enum Outcome {
    /// A value.
    Value(Term),
    /// `\bottom`.
    Bottom,
    /// The simplifier's refusal of a partial hook's application on constructor-like arguments
    /// that its evaluator left unevaluated: neither a value nor `\bottom`.
    Refused,
}

fn outcome(definition: &BackendDefinition, source: &str) -> Outcome {
    let term = internal_term(definition, source);
    match unstopped::simplify(definition, &term, SimplificationOptions::default()) {
        Ok(simplification) if simplification.undefined_term.is_some() => Outcome::Bottom,
        Ok(simplification) => Outcome::Value(simplification.term),
        Err(SimplificationError::UnsupportedHook { .. }) => Outcome::Refused,
        Err(error) => panic!("{source} failed to simplify: {error}"),
    }
}

/// The applications of `cases` whose outcome is not the expected one: a KORE value, `\bottom`
/// (`None`), the application itself (`Some("")`, unevaluated), or the refusal (`Some("!")`).
fn unexpected(definition: &BackendDefinition, cases: &[(String, Option<&str>)]) -> Vec<String> {
    cases
        .iter()
        .filter_map(|(source, expected)| {
            let expected = match expected {
                None => Outcome::Bottom,
                Some("") => Outcome::Value(internal_term(definition, source)),
                Some("!") => Outcome::Refused,
                Some(value) => Outcome::Value(internal_term(definition, value)),
            };
            let actual = outcome(definition, source);
            (actual != expected).then(|| format!("{source}\n  gave {}", describe(&actual)))
        })
        .collect()
}

fn describe(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Bottom => "\\bottom".to_owned(),
        Outcome::Refused => "the unsupported-hook refusal".to_owned(),
        Outcome::Value(term) => k_rust_backend::externalize::term(term).to_string(),
    }
}

const IV: &str = "inj{SortVal{}, SortKItem{}}(v{}())";
const IW: &str = "inj{SortVal{}, SortKItem{}}(w{}())";
const IS: &str = "inj{SortSmall{}, SortKItem{}}(s{}())";
const VS: &str = "inj{SortSmall{}, SortVal{}}(s{}())";
const TWO: &str = r#"\dv{SortInt{}}("2")"#;
const ITWO: &str = r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2"))"#;
const VSET: &str = "valSetItem{}(v{}())";
const VALS: &str = "valsItem{}(v{}())";
const VMAP: &str = "valMapItem{}(v{}(), w{}())";

fn set_of(element: &str) -> String {
    format!("LblSetItem{{}}({element})")
}

fn list_of(element: &str) -> String {
    format!("LblListItem{{}}({element})")
}

fn map_of(key: &str, value: &str) -> String {
    format!("Lbl'UndsPipe'-'-GT-Unds'{{}}({key}, {value})")
}

const TRUE: Option<&str> = Some(r#"\dv{SortBool{}}("true")"#);
const FALSE: Option<&str> = Some(r#"\dv{SortBool{}}("false")"#);
const UNEVALUATED: Option<&str> = Some("");
const REFUSED: Option<&str> = Some("!");

/// An item of a strict subsort of the element sort is the element it is injected to: a member
/// of a set or list holding that injection, a key of a map binding it, and its lookup is the
/// value bound to it. Injections compose as stored terms do: `inj{Small, Val}(s)` is the
/// element `inj{Small, KItem}(s)`.
#[test]
fn an_item_of_a_subsort_of_the_element_sort_is_read_as_its_injection() {
    let definition = definition();
    let map = map_of(IV, IW);
    let cases = [
        (format!("inSetOfVal{{}}(v{{}}(), {})", set_of(IV)), TRUE),
        (format!("inSetOfVal{{}}({VS}, {})", set_of(IS)), TRUE),
        (format!("inListOfVal{{}}(v{{}}(), {})", list_of(IV)), TRUE),
        (format!("inListOfVal{{}}({VS}, {})", list_of(IS)), TRUE),
        (format!("inKeysOfVal{{}}(v{{}}(), {map})"), TRUE),
        (format!("lookupOfVal{{}}({map}, v{{}}())"), Some(IW)),
        (
            format!("lookupOrDefaultOfVal{{}}({map}, v{{}}(), {ITWO})"),
            Some(IW),
        ),
    ];
    let unexpected = unexpected(&definition, &cases);
    assert!(
        unexpected.is_empty(),
        "an item of a subsort of the element sort was not read as its injection:\n{}",
        unexpected.join("\n")
    );
}

/// An item of a strict supersort of the element sort that is the injection of an element is
/// that element; one that differs from every element injected into its sort is no element.
#[test]
fn an_item_of_a_supersort_of_the_element_sort_is_read_as_the_element_it_injects() {
    let definition = definition();
    let cases = [
        (format!("inValSetOfItem{{}}({IV}, {VSET})"), TRUE),
        (
            format!("inValSetOfItem{{}}({IS}, valSetItem{{}}({VS}))"),
            TRUE,
        ),
        (format!("inValsOfItem{{}}({IV}, {VALS})"), TRUE),
        (format!("inValKeysOfItem{{}}({IV}, {VMAP})"), TRUE),
        (
            format!("lookupValMapOfItem{{}}({VMAP}, {IV})"),
            Some("w{}()"),
        ),
        (
            format!("lookupOrDefaultValMapOfItem{{}}({VMAP}, {IV}, v{{}}())"),
            Some("w{}()"),
        ),
        // Items that differ from each element injected into `KItem`.
        (format!("inValSetOfItem{{}}({IW}, {VSET})"), FALSE),
        (format!("inValSetOfItem{{}}({ITWO}, {VSET})"), FALSE),
        (format!("inValsOfItem{{}}({ITWO}, {VALS})"), FALSE),
        (format!("inValKeysOfItem{{}}({ITWO}, {VMAP})"), FALSE),
        (format!("lookupValMapOfItem{{}}({VMAP}, {ITWO})"), None),
        (
            format!("lookupOrDefaultValMapOfItem{{}}({VMAP}, {ITWO}, v{{}}())"),
            Some("v{}()"),
        ),
        // A symbolic item may be any element.
        (
            format!("inValSetOfItem{{}}(X:SortKItem{{}}, {VSET})"),
            UNEVALUATED,
        ),
        // An opaque rest may hold any element, so absence is not decided.
        (
            format!("inValSetOfItem{{}}({ITWO}, valSetConcat{{}}({VSET}, R:SortValSet{{}}))"),
            UNEVALUATED,
        ),
        (
            format!("inValsOfItem{{}}({ITWO}, valsConcat{{}}({VALS}, R:SortVals{{}}))"),
            UNEVALUATED,
        ),
        (
            format!("inValKeysOfItem{{}}({ITWO}, valMapConcat{{}}({VMAP}, R:SortValMap{{}}))"),
            UNEVALUATED,
        ),
        (
            format!(
                "lookupOrDefaultValMapOfItem{{}}(valMapConcat{{}}({VMAP}, R:SortValMap{{}}), \
                 {ITWO}, v{{}}())"
            ),
            UNEVALUATED,
        ),
        // A symbolic element: `inj{Val, KItem}(X)` and `inj{Int, KItem}(2)` are apart (`Val`
        // and `Int` share no subsort), so the `Int` item is no element; the `Small` item injects
        // a `Val`, which `X` may be.
        (
            format!("inValSetOfItem{{}}({ITWO}, valSetItem{{}}(X:SortVal{{}}))"),
            FALSE,
        ),
        (
            format!("inValSetOfItem{{}}({IS}, valSetItem{{}}(X:SortVal{{}}))"),
            UNEVALUATED,
        ),
    ];
    let unexpected = unexpected(&definition, &cases);
    assert!(
        unexpected.is_empty(),
        "an item of a supersort of the element sort was not read as the element it injects:\n{}",
        unexpected.join("\n")
    );
}

/// No injection relates an item of a sort that is neither below nor above the element sort to
/// the elements, so the hook decides nothing: no `false`, no `\bottom`, no default.
#[test]
fn an_item_of_a_sort_unrelated_to_the_element_sort_leaves_the_hook_unevaluated() {
    let definition = definition();
    let cases = [
        (format!("inValSetOfInt{{}}({TWO}, {VSET})"), UNEVALUATED),
        (format!("inValsOfInt{{}}({TWO}, {VALS})"), UNEVALUATED),
        (format!("inValKeysOfInt{{}}({TWO}, {VMAP})"), UNEVALUATED),
        // `MAP.lookup` is partial: its application on constructor-like arguments that the
        // evaluator leaves unevaluated is refused rather than taken as a value.
        (format!("lookupValMapOfInt{{}}({VMAP}, {TWO})"), REFUSED),
        (
            format!("lookupOrDefaultValMapOfInt{{}}({VMAP}, {TWO}, v{{}}())"),
            UNEVALUATED,
        ),
        (format!("removeValMapOfInt{{}}({VMAP}, {TWO})"), UNEVALUATED),
    ];
    let unexpected = unexpected(&definition, &cases);
    assert!(
        unexpected.is_empty(),
        "a hook decided an item of a sort unrelated to the element sort:\n{}",
        unexpected.join("\n")
    );
}

/// Pins: items of the element sort itself, the absent items of every relation, and the hooks that
/// build a map (`MAP.remove`, `MAP.update`), which store a subsort key injected.
#[test]
fn items_of_the_element_sort_and_absent_items_keep_their_values() {
    let definition = definition();
    let map = map_of(IV, IW);
    let updated = map_of(IV, ITWO);
    let cases = [
        (format!("inSet{{}}({IV}, {})", set_of(IV)), TRUE),
        (format!("inSet{{}}({IW}, {})", set_of(IV)), FALSE),
        (format!("inList{{}}({IV}, {})", list_of(IV)), TRUE),
        (format!("inList{{}}({IW}, {})", list_of(IV)), FALSE),
        (format!("inKeys{{}}({IV}, {map})"), TRUE),
        (format!("inKeys{{}}({IW}, {map})"), FALSE),
        (format!("lookup{{}}({map}, {IV})"), Some(IW)),
        (format!("lookup{{}}({map}, {IW})"), None),
        (
            format!("lookupOrDefault{{}}({map}, {IW}, {ITWO})"),
            Some(ITWO),
        ),
        (format!("remove{{}}({map}, {IV})"), Some("Lbl'Stop'Map{}()")),
        (format!("update{{}}({map}, {IV}, {ITWO})"), Some(&*updated)),
        (format!("inSetOfVal{{}}(w{{}}(), {})", set_of(IV)), FALSE),
        (format!("inListOfVal{{}}(w{{}}(), {})", list_of(IV)), FALSE),
        (format!("inKeysOfVal{{}}(w{{}}(), {map})"), FALSE),
        (format!("lookupOfVal{{}}({map}, w{{}}())"), None),
        (
            format!("lookupOrDefaultOfVal{{}}({map}, w{{}}(), {ITWO})"),
            Some(ITWO),
        ),
        (
            format!("removeOfVal{{}}({map}, v{{}}())"),
            Some("Lbl'Stop'Map{}()"),
        ),
        (format!("removeOfVal{{}}({map}, w{{}}())"), Some(&*map)),
        (
            format!("updateOfVal{{}}({map}, v{{}}(), {ITWO})"),
            Some(&*updated),
        ),
        (
            format!("inSetOfVal{{}}(X:SortVal{{}}, {})", set_of(IV)),
            UNEVALUATED,
        ),
    ];
    let unexpected = unexpected(&definition, &cases);
    assert!(
        unexpected.is_empty(),
        "a collection hook changed its value on items of the element sort or absent items:\n{}",
        unexpected.join("\n")
    );
}
