//! The grammar graph of a definition's named symbols ([`grammar_graph`]), the universe of
//! kink-flow's syntax paths.
//!
//! A syntax path `(P1, i1, P2, ..., Pn)` is a sequence of named symbols along consecutive
//! argument positions, `P(j+1)` the head, through injections, of argument `ij` of `Pj`'s
//! application ([`super::SyntaxPath`], k-rust `bindings.paths`). A well-sorted term holds an
//! application of `Q` at argument `i` of an application of `P` either directly, where `Q`'s
//! result sort is the sort of `P`'s argument `i`, or below an injection of `Q`'s result sort into
//! it, which the definition admits only where that sort is a subsort of the argument's. So `Q`
//! can follow `P` at `i` only where `Q`'s result sort is at or below the sort of `P`'s argument
//! `i`, and every path a run records is a walk of the graph whose edges are those triples
//! `(P, i, Q)`. The graph over-approximates the paths a run can take: it reads sorts alone, so a
//! triple no rule ever builds or matches is an edge too. An argument of a collection sort or a
//! builtin sort holds no named symbol of an authored sort, so it has no edge: a collection's
//! elements and a builtin value are no part of a path through it. Where the sort graph cannot
//! tell whether one sort is below another, the edge is kept, so the graph never omits a path.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_backend::definition::BackendDefinition;

/// The grammar graph of a set of named symbols (module documentation): per symbol, per argument
/// position, the named symbols whose applications may stand there.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GrammarGraph {
    arguments: BTreeMap<String, Vec<BTreeSet<String>>>,
}

/// No argument.
static NO_ARGUMENTS: [BTreeSet<String>; 0] = [];

impl GrammarGraph {
    /// The symbols, by KORE name, in name order: those of the set the definition declares.
    pub fn symbols(&self) -> impl Iterator<Item = &str> {
        self.arguments.keys().map(String::as_str)
    }

    /// Per argument position of `symbol`, the symbols that may stand there; empty for a symbol
    /// the graph does not hold.
    #[must_use]
    pub fn arguments(&self, symbol: &str) -> &[BTreeSet<String>] {
        self.arguments
            .get(symbol)
            .map_or(&NO_ARGUMENTS, Vec::as_slice)
    }

    /// The number of edges `(P, i, Q)`.
    #[must_use]
    pub fn edges(&self) -> usize {
        self.arguments.values().flatten().map(BTreeSet::len).sum()
    }
}

/// The grammar graph of the named symbols `symbols` of `definition` (module documentation): a
/// symbol the definition does not declare is left out, and `Q` stands at argument `i` of `P`
/// unless the sort graph says `Q`'s result sort is not below the sort of `P`'s argument `i`.
#[must_use]
pub fn grammar_graph(definition: &BackendDefinition, symbols: &BTreeSet<String>) -> GrammarGraph {
    let declared = definition
        .symbols()
        .iter()
        .filter(|(name, _)| symbols.contains(&***name))
        .map(|(_, symbol)| symbol)
        .collect::<Vec<_>>();
    let graph = definition.sort_graph();
    let arguments = declared
        .iter()
        .map(|symbol| {
            let positions = symbol
                .argument_sorts
                .iter()
                .map(|sort| {
                    declared
                        .iter()
                        .filter(|inner| graph.check_subsort(&inner.result_sort, sort) != Ok(false))
                        .map(|inner| inner.name.to_string())
                        .collect()
                })
                .collect();
            (symbol.name.to_string(), positions)
        })
        .collect();
    GrammarGraph { arguments }
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::kore::parser::parse_definition;

    /// `Q` stands at an argument of a sort it is at or below, through the subsort `Exp < Stmt`,
    /// and nowhere else: not at an `Int` argument, not at a `K` argument (whose values are `K`
    /// sequences, not items), and a symbol outside the set is no node.
    #[test]
    fn a_symbol_follows_another_at_an_argument_its_sort_is_below() {
        let source = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            sort SortKItem{} []
            sort SortK{} []
            sort SortExp{} []
            sort SortStmt{} []
            symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
            symbol dotk{}() : SortK{} [constructor{}(), functional{}(), injective{}()]
            symbol inj{From, To}(From) : To [sortInjection{}()]
            axiom{R} \exists{R}(Val:SortStmt{}, \equals{SortStmt{}, R}(Val:SortStmt{}, inj{SortExp{}, SortStmt{}}(From:SortExp{}))) [subsort{SortExp{}, SortStmt{}}()]
            axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{}, R}(Val:SortKItem{}, inj{SortStmt{}, SortKItem{}}(From:SortStmt{}))) [subsort{SortStmt{}, SortKItem{}}()]
            symbol Lbllit{}(SortInt{}) : SortExp{} [constructor{}(), functional{}(), injective{}()]
            symbol Lbladd{}(SortExp{}, SortExp{}) : SortExp{} [constructor{}(), functional{}(), injective{}()]
            symbol Lblexpr{}(SortStmt{}) : SortStmt{} [constructor{}(), functional{}(), injective{}()]
            symbol Lblblock{}(SortK{}) : SortStmt{} [constructor{}(), functional{}(), injective{}()]
            symbol Lblother{}(SortExp{}) : SortExp{} [constructor{}(), functional{}(), injective{}()]
        endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let symbols = ["Lbllit", "Lbladd", "Lblexpr", "Lblblock"]
            .map(str::to_owned)
            .into_iter()
            .collect();
        let grammar = grammar_graph(&definition, &symbols);
        let set = |names: &[&str]| {
            names
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(
            grammar.symbols().collect::<Vec<_>>(),
            ["Lbladd", "Lblblock", "Lblexpr", "Lbllit"]
        );
        assert_eq!(grammar.arguments("Lbllit"), [set(&[])]);
        assert_eq!(
            grammar.arguments("Lbladd"),
            [set(&["Lbladd", "Lbllit"]), set(&["Lbladd", "Lbllit"])]
        );
        assert_eq!(
            grammar.arguments("Lblexpr"),
            [set(&["Lbladd", "Lblblock", "Lblexpr", "Lbllit"])]
        );
        assert_eq!(grammar.arguments("Lblblock"), [set(&[])]);
        assert!(grammar.arguments("Lblother").is_empty());
        assert_eq!(grammar.edges(), 8);
    }
}
