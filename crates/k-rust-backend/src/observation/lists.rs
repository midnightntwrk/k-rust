//! Source-owned fixed list prefix observations. A view retains the original source domain;
//! its generated tail uses LIST.range's front/back removal counts, not slice endpoints.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::names::BuiltinSort;
use num_traits::ToPrimitive;

use crate::{
    definition::BackendDefinition,
    rule::{ClassifiedAxiom, Predicate, TermIndex},
    smt::{SExpr, SmtType},
    term::{
        CollectionMetadata, DomainKind, FunctionType, HeadRole, ListDefinition, Sort, Symbol,
        SymbolType, Term, TermKind,
    },
};

use super::reading::Reading;

const PREFIX_LIMIT: usize = 128;

#[derive(Clone, Debug)]
pub(crate) struct Operations {
    pub collection: Arc<ListDefinition>,
    symbols: Vec<Arc<Symbol>>,
}

impl Operations {
    fn of(definition: &BackendDefinition, collection: Arc<ListDefinition>) -> Option<Self> {
        if definition.classified_axioms().len() > 16_384 || definition.symbols().len() > 16_384 {
            return None;
        }
        definition.equation_selection_complete()?;
        let effects = definition.console_effect_symbols()?;
        if [
            definition.function_theory(),
            definition.simplification_theory(),
            definition.ceil_theory(),
        ]
        .into_iter()
        .any(|t| t.contains_key(&TermIndex::Variable) || t.contains_key(&TermIndex::And))
        {
            return None;
        }
        let mut changed = BTreeSet::new();
        for axiom in definition.classified_axioms() {
            let lhs = match axiom {
                ClassifiedAxiom::Function { lhs, .. }
                | ClassifiedAxiom::Simplification { lhs, .. }
                | ClassifiedAxiom::Ceil { lhs, .. } => lhs,
                ClassifiedAxiom::Rewrite { .. } => continue,
            };
            if let k_rust_kore::kore::ast::Pattern::Application { symbol, .. } = lhs {
                changed.insert(symbol.name.as_str());
            }
        }
        for name in [
            &collection.symbols.unit,
            &collection.symbols.element,
            &collection.symbols.concat,
        ] {
            let symbol = definition.symbols().get(name)?;
            // Standard list roles carry smtlib declarations. The internal list value
            // bypasses those role applications; a declaration supplies no extra law.
            if changed.contains(name.as_ref())
                || effects.contains(name.as_ref())
                || symbol.attributes.binder
                || symbol.attributes.macro_or_alias
                || symbol
                    .attributes
                    .smt
                    .as_ref()
                    .is_some_and(|s| !matches!(s, SmtType::Lib(_)))
            {
                return None;
            }
        }
        let symbols = definition
            .symbols()
            .values()
            .filter(|symbol| {
                matches!(
                    symbol.attributes.head_role(),
                    HeadRole::Function { declared: true, .. }
                ) && !symbol.attributes.binder
                    && !symbol.attributes.macro_or_alias
                    && !effects.contains(symbol.name.as_ref())
                    && !changed.contains(symbol.name.as_ref())
                    && (!matches!(
                        symbol.attributes.hook.as_deref(),
                        Some("LIST.get" | "LIST.range")
                    ) || symbol.attributes.symbol_type
                        == SymbolType::Function(FunctionType::Partial))
                    && (symbol.sort_variables.is_empty()
                        || symbol.attributes.hook.as_deref() == Some("KEQUAL.ite"))
                    && matches!(
                        symbol.attributes.hook.as_deref(),
                        Some(
                            "LIST.get"
                                | "LIST.range"
                                | "LIST.size"
                                | "INT.ge"
                                | "INT.add"
                                | "INT.sub"
                                | "KEQUAL.ite"
                        )
                    )
            })
            .cloned()
            .collect();
        Some(Self {
            collection,
            symbols,
        })
    }

    fn sort(&self) -> Sort {
        Sort::simple(self.collection.list_sort.clone())
    }

    fn admits(&self, term: &Term, hook: &str) -> bool {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            return false;
        };
        if !self.symbols.contains(symbol)
            || symbol.attributes.hook.as_deref() != Some(hook)
            || sort_arguments.len() != symbol.sort_variables.len()
            || sort_arguments.iter().any(Sort::has_variable)
        {
            return false;
        }
        let bindings = symbol
            .sort_variables
            .iter()
            .cloned()
            .zip(sort_arguments.iter().copied())
            .collect();
        symbol.argument_sorts.len() == arguments.len()
            && symbol
                .argument_sorts
                .iter()
                .zip(arguments)
                .all(|(s, a)| crate::definition::substitute_sort(s, &bindings) == a.sort())
    }

    fn call(&self, hook: &str, arguments: Vec<Term>, result: Sort) -> Option<Term> {
        let symbol = self.symbols.iter().find(|s| {
            s.sort_variables.is_empty()
                && s.attributes.hook.as_deref() == Some(hook)
                && s.result_sort == result
                && s.argument_sorts
                    .iter()
                    .copied()
                    .eq(arguments.iter().map(Term::sort))
        })?;
        Some(Term::application(symbol.clone(), vec![], arguments))
    }

    pub fn get(&self, list: Term, index: usize) -> Option<Term> {
        (list.sort() == self.sort() && index < PREFIX_LIMIT).then_some(())?;
        self.call(
            "LIST.get",
            vec![list, Term::int(index)],
            self.collection.element_sort,
        )
    }

    pub fn tail(&self, list: Term, count: usize) -> Option<Term> {
        (list.sort() == self.sort() && count <= PREFIX_LIMIT).then_some(())?;
        self.call(
            "LIST.range",
            vec![list, Term::int(count), Term::int(0)],
            self.sort(),
        )
    }

    fn size(&self, list: Term) -> Option<Term> {
        (list.sort() == self.sort()).then_some(())?;
        let term = self.call("LIST.size", vec![list], Sort::builtin(BuiltinSort::Int))?;
        let TermKind::Application { symbol, .. } = term.kind() else {
            unreachable!();
        };
        (symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total)).then_some(term)
    }

    fn scalar(
        &self,
        hook: &str,
        operator: &str,
        arguments: Vec<Term>,
        result: Sort,
    ) -> Option<Term> {
        let term = self.call(hook, arguments, result)?;
        let TermKind::Application { symbol, .. } = term.kind() else {
            unreachable!();
        };
        (symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total)
            && matches!(&symbol.attributes.smt, Some(SmtType::Hook(SExpr::Atom(op))) if op == operator)).then_some(term)
    }

    fn length_at_least(&self, list: Term, count: usize) -> Option<Predicate> {
        Some(Predicate::Term(self.scalar(
            "INT.ge",
            ">=",
            vec![self.size(list)?, Term::int(count)],
            Sort::builtin(BuiltinSort::Bool),
        )?))
    }

    fn get_parts<'a>(&self, term: &'a Term) -> Option<(&'a Term, usize)> {
        let TermKind::Application { arguments, .. } = term.kind() else {
            return None;
        };
        let [list, index] = arguments.as_slice() else {
            return None;
        };
        (self.admits(term, "LIST.get")
            && list.sort() == self.sort()
            && term.sort() == self.collection.element_sort)
            .then_some(())?;
        let index = fixed(index)?;
        (index < PREFIX_LIMIT).then_some((list, index))
    }

    pub(crate) fn demanded_prefix<'a>(&self, term: &'a Term) -> Option<(&'a Term, usize)> {
        let (list, index) = self.get_parts(term)?;
        Some((list, index + 1))
    }

    fn tail_parts<'a>(&self, term: &'a Term) -> Option<(&'a Term, usize)> {
        let TermKind::Application { arguments, .. } = term.kind() else {
            return None;
        };
        let [list, front, back] = arguments.as_slice() else {
            return None;
        };
        (self.admits(term, "LIST.range")
            && list.sort() == self.sort()
            && term.sort() == self.sort()
            && fixed(back) == Some(0))
        .then_some(())?;
        Some((list, fixed(front)?))
    }

    pub fn prefix(&self, list: Term, count: usize) -> Option<Term> {
        if count == 0 || count > PREFIX_LIMIT {
            return None;
        }
        let heads = (0..count)
            .map(|i| self.get(list.clone(), i))
            .collect::<Option<Vec<_>>>()?;
        Some(Term::list(
            self.collection.clone(),
            heads,
            Some((self.tail(list, count)?, vec![])),
        ))
    }

    /// The zero-length list law, guarded by the original value's domain. This is a
    /// source consequence, never a proposed replacement domain for an opaque function.
    pub(crate) fn empty_fact(&self, list: &Term) -> Option<Predicate> {
        Some(Predicate::Implies(
            Arc::new(Predicate::And(
                vec![
                    Predicate::Ceil(list.clone()),
                    Predicate::Equals(self.size(list.clone())?, Term::int(0)),
                ]
                .into(),
            )),
            Arc::new(Predicate::Equals(
                list.clone(),
                Term::list(self.collection.clone(), vec![], None),
            )),
        ))
    }

    fn reconstruction(&self, definition: &BackendDefinition, term: &Term) -> Option<Term> {
        let TermKind::List {
            definition: collection,
            heads,
            rest: Some((tail, tails)),
        } = term.kind()
        else {
            return None;
        };
        if collection != &self.collection
            || heads.is_empty()
            || heads.len() > PREFIX_LIMIT
            || !tails.is_empty()
        {
            return None;
        }
        let (base, count) = self.tail_parts(tail)?;
        if count != heads.len() {
            return None;
        }
        for (index, head) in heads.iter().enumerate() {
            let raw = super::reading::stored_reconstruction(definition, head)
                .unwrap_or_else(|| head.clone());
            if raw != self.get(base.clone(), index)? {
                return None;
            }
        }
        Some(base.clone())
    }

    pub(super) fn reading(
        &self,
        definition: &BackendDefinition,
        term: &Term,
    ) -> Option<Arc<Reading>> {
        if let Some(base) = self.reconstruction(definition, term) {
            return Some(Arc::new(Reading::Leaf(base)));
        }
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            return None;
        };
        let hook = symbol.attributes.hook.as_deref()?;
        let (input, offset) = match hook {
            "LIST.get" => self.get_parts(term)?,
            "LIST.range" => self.tail_parts(term)?,
            "LIST.size"
                if self.admits(term, hook)
                    && arguments.len() == 1
                    && arguments[0].sort() == self.sort()
                    && term.sort().is_builtin(BuiltinSort::Int) =>
            {
                (&arguments[0], 0)
            }
            _ => return None,
        };
        if let TermKind::Application {
            arguments: branches,
            ..
        } = input.kind()
            && self.admits(input, "KEQUAL.ite")
            && let [test, yes, no] = branches.as_slice()
            && test.sort().is_builtin(BuiltinSort::Bool)
            && yes.sort() == self.sort()
            && no.sort() == self.sort()
        {
            let branch = |value: &Term| {
                let mut actual = arguments.clone();
                actual[0] = value.clone();
                Arc::new(Reading::Leaf(Term::application(
                    symbol.clone(),
                    *sort_arguments,
                    actual,
                )))
            };
            return Some(Arc::new(Reading::If {
                test: Predicate::Term(test.clone()),
                yes: branch(yes),
                no: branch(no),
            }));
        }
        let value = if let Some((base, count)) = self.tail_parts(input) {
            match hook {
                "LIST.get" => self.get(base.clone(), count.checked_add(offset)?)?,
                "LIST.range" => self.tail(base.clone(), count.checked_add(offset)?)?,
                "LIST.size" => self.scalar(
                    "INT.sub",
                    "-",
                    vec![self.size(base.clone())?, Term::int(count)],
                    Sort::builtin(BuiltinSort::Int),
                )?,
                _ => return None,
            }
        } else if let TermKind::List {
            definition: collection,
            heads,
            rest,
        } = input.kind()
        {
            if collection != &self.collection {
                return None;
            }
            match hook {
                "LIST.get" => {
                    if let Some(head) = heads.get(offset) {
                        head.clone()
                    } else if let Some((base, tails)) = rest {
                        if !tails.is_empty() {
                            return None;
                        }
                        self.get(base.clone(), offset - heads.len())?
                    } else {
                        return Some(Arc::new(Reading::Missing));
                    }
                }
                "LIST.range" if offset <= heads.len() => Term::list_of_items(
                    self.collection.clone(),
                    heads.split_at(offset).1,
                    rest.clone(),
                ),
                "LIST.size" => {
                    let count = heads.len() + rest.as_ref().map_or(0, |(_, tails)| tails.len());
                    if let Some((base, _)) = rest {
                        self.scalar(
                            "INT.add",
                            "+",
                            vec![Term::int(count), self.size(base.clone())?],
                            Sort::builtin(BuiltinSort::Int),
                        )?
                    } else {
                        Term::int(count)
                    }
                }
                _ => return None,
            }
        } else {
            return None;
        };
        Some(Arc::new(Reading::Leaf(value)))
    }
}

fn fixed(term: &Term) -> Option<usize> {
    let value = crate::builtin::read_int(term)?.to_usize()?;
    (value <= PREFIX_LIMIT).then_some(value)
}

/// Exact deterministic prefix/rest region for distinct typed element variables.
/// Unsupported value patterns decline; a failed candidate never refutes another match.
pub(crate) fn match_view(
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
) -> crate::stop::Stoppable<Option<(Term, Vec<Predicate>)>> {
    let TermKind::List {
        definition: collection,
        heads,
        rest: Some((rest, tails)),
    } = pattern.kind()
    else {
        return Ok(None);
    };
    if heads.is_empty()
        || heads.len() > PREFIX_LIMIT
        || !tails.is_empty()
        || !matches!(rest.kind(),TermKind::Variable(v) if v.kind == crate::term::VariableKind::Element)
        || !pattern
            .attributes()
            .variables
            .is_disjoint(&subject.attributes().variables)
        || subject.sort() != pattern.sort()
    {
        return Ok(None);
    }
    let Some(ops) = definition.list_operations(&subject.sort()) else {
        return Ok(None);
    };
    if collection != &ops.collection || !super::reading::Builder::new(definition).pure(subject)? {
        return Ok(None);
    }
    let mut variables = BTreeSet::new();
    for item in heads.iter().chain(std::iter::once(rest)) {
        if item.attributes().variables.len() != 1
            || !item
                .attributes()
                .variables
                .iter()
                .all(|v| variables.insert(v.clone()))
        {
            return Ok(None);
        }
    }
    let mut values = Vec::with_capacity(heads.len());
    for (index, head) in heads.iter().enumerate() {
        crate::stop::check()?;
        let Some(raw) = ops.get(subject.clone(), index) else {
            return Ok(None);
        };
        let Some(value) = super::variable_observation(definition, head, &raw) else {
            return Ok(None);
        };
        values.push(value);
    }
    let Some(tail) = ops.tail(subject.clone(), heads.len()) else {
        return Ok(None);
    };
    let witness = Term::list(collection.clone(), values, Some((tail, vec![])));
    // Keep reconstruction as an obligation against the original path, alongside all
    // typed/head/tail domains. No subject variable is bound to the decomposition.
    let mut guards = vec![
        Predicate::Ceil(witness.clone()),
        Predicate::Ceil(subject.clone()),
    ];
    guards.push(Predicate::Equals(witness.clone(), subject.clone()));
    Ok(Some((witness, guards)))
}

impl BackendDefinition {
    pub(crate) fn list_operations(&self, sort: &Sort) -> Option<&Operations> {
        self.value_claims().admit_at(
            self,
            &TermIndex::List,
            crate::confluence::GateSite::Collection,
        )?;
        if let Some(operations) = self.list_observations.get() {
            return operations.get(sort);
        }
        self.console_effect_symbols()?;
        self.equation_selection_complete()?;
        if self.domain_kind(&Sort::builtin(BuiltinSort::Int)) != Some(DomainKind::Int)
            || self.domain_kind(&Sort::builtin(BuiltinSort::Bool)) != Some(DomainKind::Bool)
        {
            return None;
        }
        self.list_observations
            .get_or_init(|| {
                let collections = self
                    .symbols()
                    .values()
                    .filter_map(|s| match s.attributes.collection.as_ref()? {
                        CollectionMetadata::List(list) => {
                            Some((Sort::simple(list.list_sort.clone()), list.clone()))
                        }
                        _ => None,
                    })
                    .collect::<BTreeMap<_, _>>();
                collections
                    .into_iter()
                    .filter_map(|(sort, list)| Some((sort, Operations::of(self, list)?)))
                    .collect()
            })
            .get(sort)
    }
}

/// Only the selected fixed nonnegative index and front-removal domains are exposed here.
/// The canonical caller retains every original strict operand's domain.
///
/// On a defined `L`, `L[i]` is defined exactly when `0 <= i < size(L)` and `range(L, k, 0)` exactly when `0 <= k <= size(L)`.
/// For the nonnegative literals admitted here, `size(L) >=Int i + 1` and `size(L) >=Int k` are therefore exactly their definedness
/// (kink27 R2-DOMAIN-ROUTES).
pub(crate) fn domain(definition: &BackendDefinition, term: &Term) -> Option<Vec<Predicate>> {
    let TermKind::Application { arguments, .. } = term.kind() else {
        return None;
    };
    let input = arguments.first()?;
    let ops = definition.list_operations(&input.sort())?;
    let (list, count) = if let Some((list, index)) = ops.get_parts(term) {
        (list, index + 1)
    } else {
        ops.tail_parts(term)?
    };
    Some(vec![ops.length_at_least(list.clone(), count)?])
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    const SOURCE: &str = r#"[] module MAIN
      hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
      hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
      hooked-sort SortList{} [hook{}("LIST.List"),unit{}(unit{}()),element{}(item{}()),concat{}(concat{}())]
      hooked-symbol unit{}() : SortList{} [function{}(),total{}(),hook{}("LIST.unit"),smtlib{}("list_nil")]
      hooked-symbol item{}(SortInt{}) : SortList{} [function{}(),total{}(),hook{}("LIST.element"),smtlib{}("list_item")]
      hooked-symbol concat{}(SortList{},SortList{}) : SortList{} [function{}(),total{}(),hook{}("LIST.concat"),assoc{}(),smtlib{}("list_concat")]
      hooked-symbol get{}(SortList{},SortInt{}) : SortInt{} [function{}(),hook{}("LIST.get")]
      hooked-symbol range{}(SortList{},SortInt{},SortInt{}) : SortList{} [function{}(),hook{}("LIST.range")]
      hooked-symbol size{}(SortList{}) : SortInt{} [function{}(),total{}(),hook{}("LIST.size"),smtlib{}("length")]
      hooked-symbol ge{}(SortInt{},SortInt{}) : SortBool{} [function{}(),total{}(),hook{}("INT.ge"),smt-hook{}(">=")]
      hooked-symbol add{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}(),hook{}("INT.add"),smt-hook{}("+")]
      hooked-symbol sub{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}(),hook{}("INT.sub"),smt-hook{}("-")]
      hooked-symbol choose{S}(SortBool{},S,S) : S [function{}(),total{}(),hook{}("KEQUAL.ite"),smt-hook{}("ite")]
      symbol partial{}() : SortList{} [function{}()]
      symbol context{}(SortList{}) : SortInt{} [function{}()]
    endmodule []"#;

    fn load(source: &str) -> BackendDefinition {
        BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, text: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(text).unwrap(), &[])
            .unwrap()
    }

    #[cfg(feature = "z3")]
    fn typed_source() -> String {
        SOURCE.replace("item{}(SortInt{})","item{}(SortKItem{})")
            .replace("get{}(SortList{},SortInt{}) : SortInt{}","get{}(SortList{},SortInt{}) : SortKItem{}")
            .replace("endmodule",r#"
              sort SortKItem{} [] sort SortK{} []
              symbol inj{From,To}(From) : To [sortInjection{}()]
              symbol kseq{}(SortKItem{},SortK{}) : SortK{} [constructor{}()]
              symbol dotk{}() : SortK{} [constructor{}()]
              symbol project{}(SortK{}) : SortInt{} [function{}()]
              axiom{R} \exists{R}(V:SortKItem{},\equals{SortKItem{},R}(V:SortKItem{},inj{SortInt{},SortKItem{}}(X:SortInt{}))) [subsort{SortInt{},SortKItem{}}()]
              axiom{R} \implies{R}(\and{R}(\top{R}(),\and{R}(\in{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}())),\top{R}())),
                \equals{SortInt{},R}(project{}(X:SortK{}),\and{SortInt{}}(Y:SortInt{},\top{SortInt{}}()))) []
              axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(project{}(X:SortK{})),
                \exists{R}(Y:SortInt{},\equals{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}()))))) []
              axiom{R} \implies{R}(\ceil{SortInt{},R}(project{}(Z:SortK{})),
                \equals{SortK{},R}(kseq{}(inj{SortInt{},SortKItem{}}(project{}(Z:SortK{})),dotk{}()),\and{SortK{}}(Z:SortK{},\top{SortK{}}()))) [simplification{}()]
            endmodule"#)
    }

    #[cfg(feature = "z3")]
    #[test]
    fn typed_head_values_transport_into_concrete_prefixes_without_explicit_inverse_syntax() {
        use crate::{
            smt::{SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
        };
        let definition = load(&typed_source());
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let list = term(&definition, "L:SortList{}");
        for count in [1, 2] {
            let mut known = Vec::new();
            let mut heads = Vec::new();
            for index in 0..count {
                let typed = definition
                    .observe_stored(
                        &ops.get(list.clone(), index).unwrap(),
                        &Sort::simple("SortInt"),
                    )
                    .unwrap();
                known.push(Predicate::Ceil(typed.clone()));
                known.push(Predicate::Equals(typed, Term::int(index + 1)));
                heads.push(Term::injection(
                    Sort::simple("SortInt"),
                    ops.collection.element_sort,
                    Term::int(index + 1),
                ));
            }
            let rebuilt = Term::list(
                ops.collection.clone(),
                heads,
                Some((ops.tail(list.clone(), count).unwrap(), vec![])),
            );
            assert_eq!(
                Z3Solver::new(&definition)
                    .unwrap()
                    .check_predicates(
                        &known,
                        &Substitution::new(),
                        &[Predicate::Equals(list.clone(), rebuilt)]
                    )
                    .unwrap()
                    .unwrap(),
                Validity::Valid,
                "prefix {count}"
            );
        }
    }

    #[test]
    #[ignore = "set LIST_AUDIT_KORE and LIST_AUDIT_MODULE to actual compiler output"]
    fn actual_compiler_list_roles_and_typed_witnesses_are_admitted() {
        let source = std::fs::read_to_string(std::env::var("LIST_AUDIT_KORE").unwrap()).unwrap();
        let definition = BackendDefinition::internalize(
            &parse_definition(&source).unwrap(),
            &std::env::var("LIST_AUDIT_MODULE").unwrap(),
        )
        .unwrap();
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let list = term(&definition, "L:SortList{}");
        let head = ops.get(list.clone(), 0).unwrap();
        assert!(ops.tail(list.clone(), 1).is_some());
        assert!(domain(&definition, &head).is_some());
        assert!(
            definition
                .observe_stored(&head, &Sort::simple("SortInt"))
                .is_some()
        );
        let prefix = ops.prefix(list.clone(), 1).unwrap();
        assert_eq!(ops.reconstruction(&definition, &prefix), Some(list.clone()));
        let mut pending = definition
            .rewrite_theory()
            .values()
            .flat_map(|g| g.values())
            .flatten()
            .map(|r| r.lhs.clone())
            .collect::<Vec<_>>();
        let mut tested = 0;
        while let Some(pattern) = pending.pop() {
            if matches!(pattern.kind(),TermKind::List { heads, rest: Some(_), .. } if !heads.is_empty())
            {
                let view = match_view(&definition, &pattern, &list).unwrap();
                assert!(view.is_some(), "actual rule prefix declined: {pattern:?}");
                let (witness, _) = view.unwrap();
                assert!(matches!(
                    crate::matching::match_terms_in_definition(
                        crate::matching::MatchMode::Rewrite,
                        &definition,
                        &pattern,
                        &witness
                    ),
                    crate::matching::MatchResult::Success(_)
                ));
                tested += 1;
            }
            pending.extend(crate::deferred::children(&pattern).into_iter().cloned());
        }
        assert!(
            tested > 0,
            "actual source must include a prefix-consuming rewrite"
        );
    }

    #[test]
    fn fixed_prefixes_use_actual_hooks_and_front_removal_counts() {
        let definition = load(SOURCE);
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let list = term(&definition, "L:SortList{}");
        for count in [1, 2, 8, 128] {
            let prefix = ops.prefix(list.clone(), count).unwrap();
            assert_eq!(ops.reconstruction(&definition, &prefix), Some(list.clone()));
            let reading = super::super::reading::Builder::new(&definition)
                .of(&prefix)
                .unwrap()
                .unwrap();
            assert_eq!(reading.as_ref(), &Reading::Leaf(list.clone()));
        }
        assert!(ops.prefix(list.clone(), 129).is_none());
        assert!(ops.prefix(list, 0).is_none());
        assert!(
            domain(
                &definition,
                &term(&definition, r#"get{}(L:SortList{},\dv{SortInt{}}("-1"))"#)
            )
            .is_none()
        );
        assert!(
            domain(
                &definition,
                &term(
                    &definition,
                    r#"range{}(L:SortList{},\dv{SortInt{}}("0"),\dv{SortInt{}}("1"))"#
                )
            )
            .is_none()
        );
    }

    #[test]
    fn source_changes_decline_only_the_affected_contract() {
        let extra_value = SOURCE.replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(get{}(L:SortList{},I:SortInt{}),\and{SortInt{}}(\dv{SortInt{}}("9"),\top{SortInt{}}()))) [simplification{}()] endmodule"#);
        let extra_domain = SOURCE.replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(get{}(L:SortList{},I:SortInt{})),\bottom{R}())) [] endmodule"#);
        for text in [
            extra_value,
            extra_domain,
            SOURCE.replace(
                "get{}(SortList{},SortInt{}) : SortInt{} [function{}(),hook",
                "get{}(SortList{},SortInt{}) : SortInt{} [function{}(),total{}(),hook",
            ),
        ] {
            let definition = load(&text);
            let ops = definition
                .list_operations(&Sort::simple("SortList"))
                .unwrap();
            assert!(ops.get(term(&definition, "L:SortList{}"), 0).is_none());
            assert!(
                domain(
                    &definition,
                    &term(&definition, r#"get{}(L:SortList{},\dv{SortInt{}}("0"))"#)
                )
                .is_none()
            );
        }
        let changed = SOURCE.replace("smt-hook{}(\">=\")", "smt-hook{}(\"<\")");
        let definition = load(&changed);
        assert!(
            domain(
                &definition,
                &term(&definition, r#"get{}(L:SortList{},\dv{SortInt{}}("0"))"#)
            )
            .is_none()
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn prefix_read_rebuild_domains_and_contexts_compose_without_assuming_a_match() {
        use crate::{
            smt::{SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
        };
        let definition = load(SOURCE);
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let list = term(&definition, "L:SortList{}");
        let known = [ops.length_at_least(list.clone(), 2).unwrap()];
        let prefix = ops.prefix(list.clone(), 2).unwrap();
        let context =
            |value| Term::application(definition.symbols()["context"].clone(), vec![], vec![value]);
        let checked = [
            Predicate::Ceil(ops.get(list.clone(), 0).unwrap()),
            Predicate::Ceil(ops.tail(list.clone(), 2).unwrap()),
            Predicate::Equals(prefix.clone(), list.clone()),
            Predicate::Equals(context(prefix), context(list.clone())),
            Predicate::Equals(
                ops.get(ops.tail(list.clone(), 1).unwrap(), 0).unwrap(),
                ops.get(list.clone(), 1).unwrap(),
            ),
        ];
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver
                .check_predicates(&known, &Substitution::new(), &checked)
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let mut concrete_known = known.to_vec();
        concrete_known.push(Predicate::Equals(
            ops.get(list.clone(), 0).unwrap(),
            Term::int(1),
        ));
        let concrete_prefix = Term::list(
            ops.collection.clone(),
            vec![Term::int(1)],
            Some((ops.tail(list.clone(), 1).unwrap(), vec![])),
        );
        assert_eq!(
            solver
                .check_predicates(
                    &concrete_known,
                    &Substitution::new(),
                    &[Predicate::Equals(concrete_prefix, list.clone())]
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let empty = Term::list(ops.collection.clone(), vec![], None);
        let selected = term(
            &definition,
            r#"get{}(choose{SortList{}}(\dv{SortBool{}}("true"),L:SortList{},unit{}()),\dv{SortInt{}}("0"))"#,
        );
        assert_eq!(
            solver
                .check_predicates(
                    &known,
                    &Substitution::new(),
                    &[
                        Predicate::Ceil(selected.clone()),
                        Predicate::Equals(selected, ops.get(list.clone(), 0).unwrap())
                    ]
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        assert_ne!(
            solver
                .check_predicates(
                    &[],
                    &Substitution::new(),
                    &[Predicate::Ceil(ops.get(empty, 0).unwrap())]
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let wrong = Term::list(
            ops.collection.clone(),
            vec![ops.get(list.clone(), 0).unwrap()],
            Some((term(&definition, "R:SortList{}"), vec![])),
        );
        assert_ne!(
            solver
                .check_predicates(
                    &known,
                    &Substitution::new(),
                    &[Predicate::Equals(wrong, list)]
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn a_known_head_does_not_erase_an_undefined_strict_tail() {
        use crate::{
            smt::{Satisfiability, SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
        };
        let definition = load(SOURCE);
        let partial = term(&definition, "partial{}()");
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let source = Term::list(
            ops.collection.clone(),
            vec![Term::int(1)],
            Some((partial.clone(), vec![])),
        );
        let read = ops.get(source, 0).unwrap();
        let known = [Predicate::Not(Arc::new(Predicate::Ceil(partial)))];
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver
                .is_sat(&known, &Substitution::new())
                .unwrap()
                .unwrap(),
            Satisfiability::Sat
        );
        assert_ne!(
            solver
                .check_predicates(&known, &Substitution::new(), &[Predicate::Ceil(read)])
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn zero_length_reconstruction_keeps_the_original_opaque_head_domain() {
        use crate::{
            smt::{Satisfiability, SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
        };
        let definition = load(SOURCE);
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let list = term(&definition, "L:SortList{}");
        let solver = Z3Solver::new(&definition).unwrap();
        let empty = Term::list(ops.collection.clone(), vec![], None);
        assert_eq!(
            solver
                .check_predicates(
                    &[Predicate::Equals(
                        ops.size(list.clone()).unwrap(),
                        Term::int(0)
                    )],
                    &Substitution::new(),
                    &[Predicate::Equals(list, empty)]
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let partial = term(&definition, "partial{}()");
        let known = [
            Predicate::Not(Arc::new(Predicate::Ceil(partial.clone()))),
            Predicate::Equals(ops.size(partial.clone()).unwrap(), Term::int(0)),
        ];
        assert_eq!(
            solver
                .is_sat(&known, &Substitution::new())
                .unwrap()
                .unwrap(),
            Satisfiability::Sat
        );
        assert_ne!(
            solver
                .check_predicates(&known, &Substitution::new(), &[Predicate::Ceil(partial)])
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let variable = crate::term::Variable::new("L", Sort::simple("SortList"));
        let bound = Term::variable(variable.clone());
        let theorem = Predicate::Forall(
            variable,
            Arc::new(Predicate::Implies(
                Arc::new(Predicate::Equals(
                    ops.size(bound.clone()).unwrap(),
                    Term::int(0),
                )),
                Arc::new(Predicate::Equals(
                    bound,
                    Term::list(ops.collection.clone(), vec![], None),
                )),
            )),
        );
        assert_eq!(
            solver
                .check_predicates(&[], &Substitution::new(), &[theorem])
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn deterministic_prefix_matching_retains_its_complete_original_path_region() {
        use crate::{
            matching::{MatchMode, MatchResult, match_terms_in_definition},
            smt::{SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
            term::Variable,
        };
        let definition = load(SOURCE);
        let ops = definition
            .list_operations(&Sort::simple("SortList"))
            .unwrap();
        let list = term(&definition, "L:SortList{}");
        let pattern = Term::list(
            ops.collection.clone(),
            vec![
                term(&definition, "X:SortInt{}"),
                term(&definition, "Y:SortInt{}"),
            ],
            Some((term(&definition, "R:SortList{}"), vec![])),
        );
        let (witness, guards) = match_view(&definition, &pattern, &list).unwrap().unwrap();
        let MatchResult::Success(bindings) =
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &witness)
        else {
            panic!("deterministic variable view must match");
        };
        assert_eq!(
            bindings.get(&Variable::new("X", Sort::simple("SortInt"))),
            Some(&ops.get(list.clone(), 0).unwrap())
        );
        assert_eq!(
            bindings.get(&Variable::new("R", Sort::simple("SortList"))),
            Some(&ops.tail(list.clone(), 2).unwrap())
        );
        assert!(!bindings.contains_key(&Variable::new("L", Sort::simple("SortList"))));
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver
                .check_predicates(
                    &[ops.length_at_least(list.clone(), 2).unwrap()],
                    &Substitution::new(),
                    &guards
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        assert_ne!(
            solver
                .check_predicates(
                    &[Predicate::Equals(
                        ops.size(list.clone()).unwrap(),
                        Term::int(1)
                    )],
                    &Substitution::new(),
                    &guards
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let repeated = Term::list(
            ops.collection.clone(),
            vec![
                term(&definition, "X:SortInt{}"),
                term(&definition, "X:SortInt{}"),
            ],
            Some((term(&definition, "R:SortList{}"), vec![])),
        );
        assert!(match_view(&definition, &repeated, &list).unwrap().is_none());
        let effect_source = SOURCE.replace(
            "partial{}() : SortList{} [function{}()]",
            "partial{}() : SortList{} [function{}(),impure{}()]",
        );
        let effect = load(&effect_source);
        assert!(
            match_view(
                &effect,
                &term(&effect, "concat{}(item{}(X:SortInt{}),R:SortList{})"),
                &term(&effect, "partial{}()")
            )
            .unwrap()
            .is_none()
        );
    }
}
