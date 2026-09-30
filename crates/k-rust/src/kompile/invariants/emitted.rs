//! The emitted-theory checker.
//!
//! In KORE, `inj` is one polymorphic symbol: the axiom
//! `\exists{R}(Val:B, \equals{B,R}(Val, inj{A,B}(From:A)))` carrying the attribute
//! `subsort{A,B}()` is what makes `inj{A,B}` the embedding of `A` in `B`, and composition extends
//! it along chains of such axioms. An application of `inj` at a pair that no chain relates denotes
//! nothing the theory describes: a left-hand side containing it never matches a value, and a
//! right-hand side containing it writes a junk value. A domain value `\dv{S}("s")` denotes the
//! element of `S` that `s` names in `S`'s domain, which exists only when the declaration of `S`'s
//! head carries `hasDomainValues`. A compiler-generated binder variable is introduced to bind
//! something, so a generated `\exists` or `\forall` whose body does not mention its variable binds
//! it in place of whatever the construct means to bind.
//!
//! [`EmittedTheory`] collects those facts from one emitted module and checks a sentence against
//! them:
//!
//! - K1: every application of `inj{A, B}` has `A != B` and a path from `A` to `B` along the
//!   module's `subsort{..}` axiom attributes. The oracle is the emitted axioms themselves, not
//!   the injector's relation, so a defect of that relation is caught here too.
//! - K2: every `\dv{S}` has a sort `S` whose head is declared with `hasDomainValues`.
//! - K3: every `\exists` and `\forall` whose variable decodes to a name that
//!   `is_generated_anonymous` accepts has that variable free in its body.
//!
//! The checks read the patterns of a sentence (the pattern of an axiom or claim, the left and
//! right patterns of an alias declaration), not its attributes. They traverse with the kore
//! crate's own [`for_each_post_order`], so a new `Pattern` variant reaches them through the one
//! exhaustive match of `walk::children` and through the exhaustive match of `check_node`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::kast::identifier::decode_variable;
use crate::kompile::fresh_names::is_generated_anonymous;
use crate::kore::ast::{
    Module, Pattern, Sentence as KoreSentence, Sort as KoreSort, Symbol, Variable,
};
use crate::kore::walk::for_each_post_order;
use crate::names::{KoreAttribute, WellKnownSymbol};
use crate::provenance::OriginRecord;

/// The facts of one emitted KORE module that give its injections and domain values meaning.
#[derive(Debug)]
pub(crate) struct EmittedTheory {
    /// `lesser -> greater` for every `subsort{lesser, greater}()` attribute on an axiom whose
    /// sorts mention no sort variable.
    subsorts: BTreeMap<KoreSort, BTreeSet<KoreSort>>,
    /// `(lesser, greater)` for every `subsort{lesser, greater}()` attribute on an axiom whose
    /// sorts mention a sort variable: a schema, whose instances are found by matching `lesser`.
    schemas: Vec<(KoreSort, KoreSort)>,
    /// Heads of sort declarations that carry `hasDomainValues{}()`.
    domain_heads: BTreeSet<String>,
    /// Whether a path of one or more subsort axioms leads from the first sort to the second,
    /// for every pair asked so far.
    paths: RefCell<BTreeMap<(KoreSort, KoreSort), bool>>,
}

impl EmittedTheory {
    /// Collect the subsort axioms and the domain-value sort heads of `module`.
    pub(crate) fn of(module: &Module) -> Self {
        let mut subsorts = BTreeMap::<KoreSort, BTreeSet<KoreSort>>::new();
        let mut schemas = Vec::new();
        let mut domain_heads = BTreeSet::new();
        // Invariant: `subsorts` and `schemas` hold one edge per `subsort` attribute of every axiom
        // before `sentence`, and `domain_heads` the name of every sort declaration before
        // `sentence` that carries `hasDomainValues`.
        for sentence in &module.sentences {
            match sentence {
                KoreSentence::Axiom { attributes, .. } => {
                    for (lesser, greater) in attributes.0.iter().filter_map(subsort_attribute) {
                        if mentions_sort_variable(lesser) || mentions_sort_variable(greater) {
                            schemas.push((lesser.clone(), greater.clone()));
                        } else {
                            subsorts
                                .entry(lesser.clone())
                                .or_default()
                                .insert(greater.clone());
                        }
                    }
                }
                KoreSentence::SortDeclaration {
                    name, attributes, ..
                } => {
                    if attributes.0.iter().any(|attribute| {
                        is_nullary_attribute(attribute, KoreAttribute::HasDomainValues)
                    }) {
                        domain_heads.insert(name.clone());
                    }
                }
                KoreSentence::Import { .. }
                | KoreSentence::SymbolDeclaration { .. }
                | KoreSentence::AliasDeclaration { .. }
                | KoreSentence::Claim { .. } => {}
            }
        }
        Self {
            subsorts,
            schemas,
            domain_heads,
            paths: RefCell::default(),
        }
    }

    /// Check one emitted sentence against K1, K2 and K3; panics on the first violation.
    ///
    /// `source` describes what the sentence was emitted from and, for a rule or claim, the pass
    /// of its origin record (see [`emitted_from`]); it is called only to report a violation.
    pub(crate) fn check(&self, sentence: &KoreSentence, source: &dyn Fn() -> String) {
        let patterns: Vec<&Pattern> = match sentence {
            KoreSentence::Axiom { pattern, .. } | KoreSentence::Claim { pattern, .. } => {
                vec![pattern]
            }
            KoreSentence::AliasDeclaration { left, right, .. } => vec![left, right],
            KoreSentence::Import { .. }
            | KoreSentence::SortDeclaration { .. }
            | KoreSentence::SymbolDeclaration { .. } => Vec::new(),
        };
        for pattern in patterns {
            for_each_post_order(pattern, |node| {
                if let Some(violation) = self.violation(node) {
                    panic!(
                        "kompile invariant {violation}\n  in the sentence emitted from: {}\n  emitted sentence: {sentence}",
                        source()
                    );
                }
            });
        }
    }

    /// The violated rule and its reason, when `node` itself violates K1, K2 or K3.
    fn violation(&self, node: &Pattern) -> Option<String> {
        match node {
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => self.injection_violation(symbol),
            Pattern::DomainValue { sort, .. } => {
                let declared = match sort {
                    KoreSort::Application { name, .. } => self.domain_heads.contains(name),
                    KoreSort::Variable(_) => false,
                };
                (!declared).then(|| {
                    format!(
                        "K2 (domain value) violated: {node} is a domain value of a sort whose head \
                         is not declared with hasDomainValues"
                    )
                })
            }
            Pattern::Exists { variable, body, .. } => binder_violation("\\exists", variable, body),
            Pattern::Forall { variable, body, .. } => binder_violation("\\forall", variable, body),
            Pattern::String(_)
            | Pattern::Variable(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::And { .. }
            | Pattern::Or { .. }
            | Pattern::Not { .. }
            | Pattern::Next { .. }
            | Pattern::Implies { .. }
            | Pattern::Iff { .. }
            | Pattern::Rewrites { .. }
            | Pattern::Mu { .. }
            | Pattern::Nu { .. }
            | Pattern::Ceil { .. }
            | Pattern::Floor { .. }
            | Pattern::Equals { .. }
            | Pattern::In { .. } => None,
        }
    }

    fn injection_violation(&self, symbol: &Symbol) -> Option<String> {
        if symbol.name != WellKnownSymbol::Inj.as_str() {
            return None;
        }
        let [from, to] = symbol.sort_parameters.as_slice() else {
            return Some(format!(
                "K1 (injection) violated: inj is applied with {} sort arguments instead of two",
                symbol.sort_parameters.len()
            ));
        };
        let reason = if from == to {
            "injects a sort into itself"
        } else if !self.has_path(from, to) {
            "has no path of subsort axioms of the emitted theory from its first sort to its second"
        } else {
            return None;
        };
        Some(format!(
            "K1 (injection) violated: inj{{{}, {}}} {reason}",
            render_sort(from),
            render_sort(to)
        ))
    }

    /// Whether a path of one or more subsort axioms leads from `from` to `to`, memoized per pair.
    fn has_path(&self, from: &KoreSort, to: &KoreSort) -> bool {
        let key = (from.clone(), to.clone());
        if let Some(known) = self.paths.borrow().get(&key) {
            return *known;
        }
        let answer = self.search(from, to);
        self.paths.borrow_mut().insert(key, answer);
        answer
    }

    fn search(&self, from: &KoreSort, to: &KoreSort) -> bool {
        let mut seen = BTreeSet::new();
        let mut work = vec![from.clone()];
        // Invariant: every sort in `seen` or `work` is reachable from `from` by zero or more
        // subsort axioms, and every sort popped from `work` has had all its direct supersorts
        // added to `seen`; each sort enters `work` at most once after `from`, so the search ends
        // once the reachable sorts are exhausted.
        while let Some(sort) = work.pop() {
            for greater in self.direct_supersorts(&sort) {
                if greater == *to {
                    return true;
                }
                if seen.insert(greater.clone()) {
                    work.push(greater);
                }
            }
        }
        false
    }

    /// The sorts one subsort axiom places directly above `sort`.
    fn direct_supersorts(&self, sort: &KoreSort) -> Vec<KoreSort> {
        let mut result: Vec<KoreSort> = self
            .subsorts
            .get(sort)
            .into_iter()
            .flatten()
            .cloned()
            .collect();
        // Invariant: `result` holds the instance of the greater sort of every schema before
        // `(lesser, greater)` whose lesser sort matches `sort`.
        for (lesser, greater) in &self.schemas {
            let mut bindings = BTreeMap::new();
            if match_sort(lesser, sort, &mut bindings)
                && let Some(instance) = substitute(greater, &bindings)
            {
                result.push(instance);
            }
        }
        result
    }
}

/// The K3 violation of a binder `binder` over `variable` with body `body`, if any.
fn binder_violation(binder: &str, variable: &Variable, body: &Pattern) -> Option<String> {
    let (_, decoded) = decode_variable(&variable.name);
    let generated = decoded.is_ok_and(|name| is_generated_anonymous(&name));
    (generated && !body.free_variables().contains(variable)).then(|| {
        format!(
            "K3 (generated binder) violated: {binder} binds the compiler-generated variable \
             {}:{}, which does not occur free in its body",
            variable.name,
            render_sort(&variable.sort)
        )
    })
}

/// What an emitted rule or claim was emitted from, for a violation report: the description of
/// its source sentence and the kompile pass its origin record names, if any.
pub(crate) fn emitted_from(description: &str, origin: Option<&OriginRecord>) -> String {
    match origin {
        Some(record) => format!("{description} (origin: {})", record.pass.as_str()),
        None => format!("{description} (origin: none)"),
    }
}

/// The `(lesser, greater)` sorts of a `subsort{lesser, greater}()` attribute.
fn subsort_attribute(attribute: &Pattern) -> Option<(&KoreSort, &KoreSort)> {
    let Pattern::Application { symbol, arguments } = attribute else {
        return None;
    };
    if symbol.name != KoreAttribute::Subsort.as_str() || !arguments.is_empty() {
        return None;
    }
    match symbol.sort_parameters.as_slice() {
        [lesser, greater] => Some((lesser, greater)),
        _ => None,
    }
}

fn is_nullary_attribute(attribute: &Pattern, key: KoreAttribute) -> bool {
    matches!(
        attribute,
        Pattern::Application { symbol, arguments }
            if symbol.name == key.as_str() && symbol.sort_parameters.is_empty() && arguments.is_empty()
    )
}

fn mentions_sort_variable(sort: &KoreSort) -> bool {
    match sort {
        KoreSort::Variable(_) => true,
        KoreSort::Application { arguments, .. } => arguments.iter().any(mentions_sort_variable),
    }
}

/// First-order matching of the schema sort `pattern` against `subject`, whose sort variables
/// are rigid: extends `bindings` and answers whether `subject` is an instance of `pattern`.
fn match_sort(
    pattern: &KoreSort,
    subject: &KoreSort,
    bindings: &mut BTreeMap<String, KoreSort>,
) -> bool {
    match pattern {
        KoreSort::Variable(name) => match bindings.get(name) {
            Some(bound) => bound == subject,
            None => {
                bindings.insert(name.clone(), subject.clone());
                true
            }
        },
        KoreSort::Application { name, arguments } => match subject {
            KoreSort::Application {
                name: subject_name,
                arguments: subject_arguments,
            } => {
                name == subject_name
                    && arguments.len() == subject_arguments.len()
                    && arguments
                        .iter()
                        .zip(subject_arguments)
                        .all(|(argument, subject)| match_sort(argument, subject, bindings))
            }
            KoreSort::Variable(_) => false,
        },
    }
}

/// `sort` with `bindings` applied, or `None` when it mentions a variable `bindings` lacks (a
/// schema whose greater sort is not determined by its lesser sort has no single instance).
fn substitute(sort: &KoreSort, bindings: &BTreeMap<String, KoreSort>) -> Option<KoreSort> {
    match sort {
        KoreSort::Variable(name) => bindings.get(name).cloned(),
        KoreSort::Application { name, arguments } => Some(KoreSort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute(argument, bindings))
                .collect::<Option<_>>()?,
        }),
    }
}

fn render_sort(sort: &KoreSort) -> String {
    match sort {
        KoreSort::Variable(name) => name.clone(),
        KoreSort::Application { name, arguments } => format!(
            "{name}{{{}}}",
            arguments
                .iter()
                .map(render_sort)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::Arc;

    use super::{EmittedTheory, emitted_from};
    use crate::kore::ast::Sentence as KoreSentence;
    use crate::kore::parser::{parse_module, parse_sentence};
    use crate::provenance::{GeneratingPass, OriginRecord};

    /// The counter fixture's theory: `Counter < Nat` and `Int < Nat`, `Bool` with domain values,
    /// `Foo` without them.
    const THEORY: &str = r#"
        module MAIN
          sort SortBool{} [hasDomainValues{}()]
          sort SortInt{} [hasDomainValues{}()]
          sort SortNat{} []
          sort SortCounter{} []
          sort SortFoo{} []
          axiom{R} \exists{R}(Val:SortNat{}, \equals{SortNat{}, R}(Val:SortNat{}, inj{SortCounter{}, SortNat{}}(From:SortCounter{}))) [subsort{SortCounter{}, SortNat{}}()]
          axiom{R} \exists{R}(Val:SortNat{}, \equals{SortNat{}, R}(Val:SortNat{}, inj{SortInt{}, SortNat{}}(From:SortInt{}))) [subsort{SortInt{}, SortNat{}}()]
        endmodule []
    "#;

    fn theory(text: &str) -> EmittedTheory {
        EmittedTheory::of(&parse_module(text).expect("the test theory parses"))
    }

    fn sentence(text: &str) -> KoreSentence {
        parse_sentence(text).expect("the test sentence parses")
    }

    fn generated_origin() -> OriginRecord {
        OriginRecord {
            pass: GeneratingPass::GenerateSortPredicateRules,
            origins: Arc::from([]),
            destination: None,
        }
    }

    fn source() -> String {
        emitted_from("increment-rule", Some(&generated_origin()))
    }

    /// The panic message of checking `sentence` against `theory`, or `None` when it passes.
    fn violation(theory: &EmittedTheory, sentence: &KoreSentence) -> Option<String> {
        catch_unwind(AssertUnwindSafe(|| theory.check(sentence, &source)))
            .err()
            .map(|payload| {
                payload
                    .downcast_ref::<String>()
                    .cloned()
                    .expect("the checker panics with a formatted message")
            })
    }

    fn assert_violation(theory: &EmittedTheory, sentence: &KoreSentence, rule: &str) {
        let message = violation(theory, sentence).expect("the sentence violates the theory");
        assert!(message.contains(rule), "{message}");
        assert!(
            message.contains("increment-rule (origin: generate-sort-predicate-rules)"),
            "{message}"
        );
    }

    #[test]
    fn injection_without_a_subsort_path_panics_naming_source_and_origin() {
        let theory = theory(THEORY);
        let bool_at_nat = sentence(
            r#"axiom{} \rewrites{SortNat{}}(increment{}(inj{SortBool{}, SortNat{}}(\dv{SortBool{}}("true"))), \dv{SortInt{}}("1")) []"#,
        );
        assert_violation(
            &theory,
            &bool_at_nat,
            "K1 (injection) violated: inj{SortBool{}, SortNat{}} has no path",
        );
        let reflexive = sentence(
            r#"axiom{} \rewrites{SortNat{}}(inj{SortNat{}, SortNat{}}(X:SortNat{}), X:SortNat{}) []"#,
        );
        assert_violation(
            &theory,
            &reflexive,
            "K1 (injection) violated: inj{SortNat{}, SortNat{}} injects a sort into itself",
        );
    }

    #[test]
    fn injection_along_a_chain_of_subsort_axioms_passes() {
        let with_bool = theory(&THEORY.replace(
            "endmodule",
            r#"axiom{R} \exists{R}(Val:SortInt{}, \equals{SortInt{}, R}(Val:SortInt{}, inj{SortBool{}, SortInt{}}(From:SortBool{}))) [subsort{SortBool{}, SortInt{}}()]
               endmodule"#,
        ));
        let bool_at_nat = sentence(
            r#"axiom{} \rewrites{SortNat{}}(increment{}(inj{SortBool{}, SortNat{}}(\dv{SortBool{}}("true"))), \dv{SortInt{}}("1")) []"#,
        );
        assert_eq!(violation(&with_bool, &bool_at_nat), None);
        let counter_at_nat = sentence(
            r#"axiom{} \rewrites{SortNat{}}(increment{}(inj{SortCounter{}, SortNat{}}(X:SortCounter{})), \dv{SortInt{}}("1")) []"#,
        );
        assert_eq!(violation(&theory(THEORY), &counter_at_nat), None);
    }

    #[test]
    fn injection_along_a_schema_axiom_passes_only_for_its_instances() {
        let schema = theory(
            r#"module MAIN
                 sort SortList{S} []
                 sort SortColl{S} []
                 axiom{S, R} \top{R}() [subsort{SortList{S}, SortColl{S}}()]
               endmodule []"#,
        );
        let instance = sentence(
            r#"axiom{} \rewrites{SortColl{SortNat{}}}(inj{SortList{SortNat{}}, SortColl{SortNat{}}}(X:SortList{SortNat{}}), Y:SortColl{SortNat{}}) []"#,
        );
        assert_eq!(violation(&schema, &instance), None);
        let mismatch = sentence(
            r#"axiom{} \rewrites{SortColl{SortInt{}}}(inj{SortList{SortNat{}}, SortColl{SortInt{}}}(X:SortList{SortNat{}}), Y:SortColl{SortInt{}}) []"#,
        );
        assert_violation(&schema, &mismatch, "has no path");
    }

    #[test]
    fn domain_value_of_a_sort_without_domain_values_panics_naming_source_and_origin() {
        let token = sentence(
            r#"axiom{} \rewrites{SortFoo{}}(go{}(\dv{SortInt{}}("0")), bar{}(\dv{SortFoo{}}("1"))) []"#,
        );
        assert_violation(
            &theory(THEORY),
            &token,
            r#"K2 (domain value) violated: \dv{SortFoo{}}("1")"#,
        );
    }

    #[test]
    fn domain_value_of_a_sort_declared_with_domain_values_passes() {
        let declared =
            theory(&THEORY.replace("sort SortFoo{} []", "sort SortFoo{} [hasDomainValues{}()]"));
        let token = sentence(
            r#"axiom{} \rewrites{SortFoo{}}(go{}(\dv{SortInt{}}("0")), bar{}(\dv{SortFoo{}}("1"))) []"#,
        );
        assert_eq!(violation(&declared, &token), None);
    }

    #[test]
    fn generated_binder_over_an_absent_variable_panics_naming_source_and_origin() {
        let vacuous = sentence(
            r#"axiom{S} \exists{S}(Var'Unds'Gen0:SortK{}, \equals{SortInt{}, S}(VarX:SortInt{}, \dv{SortInt{}}("1"))) []"#,
        );
        assert_violation(
            &theory(THEORY),
            &vacuous,
            "K3 (generated binder) violated: \\exists binds the compiler-generated variable Var'Unds'Gen0:SortK{}",
        );
        let vacuous_forall =
            sentence(r#"axiom{S} \forall{S}(Var'Unds'Gen3:SortK{}, \top{S}()) []"#);
        assert_violation(
            &theory(THEORY),
            &vacuous_forall,
            "K3 (generated binder) violated: \\forall",
        );
    }

    #[test]
    fn generated_binder_over_a_body_variable_and_user_binders_pass() {
        let bound = sentence(
            r#"axiom{S} \exists{S}(Var'Unds'Gen0:SortK{}, \equals{SortK{}, S}(Var'Unds'Gen0:SortK{}, VarX:SortK{})) []"#,
        );
        assert_eq!(violation(&theory(THEORY), &bound), None);
        // A binder the author wrote over a variable its body does not mention is well-formed
        // and equivalent to its body.
        let user = sentence(
            r#"axiom{S} \exists{S}(VarX:SortK{}, \equals{SortInt{}, S}(VarY:SortInt{}, \dv{SortInt{}}("1"))) []"#,
        );
        assert_eq!(violation(&theory(THEORY), &user), None);
        // A generated variable of another sort is another variable.
        let other_sort = sentence(
            r#"axiom{S} \exists{S}(Var'Unds'Gen0:SortK{}, \equals{SortInt{}, S}(Var'Unds'Gen0:SortInt{}, \dv{SortInt{}}("1"))) []"#,
        );
        assert!(violation(&theory(THEORY), &other_sort).is_some());
    }

    #[test]
    fn source_without_origin_record_says_so() {
        assert_eq!(emitted_from("main.k:3", None), "main.k:3 (origin: none)");
    }
}
