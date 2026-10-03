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
//! it in place of whatever the construct means to bind. KORE quantifies sort variables only at a
//! sentence (`axiom{R, W}`, `symbol f{W}`), never inside a pattern, and a sort application
//! `SortH{A1, .., An}` names a sort declared with `n` parameters; a sentence that mentions any
//! other sort refers to nothing the theory declares, and when a sort parameter of a source
//! sentence leaked out of its binder as `SortW{}` it states the source's property at a sort that
//! does not exist instead of at every instantiation.
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
//! - K4 (sort scope): every sort the sentence mentions is a sort variable the sentence binds, or
//!   an application of a sort declared (as a sort or hooked sort) in the module or in the
//!   embedded prelude with exactly as many parameters as it is applied to, whose arguments
//!   satisfy K4 in turn. An axiom or claim binds its `parameters` and mentions every sort of its
//!   pattern; a symbol or alias declaration binds its sort parameters, each of which must be a
//!   sort variable, and mentions its argument and result sorts (and an alias its two patterns);
//!   a sort declaration binds its parameters. The symbol instances in `element`, `unit`,
//!   `concat` and `update` attributes also satisfy K4 under the sentence's binder.
//!   K4 runs before K1-K3, so an undeclared sort reports its cause rather than a junk injection.
//! - K5 (symbol arity): every symbol or alias application names a declaration in the module or
//!   embedded prelude and carries exactly as many sort arguments as that declaration binds.
//!   K5 runs before K1, so missing injection sort arguments report their arity.
//!   A generated module's pattern applications are checked for K5 before sentence checks, so
//!   a dropped symbol instance in an axiom is reported before a leaked attribute sort in a
//!   declaration of the same theory.
//!
//! The checks read the sorts and patterns of a sentence (the pattern of an axiom or claim, the
//! left and right patterns of an alias declaration, the signature of a symbol or alias
//! declaration), and the symbol instances in the four attributes above. Other attributes name
//! symbols without sort arguments by convention (`priorities`, `left`, `right`, `format`), or
//! belong to another rule (`subsort` to K1), and are left alone. Pattern checks traverse with the
//! kore crate's own [`for_each_post_order`] and [`Pattern::for_each_sort`], so a new `Pattern`
//! variant reaches them through the exhaustive matches of `walk::children` and `for_each_sort`
//! and through the exhaustive match of `violation`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use crate::kast::identifier::decode_variable;
use crate::kompile::fresh_names::is_generated_anonymous;
use crate::kompile::module_to_kore::standard_kore_prelude;
use crate::kore::ast::{
    Module, Pattern, Sentence as KoreSentence, Sort as KoreSort, Symbol, Variable,
};
use crate::kore::walk::for_each_post_order;
use crate::names::{KoreAttribute, WellKnownSymbol};
use crate::provenance::OriginRecord;

/// The declarations and subsort facts of one emitted KORE module.
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
    /// `name -> number of parameters` for every sort declared in the module or in the embedded
    /// prelude.
    sorts: BTreeMap<String, usize>,
    /// `name -> number of sort parameters` for every symbol or alias declared in the module or
    /// in the embedded prelude.
    symbols: BTreeMap<String, usize>,
    /// Whether a path of one or more subsort axioms leads from the first sort to the second,
    /// for every pair asked so far.
    paths: RefCell<BTreeMap<(KoreSort, KoreSort), bool>>,
}

impl EmittedTheory {
    /// Collect the subsort axioms, domain-value sort heads and sort, symbol and alias declarations.
    pub(crate) fn of(module: &Module) -> Self {
        let mut subsorts = BTreeMap::<KoreSort, BTreeSet<KoreSort>>::new();
        let mut schemas = Vec::new();
        let mut domain_heads = BTreeSet::new();
        let mut sorts = prelude_sorts().clone();
        let mut symbols = prelude_symbols().clone();
        // Invariant: `subsorts` and `schemas` hold one edge per `subsort` attribute of every axiom
        // before `sentence`, `domain_heads` the name of every sort declaration before `sentence`
        // that carries `hasDomainValues`, and `sorts` the prelude's sorts and every sort declared
        // before `sentence` with its number of parameters; `symbols` holds the prelude's symbols
        // and every symbol or alias declared before `sentence` with its number of sort parameters.
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
                    name,
                    parameters,
                    attributes,
                    ..
                } => {
                    sorts.insert(name.clone(), parameters.len());
                    if attributes.0.iter().any(|attribute| {
                        is_nullary_attribute(attribute, KoreAttribute::HasDomainValues)
                    }) {
                        domain_heads.insert(name.clone());
                    }
                }
                KoreSentence::SymbolDeclaration { symbol, .. }
                | KoreSentence::AliasDeclaration { alias: symbol, .. } => {
                    symbols.insert(symbol.name.clone(), symbol.sort_parameters.len());
                }
                KoreSentence::Import { .. } | KoreSentence::Claim { .. } => {}
            }
        }
        Self {
            subsorts,
            schemas,
            domain_heads,
            sorts,
            symbols,
            paths: RefCell::default(),
        }
    }

    /// Check pattern symbol arities throughout the generated theory before checking sentences.
    /// A declaration and its axioms can contain different defects of the same symbol instance;
    /// the missing instance must be reported before interpreting the sorts of that theory.
    pub(crate) fn check_module(&self, module: &Module) {
        let source = || format!("a declaration or generated axiom of module {}", module.name);
        // Invariant: pattern applications in every sentence before `sentence` satisfy K5.
        for sentence in &module.sentences {
            for pattern in sentence_patterns(sentence) {
                for_each_post_order(pattern, |node| {
                    if let Pattern::Application { symbol, .. }
                    | Pattern::AssociativeApplication { symbol, .. } = node
                        && let Some(reason) = self.symbol_arity_violation(symbol)
                    {
                        report_violation(sentence, &reason, &source);
                    }
                });
            }
        }
        // Invariant: every sentence before `sentence` satisfies K1-K5 in this theory.
        for sentence in &module.sentences {
            self.check(sentence, &source);
        }
    }

    /// Check attributes first, then signature/pattern sort scope and K5 and K1-K3.
    /// Panics on the first violation.
    ///
    /// `source` describes what the sentence was emitted from and, for a rule or claim, the pass
    /// of its origin record (see [`emitted_from`]); it is called only to report a violation.
    pub(crate) fn check(&self, sentence: &KoreSentence, source: &dyn Fn() -> String) {
        if let Some(reason) = self.attribute_violation(sentence) {
            report_violation(sentence, &reason, source);
        }
        if let Some(reason) = self.scope_violation(sentence) {
            report_violation(
                sentence,
                &format!("K4 (sort scope) violated: {reason}"),
                source,
            );
        }
        for pattern in sentence_patterns(sentence) {
            for_each_post_order(pattern, |node| {
                if let Some(reason) = self.violation(node) {
                    report_violation(sentence, &reason, source);
                }
            });
        }
    }

    /// Check a frontend-produced standalone pattern against emitted declarations and paths.
    /// Element variables are permitted; no sort variable has a standalone binder.
    pub(crate) fn check_pattern(&self, pattern: &Pattern, source: &str) {
        let bound = BTreeSet::new();
        let mut first = None;
        pattern.for_each_sort(|sort| {
            if first.is_none() {
                first = self.sort_scope_violation(sort, &bound);
            }
        });
        if let Some(reason) = first {
            panic!(
                "kompile invariant K4 (sort scope) violated: {reason}\n  in frontend pattern from: {source}\n  emitted pattern: {pattern}"
            );
        }
        for_each_post_order(pattern, |node| {
            if let Some(reason) = self.violation(node) {
                panic!(
                    "kompile invariant {reason}\n  in frontend pattern from: {source}\n  emitted pattern: {pattern}"
                );
            }
        });
    }

    /// The reason `sentence` violates K4, if it does: the first sort it mentions, in signature
    /// then pattern order, that is neither a sort variable it binds nor a declared sort applied
    /// to as many arguments as its declaration has parameters.
    fn scope_violation(&self, sentence: &KoreSentence) -> Option<String> {
        // An axiom or claim binds its `parameters`, which are sort variables by construction; a
        // symbol or alias declaration binds its `binder` sorts, which must be sort variables.
        let (parameters, binder, signature, patterns): (
            &[String],
            &[KoreSort],
            Vec<&KoreSort>,
            Vec<&Pattern>,
        ) = match sentence {
            KoreSentence::Axiom {
                parameters,
                pattern,
                ..
            }
            | KoreSentence::Claim {
                parameters,
                pattern,
                ..
            } => (parameters, &[], Vec::new(), vec![pattern]),
            KoreSentence::SymbolDeclaration {
                symbol,
                argument_sorts,
                result_sort,
                ..
            } => (
                &[],
                &symbol.sort_parameters,
                argument_sorts.iter().chain([result_sort]).collect(),
                Vec::new(),
            ),
            KoreSentence::AliasDeclaration {
                alias,
                argument_sorts,
                result_sort,
                left,
                right,
                ..
            } => (
                &[],
                &alias.sort_parameters,
                argument_sorts.iter().chain([result_sort]).collect(),
                vec![left, right],
            ),
            KoreSentence::Import { .. } | KoreSentence::SortDeclaration { .. } => return None,
        };
        let mut bound: BTreeSet<&str> = parameters.iter().map(String::as_str).collect();
        // Invariant: `bound` holds `parameters` and the names of the binder's sorts before
        // `parameter`, each of which is a sort variable.
        for parameter in binder {
            match parameter {
                KoreSort::Variable(name) => {
                    bound.insert(name);
                }
                KoreSort::Application { .. } => {
                    return Some(format!(
                        "the sort parameter {} of the declaration is not a sort variable",
                        render_sort(parameter)
                    ));
                }
            }
        }
        if let Some(reason) = signature
            .into_iter()
            .find_map(|sort| self.sort_scope_violation(sort, &bound))
        {
            return Some(reason);
        }
        let mut first = None;
        // Invariant: `first` is the first violation among the sorts of the patterns before
        // `pattern`, if any; the loop stops at the first pattern that holds one.
        for pattern in patterns {
            pattern.for_each_sort(|sort| {
                if first.is_none() {
                    first = self.sort_scope_violation(sort, &bound);
                }
            });
            if first.is_some() {
                break;
            }
        }
        first
    }

    /// The four instance-valued attributes are interpreted in the declaring sentence's binder.
    fn attribute_violation(&self, sentence: &KoreSentence) -> Option<String> {
        let (bound, attributes): (BTreeSet<&str>, _) = match sentence {
            KoreSentence::SortDeclaration {
                parameters,
                attributes,
                ..
            }
            | KoreSentence::Axiom {
                parameters,
                attributes,
                ..
            }
            | KoreSentence::Claim {
                parameters,
                attributes,
                ..
            } => (parameters.iter().map(String::as_str).collect(), attributes),
            KoreSentence::SymbolDeclaration {
                symbol, attributes, ..
            }
            | KoreSentence::AliasDeclaration {
                alias: symbol,
                attributes,
                ..
            } => (
                symbol
                    .sort_parameters
                    .iter()
                    .filter_map(|sort| match sort {
                        KoreSort::Variable(name) => Some(name.as_str()),
                        KoreSort::Application { .. } => None,
                    })
                    .collect(),
                attributes,
            ),
            KoreSentence::Import { .. } => return None,
        };
        for attribute in &attributes.0 {
            let Pattern::Application {
                symbol: key,
                arguments,
            } = attribute
            else {
                continue;
            };
            if ![
                KoreAttribute::Element,
                KoreAttribute::Unit,
                KoreAttribute::Concat,
                KoreAttribute::Update,
            ]
            .iter()
            .any(|key_name| key.name == key_name.as_str())
            {
                continue;
            }
            for argument in arguments {
                let (Pattern::Application { symbol, .. }
                | Pattern::AssociativeApplication { symbol, .. }) = argument
                else {
                    continue;
                };
                if let Some(reason) = self.symbol_arity_violation(symbol) {
                    return Some(format!("{reason} in attribute {}", key.name));
                }
                for sort in &symbol.sort_parameters {
                    if let Some(reason) = self.sort_scope_violation(sort, &bound) {
                        return Some(format!(
                            "K4 (sort scope) violated in attribute {}: {reason}",
                            key.name
                        ));
                    }
                }
            }
        }
        None
    }

    /// The reason `sort` violates K4 under the bound sort variables `bound`, if it does.
    fn sort_scope_violation(&self, sort: &KoreSort, bound: &BTreeSet<&str>) -> Option<String> {
        let mut work = vec![sort];
        // Invariant: every sort popped so far is a bound sort variable or a declared sort applied
        // to as many arguments as its declaration has parameters, and `work` holds the unvisited
        // subsorts of `sort`; each pop pushes only its direct arguments, so each subsort
        // occurrence is popped once.
        while let Some(sort) = work.pop() {
            match sort {
                KoreSort::Variable(name) => {
                    if !bound.contains(name.as_str()) {
                        return Some(format!("sort variable {name} is not bound by the sentence"));
                    }
                }
                KoreSort::Application { name, arguments } => {
                    match self.sorts.get(name) {
                        None => return Some(format!("sort {name} is not declared")),
                        Some(&parameters) if parameters != arguments.len() => {
                            return Some(format!(
                                "sort {name} is declared with {parameters} parameters but \
                                 applied to {}",
                                arguments.len()
                            ));
                        }
                        Some(_) => {}
                    }
                    work.extend(arguments);
                }
            }
        }
        None
    }

    /// The violated rule and its reason, when `node` itself violates K5, K1, K2 or K3.
    fn violation(&self, node: &Pattern) -> Option<String> {
        match node {
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => self
                .symbol_arity_violation(symbol)
                .or_else(|| self.injection_violation(symbol)),
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

    fn symbol_arity_violation(&self, symbol: &Symbol) -> Option<String> {
        match self.symbols.get(&symbol.name) {
            None => Some(format!(
                "K5 (symbol arity) violated: symbol {} is not declared",
                symbol.name
            )),
            Some(&parameters) if parameters != symbol.sort_parameters.len() => Some(format!(
                "K5 (symbol arity) violated: symbol {} is declared with {parameters} sort parameters but applied to {}",
                symbol.name,
                symbol.sort_parameters.len()
            )),
            Some(_) => None,
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

/// The sentence's logical patterns; its signature and metadata have separate checks.
fn sentence_patterns(sentence: &KoreSentence) -> Vec<&Pattern> {
    match sentence {
        KoreSentence::Axiom { pattern, .. } | KoreSentence::Claim { pattern, .. } => vec![pattern],
        KoreSentence::AliasDeclaration { left, right, .. } => vec![left, right],
        KoreSentence::Import { .. }
        | KoreSentence::SortDeclaration { .. }
        | KoreSentence::SymbolDeclaration { .. } => Vec::new(),
    }
}

fn report_violation(sentence: &KoreSentence, reason: &str, source: &dyn Fn() -> String) -> ! {
    panic!(
        "kompile invariant {reason}\n  in the sentence emitted from: {}\n  emitted sentence: {sentence}",
        source()
    )
}

/// `name -> number of parameters` for every sort the embedded prelude declares, parsed once.
fn prelude_sorts() -> &'static BTreeMap<String, usize> {
    static SORTS: OnceLock<BTreeMap<String, usize>> = OnceLock::new();
    SORTS.get_or_init(|| {
        standard_kore_prelude()
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                KoreSentence::SortDeclaration {
                    name, parameters, ..
                } => Some((name.clone(), parameters.len())),
                KoreSentence::Import { .. }
                | KoreSentence::SymbolDeclaration { .. }
                | KoreSentence::AliasDeclaration { .. }
                | KoreSentence::Axiom { .. }
                | KoreSentence::Claim { .. } => None,
            })
            .collect()
    })
}

/// `name -> number of sort parameters` for every symbol or alias the embedded prelude declares.
fn prelude_symbols() -> &'static BTreeMap<String, usize> {
    static SYMBOLS: OnceLock<BTreeMap<String, usize>> = OnceLock::new();
    SYMBOLS.get_or_init(|| {
        standard_kore_prelude()
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                KoreSentence::SymbolDeclaration { symbol, .. }
                | KoreSentence::AliasDeclaration { alias: symbol, .. } => {
                    Some((symbol.name.clone(), symbol.sort_parameters.len()))
                }
                KoreSentence::SortDeclaration { .. }
                | KoreSentence::Import { .. }
                | KoreSentence::Axiom { .. }
                | KoreSentence::Claim { .. } => None,
            })
            .collect()
    })
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
          symbol increment{}(SortNat{}) : SortNat{} []
          symbol go{}(SortInt{}) : SortFoo{} []
          symbol bar{}(SortFoo{}) : SortFoo{} []
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

    fn pattern_violation(theory: &EmittedTheory, text: &str) -> Option<String> {
        let pattern = crate::kore::parser::parse_pattern(text).unwrap();
        catch_unwind(AssertUnwindSafe(|| {
            theory.check_pattern(&pattern, "krun initial configuration ($PGM)")
        }))
        .err()
        .map(|payload| payload.downcast_ref::<String>().unwrap().clone())
    }

    #[test]
    fn standalone_pattern_checks_emitted_paths_and_reports_frontend_origin() {
        let theory = theory(THEORY);
        assert_eq!(
            pattern_violation(&theory, r#"inj{SortCounter{}, SortNat{}}(X:SortCounter{})"#),
            None,
        );
        let message = pattern_violation(
            &theory,
            r#"inj{SortBool{}, SortNat{}}(\dv{SortBool{}}("true"))"#,
        )
        .unwrap();
        assert!(message.contains("K1 (injection)"), "{message}");
        assert!(
            message.contains("krun initial configuration ($PGM)"),
            "{message}"
        );
        let message = pattern_violation(&theory, r#"X:S"#).unwrap();
        assert!(
            message.contains("sort variable S is not bound"),
            "{message}"
        );
    }

    #[test]
    fn standalone_pattern_schema_paths_compare_full_concrete_instances() {
        let theory = theory(
            r#"module MAIN
          sort SortNat{} []
          sort SortInt{} []
          sort SortList{S} []
          sort SortColl{S} []
          axiom{S,R} \top{R}() [subsort{SortList{S},SortColl{S}}()]
        endmodule []"#,
        );
        assert_eq!(
            pattern_violation(
                &theory,
                r#"inj{SortList{SortNat{}},SortColl{SortNat{}}}(X:SortList{SortNat{}})"#
            ),
            None
        );
        let message = pattern_violation(
            &theory,
            r#"inj{SortList{SortNat{}},SortColl{SortInt{}}}(X:SortList{SortNat{}})"#,
        )
        .unwrap();
        assert!(message.contains("has no path"), "{message}");
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
                 sort SortNat{} []
                 sort SortInt{} []
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

    /// A theory with `Foo`, the hooked parametric sort `MInt{S0}` and `8`; `W` is not a sort.
    const SCOPE: &str = r#"
        module MAIN
          sort SortFoo{} []
          sort Sort8{} []
          hooked-sort SortMInt{S0} [hook{}("MINT.MInt")]
        endmodule []
    "#;

    fn check_scope(text: &str) {
        theory(SCOPE).check(&sentence(text), &source);
    }

    #[test]
    #[should_panic(expected = "K4 (sort scope) violated: sort SortW is not declared")]
    fn leaked_sort_parameter_in_an_axiom_pattern_panics() {
        check_scope(
            r#"axiom{} \or{SortFoo{}}(\exists{SortFoo{}}(X0:SortMInt{SortW{}}, pick{SortW{}}(X0:SortMInt{SortW{}})), \bottom{SortFoo{}}()) [constructor{}()]"#,
        );
    }

    #[test]
    #[should_panic(expected = "K4 (sort scope) violated: sort SortW is not declared")]
    fn leaked_sort_parameter_in_a_symbol_signature_panics() {
        check_scope(r#"symbol f{}(SortFoo{}) : SortMInt{SortW{}} [function{}()]"#);
    }

    #[test]
    #[should_panic(
        expected = "K4 (sort scope) violated: sort SortMInt is declared with 1 parameters but applied to 2"
    )]
    fn sort_applied_to_the_wrong_number_of_arguments_panics() {
        check_scope(
            r#"axiom{R} \equals{SortMInt{SortFoo{}, SortFoo{}}, R}(X:SortMInt{SortFoo{}, SortFoo{}}, X:SortMInt{SortFoo{}, SortFoo{}}) []"#,
        );
    }

    #[test]
    #[should_panic(
        expected = "K4 (sort scope) violated: sort variable W is not bound by the sentence"
    )]
    fn sort_variable_the_axiom_does_not_bind_panics() {
        check_scope(r#"axiom{} \equals{SortMInt{W}, SortFoo{}}(X:SortMInt{W}, X:SortMInt{W}) []"#);
    }

    #[test]
    #[should_panic(
        expected = "K4 (sort scope) violated: the sort parameter SortFoo{} of the declaration is not a sort variable"
    )]
    fn declaration_binding_a_sort_application_panics() {
        check_scope(r#"symbol f{SortFoo{}}(SortFoo{}) : SortFoo{} []"#);
    }

    #[test]
    fn k4_reports_the_cause_before_a_k1_symptom() {
        let message = violation(
            &theory(SCOPE),
            &sentence(
                r#"axiom{} \rewrites{SortK{}}(kseq{}(inj{SortMInt{SortW{}}, SortKItem{}}(X:SortMInt{SortW{}}), dotk{}()), dotk{}()) []"#,
            ),
        )
        .expect("the sentence violates K4 and K1");
        assert!(
            message.contains("K4 (sort scope) violated: sort SortW is not declared"),
            "{message}"
        );
    }

    #[test]
    fn bound_sort_variables_declared_and_prelude_sorts_pass() {
        let scope = theory(SCOPE);
        // Sort variables bound by the axiom, and the prelude's `SortK` and `SortKItem`, which the
        // module does not declare itself.
        let bound_axiom = sentence(
            r#"axiom{R, W} \equals{SortMInt{W}, R}(X:SortMInt{W}, Y:SortMInt{W}) [subsort{SortK{}, SortKItem{}}()]"#,
        );
        assert_eq!(violation(&scope, &bound_axiom), None);
        let prelude = sentence(
            r#"axiom{R} \equals{SortK{}, R}(kseq{}(X:SortKItem{}, dotk{}()), Y:SortK{}) []"#,
        );
        assert_eq!(violation(&scope, &prelude), None);
        // A sort variable bound by a symbol declaration.
        let bound_symbol = sentence(r#"symbol pick{W}(SortMInt{W}) : SortFoo{} [constructor{}()]"#);
        assert_eq!(violation(&scope, &bound_symbol), None);
        // A declared parametric sort applied to a declared sort.
        let instance = sentence(
            r#"axiom{R} \equals{SortMInt{Sort8{}}, R}(X:SortMInt{Sort8{}}, Y:SortMInt{Sort8{}}) []"#,
        );
        assert_eq!(violation(&scope, &instance), None);
        // Subsort metadata is read by K1, not K4.
        let attribute = sentence(r#"axiom{R} \top{R}() [subsort{SortW{}, SortFoo{}}()]"#);
        assert_eq!(violation(&scope, &attribute), None);
        // A sort declaration without instance attributes and an import mention no checked sorts.
        assert_eq!(violation(&scope, &sentence("sort SortBar{S} []")), None);
        assert_eq!(violation(&scope, &sentence("import UNKNOWN []")), None);
    }

    /// Symbol instances for the unit and collection attributes; `SortS` and `SortW` are absent.
    const SYMBOLS: &str = r#"
        module MAIN
          sort SortFoo{} []
          symbol Lbleps{S}() : S []
          symbol Lblsitem{W}(W) : SortFoo{} []
          symbol Lblcat{}(SortFoo{}, SortFoo{}) : SortFoo{} []
          alias Lbla{S}() : S where Lbla{S}() := Lbleps{S}() []
        endmodule []
    "#;

    #[test]
    fn fu23_unit_axiom_missing_sort_argument_panics() {
        assert_violation(
            &theory(SYMBOLS),
            &sentence(
                r#"axiom{R} \equals{SortFoo{}, R}(Lblcat{}(K:SortFoo{}, Lbleps{}()), K:SortFoo{}) []"#,
            ),
            "K5 (symbol arity) violated: symbol Lbleps is declared with 1 sort parameters but applied to 0",
        );
    }

    #[test]
    fn fu23_undeclared_symbol_panics() {
        assert_violation(
            &theory(SYMBOLS),
            &sentence(r#"claim{} Lblmissing{}() []"#),
            "K5 (symbol arity) violated: symbol Lblmissing is not declared",
        );
    }

    #[test]
    fn fu23_associative_application_checks_symbol_arity() {
        assert_violation(
            &theory(SYMBOLS),
            &sentence(r#"axiom{} \left-assoc{}(Lblcat{SortFoo{}}(X:SortFoo{}, Y:SortFoo{})) []"#),
            "K5 (symbol arity) violated: symbol Lblcat is declared with 0 sort parameters but applied to 1",
        );
    }

    #[test]
    fn fu23_alias_instances_use_the_alias_binder() {
        let theory = theory(SYMBOLS);
        assert_eq!(
            violation(&theory, &sentence(r#"axiom{} Lbla{SortFoo{}}() []"#)),
            None
        );
        theory.check(
            &sentence(r#"alias Lbla{S}() : S where Lbla{S}() := Lbleps{S}() []"#),
            &source,
        );
        assert_violation(
            &theory,
            &sentence(r#"axiom{} Lbla{}() []"#),
            "K5 (symbol arity) violated: symbol Lbla is declared with 1 sort parameters but applied to 0",
        );
    }

    #[test]
    fn fu23_unit_attribute_leaked_sort_panics() {
        assert_violation(
            &theory(SYMBOLS),
            &sentence(
                r#"symbol Lblcat{}(SortFoo{}, SortFoo{}) : SortFoo{} [unit{}(Lbleps{SortS{}}())]"#,
            ),
            "K4 (sort scope) violated in attribute unit: sort SortS is not declared",
        );
    }

    #[test]
    fn fu23_element_attribute_leaked_sort_panics() {
        assert_violation(
            &theory(SYMBOLS),
            &sentence(
                r#"hooked-sort SortSet{} [hook{}("SET.Set"), element{}(Lblsitem{SortW{}}())]"#,
            ),
            "K4 (sort scope) violated in attribute element: sort SortW is not declared",
        );
    }

    #[test]
    fn fu23_instance_attributes_check_arity_and_scope_on_each_sentence_kind() {
        let theory = theory(SYMBOLS);
        for key in ["element", "unit", "concat", "update"] {
            for declaration in [
                "sort SortSet{W}",
                "symbol Lblf{W}(W) : W",
                "alias Lbla{W}() : W where Lbla{W}() := Lbleps{W}()",
                r"axiom{W} \top{W}()",
                r"claim{W} \top{W}()",
            ] {
                let with =
                    |argument: &str| sentence(&format!("{declaration} [{key}{{}}({argument})]"));
                assert_eq!(violation(&theory, &with("Lbleps{W}()")), None);
                assert_violation(
                    &theory,
                    &with("Lbleps{}()"),
                    &format!(
                        "K5 (symbol arity) violated: symbol Lbleps is declared with 1 sort parameters but applied to 0 in attribute {key}"
                    ),
                );
                assert_violation(
                    &theory,
                    &with("Lblmissing{}()"),
                    &format!(
                        "K5 (symbol arity) violated: symbol Lblmissing is not declared in attribute {key}"
                    ),
                );
                assert_violation(
                    &theory,
                    &with("Lbleps{S}()"),
                    &format!(
                        "K4 (sort scope) violated in attribute {key}: sort variable S is not bound by the sentence"
                    ),
                );
                assert_violation(
                    &theory,
                    &with("Lbleps{SortFoo{SortFoo{}}}()"),
                    &format!(
                        "K4 (sort scope) violated in attribute {key}: sort SortFoo is declared with 0 parameters but applied to 1"
                    ),
                );
            }
        }
    }

    #[test]
    fn fu23_instantiated_unit_and_syntax_metadata_pass() {
        let theory = theory(SYMBOLS);
        let unit = sentence(
            r#"symbol Lblcat{}(SortFoo{}, SortFoo{}) : SortFoo{} [unit{}(Lbleps{SortFoo{}}())]"#,
        );
        assert_eq!(violation(&theory, &unit), None);
        let syntax = sentence(
            r#"symbol Lblcat{}(SortFoo{}, SortFoo{}) : SortFoo{} [priorities{}(Lbleps{}()), left{}(Lbleps{}()), right{}(Lbleps{}()), format{}(Lbleps{}())]"#,
        );
        assert_eq!(violation(&theory, &syntax), None);
    }

    #[test]
    fn fu23_prelude_injection_has_two_sort_parameters() {
        let theory = theory(THEORY);
        assert_eq!(
            violation(
                &theory,
                &sentence(r#"axiom{} inj{SortCounter{}, SortNat{}}(X:SortCounter{}) []"#)
            ),
            None
        );
        assert_violation(
            &theory,
            &sentence(r#"axiom{} inj{SortCounter{}}(X:SortCounter{}) []"#),
            "K5 (symbol arity) violated: symbol inj is declared with 2 sort parameters but applied to 1",
        );
    }

    #[test]
    fn fu23_attribute_arity_precedes_signature_and_pattern_sort_scope() {
        let theory = theory(SYMBOLS);
        for text in [
            r#"symbol Lblf{}(SortMissing{}) : SortFoo{} [unit{}(Lbleps{}())]"#,
            r#"axiom{} \top{SortMissing{}}() [unit{}(Lbleps{}())]"#,
        ] {
            assert_violation(
                &theory,
                &sentence(text),
                "K5 (symbol arity) violated: symbol Lbleps is declared with 1 sort parameters but applied to 0",
            );
        }
    }

    #[test]
    fn fu23_unlowered_semantic_cast_is_not_a_declared_symbol() {
        assert_violation(
            &theory(SYMBOLS),
            &sentence(r#"axiom{} Lbl'Hash'SemanticCastToInt{}(X:SortFoo{}) []"#),
            "K5 (symbol arity) violated: symbol Lbl'Hash'SemanticCastToInt is not declared",
        );
    }

    #[test]
    #[should_panic(
        expected = "K5 (symbol arity) violated: symbol Lbleps is declared with 1 sort parameters but applied to 0"
    )]
    fn fu23_generated_unit_axiom_arity_precedes_declaration_attribute_scope() {
        let module = parse_module(
            r#"
            module MAIN
              sort SortFoo{} []
              symbol Lbleps{S}() : S []
              symbol Lblcat{}(SortFoo{}, SortFoo{}) : SortFoo{} [unit{}(Lbleps{SortS{}}())]
              axiom{R} \equals{SortFoo{}, R}(Lblcat{}(K:SortFoo{}, Lbleps{}()), K:SortFoo{}) []
            endmodule []
        "#,
        )
        .expect("the test theory parses");
        EmittedTheory::of(&module).check_module(&module);
    }

    #[test]
    fn source_without_origin_record_says_so() {
        assert_eq!(emitted_from("main.k:3", None), "main.k:3 (origin: none)");
    }
}
