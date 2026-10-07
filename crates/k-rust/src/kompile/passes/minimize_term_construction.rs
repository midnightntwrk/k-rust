//! ```toml algorithm
//! id = "kompile.terms.minimize"
//! name = "minimization of repeated term construction"
//! sites = ["minimize_term_construction", "minimize_term_construction_pass", "Minimizer::gather_terms", "Minimizer::transform"]
//! variable = "N = rule term nodes; h = term height"
//! counters = []
//! no_counter = "term-construction minimization has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one rule"
//! bound = "O(N log N): each subterm is numbered once from its head and its children's numbers (equal numbers exactly for equal subterms), and the reused subterms are found by number"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Reuse LHS subterms that also occur on a rule RHS through `#as` aliases.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{Definition, LabelHead, ProductionCatalog, Sentence},
    kast::{InternalLabel, Label, Sort, Term},
    kompile::fresh_names::FreshNames,
    provenance::GeneratingPass,
};

use super::super::{TermConversionError, TermConverter};

/// Apply Java's final `MinimizeTermConstruction` transformation before KORE emission.
pub fn minimize_term_construction(
    definition: &Definition,
) -> Result<Definition, TermConversionError> {
    super::super::pipeline::run_standalone(
        definition,
        minimize_term_construction_pass,
        Some(GeneratingPass::MinimizeTermConstruction),
    )
}

pub(crate) fn minimize_term_construction_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, TermConversionError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| TermConversionError::Definition(error.clone()))?;
    // Java constructs one minimizer from the final main module and applies it to every
    // sentence visible through that module. In particular, compiler-generated symbols such as
    // `<generatedTop>` may be declared in the main module while occurring in imported rules.
    let main_module = resolved
        .module_id(&input.definition.main_module)
        .expect("resolved definition contains its main module");
    let views = resolved.views();
    let main_productions = views.production_catalog(main_module);
    let main_converter = TermConverter::with_views(&views, main_module)?;
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let converter = TermConverter::with_views(&views, module_id)?;
        for sentence in &mut module.local_sentences {
            // Only non-simplification rules change. The kind is decided before taking a mutable
            // sentence, which copies a shared one, so every other sentence stays shared.
            match &**sentence {
                Sentence::Rule { attributes, .. }
                    if !attributes.has(AttributeKey::Simplification) => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = sentence
            else {
                unreachable!("copy-on-write keeps the sentence decided above");
            };
            let fresh = FreshNames::for_terms([&*body, &*requires, &*ensures]);
            let mut identities = Identities::default();
            for term in [&*body, &*requires, &*ensures] {
                identities.number(term);
            }
            let mut minimizer = Minimizer::new(
                productions,
                &converter,
                main_productions,
                &main_converter,
                fresh,
                identities,
            );
            minimizer.gather_terms(body, Position::Both, true, false)?;
            minimizer.gather_terms(requires, Position::Right, true, false)?;
            minimizer.gather_terms(ensures, Position::Right, true, false)?;
            minimizer.filter_rhs(body, Position::Both);
            minimizer.filter_rhs(requires, Position::Right);
            minimizer.filter_rhs(ensures, Position::Right);
            let minimized = [
                minimizer.transform(body, Position::Both, false),
                minimizer.transform(requires, Position::Right, false),
                minimizer.transform(ensures, Position::Right, false),
            ];
            [*body, *requires, *ensures] = minimized;
        }
    }
    Ok(output)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Position {
    Both,
    Left,
    Right,
}

/// The fields of one node that [`Term::cmp`] compares apart from its children: its kind and
/// its label, token or variable with their sorts. Annotations are not among them.
#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum Head {
    InjectedLabel(Label),
    Rewrite,
    As,
    Variable(String, Option<Sort>),
    Sequence,
    Apply(Label),
    Token(String, Sort),
}

/// One number per distinct subterm of the terms of one rule, so that two subterms are equal
/// under [`Term::cmp`] exactly when their numbers are equal: a node is numbered by its head and
/// its children's numbers, and each such key is given one number.
///
/// By induction on terms, equal terms have equal heads and pairwise equal children, so equal
/// keys and one number; and two terms with one number have one key, so equal heads and
/// children with equal numbers, which are equal terms. A node's number is found by its
/// address, so the subterms are read in place: deciding whether two subterms are equal costs no
/// walk over them, and recording one costs no copy of it.
#[derive(Default)]
struct Identities {
    /// The number of each node numbered, by the address of the node with its annotations
    /// removed ([`Term::unannotated`]).
    numbers: HashMap<*const Term, u32>,
    /// The number of each key.
    keys: BTreeMap<(Head, Vec<u32>), u32>,
}

impl Identities {
    /// Number every subterm of `root`, children before their parents, without recursion.
    fn number(&mut self, root: &Term) {
        let mut pending = vec![(root.unannotated(), false)];
        // Invariant: a node is pushed unexpanded, then expanded above its children; when it is
        // popped expanded, every child has been numbered.
        while let Some((term, expanded)) = pending.pop() {
            let address = std::ptr::from_ref(term);
            if self.numbers.contains_key(&address) {
                continue;
            }
            if !expanded {
                pending.push((term, true));
                pending.extend(subterms(term).into_iter().map(|child| (child, false)));
                continue;
            }
            let head = match term {
                Term::InjectedLabel(label) => Head::InjectedLabel(label.clone()),
                Term::Rewrite { .. } => Head::Rewrite,
                Term::As { .. } => Head::As,
                Term::Variable { name, sort } => Head::Variable(name.clone(), sort.clone()),
                Term::Sequence(_) => Head::Sequence,
                Term::Apply { label, .. } => Head::Apply(label.clone()),
                Term::Token { token, sort } => Head::Token(token.clone(), sort.clone()),
                Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
            };
            let children = subterms(term)
                .into_iter()
                .map(|child| self.numbers[&std::ptr::from_ref(child)])
                .collect();
            let next = u32::try_from(self.keys.len()).expect("fewer than 2^32 distinct subterms");
            let number = *self.keys.entry((head, children)).or_insert(next);
            self.numbers.insert(address, number);
        }
    }

    /// The number of `term`, a subterm of a numbered term.
    fn of(&self, term: &Term) -> u32 {
        self.numbers[&std::ptr::from_ref(term.unannotated())]
    }
}

struct Minimizer<'use_, 'view, 'definition> {
    productions: &'use_ ProductionCatalog<'definition>,
    converter: &'use_ TermConverter<'view, 'definition>,
    main_productions: &'use_ ProductionCatalog<'definition>,
    main_converter: &'use_ TermConverter<'view, 'definition>,
    fresh: FreshNames,
    identities: Identities,
    /// The variable that names each left-position subterm gathered, by its number.
    cache: HashMap<u32, Term>,
    /// The numbers of the gathered subterms that also occur in a right position.
    used_on_rhs: HashSet<u32>,
}

impl<'use_, 'view, 'definition> Minimizer<'use_, 'view, 'definition> {
    fn new(
        productions: &'use_ ProductionCatalog<'definition>,
        converter: &'use_ TermConverter<'view, 'definition>,
        main_productions: &'use_ ProductionCatalog<'definition>,
        main_converter: &'use_ TermConverter<'view, 'definition>,
        fresh: FreshNames,
        identities: Identities,
    ) -> Self {
        Self {
            productions,
            converter,
            main_productions,
            main_converter,
            fresh,
            identities,
            cache: HashMap::new(),
            used_on_rhs: HashSet::new(),
        }
    }

    // Invariant: `self.cache` maps each left-position subterm visited so far that is not the root, a variable, or `true`, and is not under `in_bad`, to a fresh variable; each call recurses into the immediate subterms of `term` except below blocked collection hooks and `Or`, so the finite `term` bounds the visit.
    fn gather_terms(
        &mut self,
        term: &Term,
        position: Position,
        root: bool,
        in_bad: bool,
    ) -> Result<(), TermConversionError> {
        crate::stack::guarded(|| self.gather_level(term, position, root, in_bad))
    }

    /// One level of [`Self::gather_terms`], which runs it with stack for one more level.
    fn gather_level(
        &mut self,
        term: &Term,
        position: Position,
        root: bool,
        in_bad: bool,
    ) -> Result<(), TermConversionError> {
        let term = term.unannotated();
        let identity = self.identities.of(term);
        if position == Position::Left
            && !in_bad
            && !root
            && !matches!(term, Term::Variable { .. })
            && !is_true(term)
            && !self.cache.contains_key(&identity)
        {
            let sort = match self.converter.infer_sort(term) {
                Ok(sort) => sort,
                Err(local_error) => self
                    .main_converter
                    .infer_sort(term)
                    .map_err(|_| local_error)?,
            };
            let variable = self.new_variable(sort);
            self.cache.insert(identity, variable);
        }
        match term {
            Term::Rewrite { left, right } => {
                self.gather_terms(left, Position::Left, root, in_bad)?;
                self.gather_terms(right, Position::Right, false, in_bad)?;
            }
            Term::As { pattern, alias } => {
                self.gather_terms(pattern, position, false, in_bad)?;
                self.gather_terms(alias, position, false, in_bad)?;
            }
            Term::Apply { label, arguments } => {
                let hook = self.hook(label);
                if is_blocked_collection_hook(hook) || label.is(InternalLabel::Or) {
                    return Ok(());
                }
                if hook == Some("MAP.element") {
                    if let Some(value) = arguments.get(1) {
                        self.gather_terms(value, position, false, in_bad)?;
                    }
                    return Ok(());
                }
                for argument in arguments {
                    self.gather_terms(argument, position, false, in_bad)?;
                }
            }
            Term::Sequence(items) => {
                for item in items {
                    self.gather_terms(item, position, false, in_bad)?;
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
        Ok(())
    }

    // Invariant: `self.used_on_rhs` holds every right-position subterm visited so far that is a key of `self.cache`; the recursion stops at such a subterm and otherwise descends into the immediate subterms of `term`, so the finite `term` bounds the calls.
    fn filter_rhs(&mut self, term: &Term, position: Position) {
        crate::stack::guarded(|| self.filter_level(term, position));
    }

    /// One level of [`Self::filter_rhs`], which runs it with stack for one more level.
    fn filter_level(&mut self, term: &Term, position: Position) {
        let term = term.unannotated();
        let identity = self.identities.of(term);
        if position == Position::Right && self.cache.contains_key(&identity) {
            self.used_on_rhs.insert(identity);
            return;
        }
        match term {
            Term::Rewrite { left, right } => {
                self.filter_rhs(left, Position::Left);
                self.filter_rhs(right, Position::Right);
            }
            Term::As { pattern, alias } => {
                self.filter_rhs(pattern, position);
                self.filter_rhs(alias, position);
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => {
                for item in items {
                    self.filter_rhs(item, position);
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }

    // Invariant: a right-position `term` that is a key of `self.cache` becomes its variable without descending; otherwise each call rebuilds `term` from its transformed immediate subterms, so the finite `term` bounds the recursion.
    fn transform(&self, term: &Term, position: Position, in_bad: bool) -> Term {
        crate::stack::guarded(|| self.transform_level(term, position, in_bad))
    }

    /// One level of [`Self::transform`], which runs it with stack for one more level.
    fn transform_level(&self, term: &Term, position: Position, in_bad: bool) -> Term {
        let identity = self.identities.of(term);
        if position == Position::Right
            && let Some(variable) = self.cache.get(&identity)
        {
            return variable.clone();
        }
        let metadata = term.metadata().cloned();
        let bare = term.unannotated();
        let transformed = match bare {
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.transform(left, Position::Left, in_bad)),
                right: Box::new(self.transform(right, Position::Right, in_bad)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.transform(pattern, position, in_bad)),
                alias: Box::new(self.transform(alias, position, in_bad)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .iter()
                    .map(|item| self.transform(item, position, in_bad))
                    .collect(),
            ),
            Term::Apply { label, arguments } => {
                let hook = self.hook(label);
                let arguments = if hook == Some("MAP.element") {
                    arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| self.transform(argument, position, index == 0))
                        .collect()
                } else {
                    let blocked =
                        in_bad || is_blocked_collection_hook(hook) || label.is(InternalLabel::Or);
                    arguments
                        .iter()
                        .map(|argument| self.transform(argument, position, blocked))
                        .collect()
                };
                Term::Apply {
                    label: label.clone(),
                    arguments,
                }
            }
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
                leaf.clone()
            }
            Term::Annotated { .. } => unreachable!(),
        };
        let transformed = match metadata {
            Some(metadata) => transformed.with_metadata(metadata),
            None => transformed,
        };
        if position == Position::Left
            && !in_bad
            && self.used_on_rhs.contains(&identity)
            && let Some(variable) = self.cache.get(&identity)
        {
            Term::As {
                pattern: Box::new(transformed),
                alias: Box::new(variable.clone()),
            }
        } else {
            transformed
        }
    }

    fn new_variable(&mut self, sort: Sort) -> Term {
        Term::Variable {
            name: self.fresh.mint("_Gen"),
            sort: Some(sort),
        }
    }

    fn hook(&self, label: &crate::kast::Label) -> Option<&str> {
        self.productions
            .attributes_for(&LabelHead::from(label))
            .or_else(|| {
                self.main_productions
                    .attributes_for(&LabelHead::from(label))
            })
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
    }
}

/// The children of `term`, each with its annotations removed ([`Term::unannotated`]).
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants have children"
)]
fn subterms(term: &Term) -> Vec<&Term> {
    match term.unannotated() {
        Term::Rewrite { left, right } => vec![left.unannotated(), right.unannotated()],
        Term::As { pattern, alias } => vec![pattern.unannotated(), alias.unannotated()],
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().map(Term::unannotated).collect(),
        _ => Vec::new(),
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term,
        Term::Token { token, sort } if token == "true" && sort.name == BuiltinSort::Bool.k_name()
    )
}

fn is_blocked_collection_hook(hook: Option<&str>) -> bool {
    matches!(
        hook,
        Some("SET.element" | "LIST.element" | "LIST.concat" | "MAP.concat" | "SET.concat")
    )
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use std::collections::BTreeMap;

    use crate::{
        definition::Sentence,
        kast::Term,
        kompile::stage_harness::{labelled, run_to_stage},
    };

    /// Undo minimization: replace every alias variable on the right-hand side by the
    /// left-hand subterm it names, and drop the `#as` bindings.
    fn expand(term: &Term, aliases: &BTreeMap<String, Term>) -> Term {
        match term {
            Term::As { pattern, .. } => expand(pattern, aliases),
            Term::Variable { name, .. } if aliases.contains_key(name) => {
                expand(&aliases[name], aliases)
            }
            Term::Annotated { term, .. } => expand(term, aliases),
            Term::Apply { label, arguments } => Term::Apply {
                label: label.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| expand(argument, aliases))
                    .collect(),
            },
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(expand(left, aliases)),
                right: Box::new(expand(right, aliases)),
            },
            Term::Sequence(items) => {
                Term::Sequence(items.iter().map(|item| expand(item, aliases)).collect())
            }
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
                leaf.clone()
            }
        }
    }

    fn collect_aliases(term: &Term, aliases: &mut BTreeMap<String, Term>) {
        match term {
            Term::As { pattern, alias } => {
                if let Term::Variable { name, .. } = alias.unannotated() {
                    aliases.insert(name.clone(), (**pattern).clone());
                }
                collect_aliases(pattern, aliases);
            }
            Term::Annotated { term, .. } => collect_aliases(term, aliases),
            Term::Apply { arguments, .. } => arguments
                .iter()
                .for_each(|argument| collect_aliases(argument, aliases)),
            Term::Rewrite { left, right } => {
                collect_aliases(left, aliases);
                collect_aliases(right, aliases);
            }
            Term::Sequence(items) => items.iter().for_each(|item| collect_aliases(item, aliases)),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
        }
    }

    /// A right-hand side that rebuilds a subterm the left-hand side matched can reuse the
    /// matched term instead of constructing it again: the stage binds the subterm with `#as`
    /// on the left and names it on the right. The rule means the same thing, so substituting
    /// each alias back gives the rule the stage received, and here the repeated
    /// `pair(V, E)` is shared rather than rebuilt.
    #[test]
    fn a_rebuilt_left_hand_subterm_is_shared_and_the_rule_keeps_its_meaning() {
        let run = run_to_stage(
            r#"
module MAIN
  syntax K
  syntax Val ::= "v" [symbol(v)]
  syntax Exp ::= Val | pair(Exp, Exp) [symbol(pair)] | wrap(Exp) [symbol(wrap)]
  configuration <k> v </k>
  rule <k> pair(V:Val, E) => pair(E, wrap(pair(V:Val, E))) </k> [label(swap)]
endmodule
"#,
            "minimize term construction",
        );
        let body = |definition| match labelled(definition, "MAIN", "swap")[..] {
            [Sentence::Rule { body, .. }] => body.clone(),
            ref other => panic!("{other:?}"),
        };
        let (before, after) = (body(&run.input), body(run.output()));
        let mut aliases = BTreeMap::new();
        collect_aliases(&after, &mut aliases);
        assert_eq!(aliases.len(), 1, "{after}");
        let (alias, shared) = aliases.iter().next().unwrap();
        assert_eq!(shared.to_string(), "pair(inj{Val,Exp}(V),E)");
        let Term::Rewrite { right, .. } = after.unannotated() else {
            panic!("{after}")
        };
        assert!(
            right.to_string().contains(&format!("wrap({alias})")),
            "{after}"
        );
        assert_eq!(
            expand(&after, &aliases).to_string(),
            expand(&before, &BTreeMap::new()).to_string()
        );
    }
}
