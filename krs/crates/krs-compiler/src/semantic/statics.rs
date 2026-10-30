//! Static rewriting modes: alias and desugar clauses (KF-028).
//!
//! A production marked `#[k::alias]` or `#[k::desugar]` (K's `alias` or
//! `macro`, `-rec` when `recursive`) is expanded before anything runs by the
//! clauses written for it. A clause takes its production's mode: an
//! `#[k::alias]` clause expands an alias production and a `#[k::desugar]`
//! clause a desugar production. An alias or desugar production that no clause
//! expands is reported, because nothing would ever replace it.
//!
//! A clause's subject is matched by static expansion against a program's terms
//! as they are written, before anything evaluates. So KRS emits it as that
//! match reads it:
//! - an application of an alias or desugar production below its root is
//!   expanded ([`Expansion`]): a program's application of the production is
//!   expanded before the clause is tried, so the clause matches the expansion,
//!   and `dn(x, zero())` means `dn(x, red)` where `zero()` expands to `red`, as
//!   it does in a rule's pattern, which the definition's own expansion
//!   rewrites. KRS expands it only where the expansion needs no value: its
//!   arguments are ground, or the production is not recursive and has one
//!   clause, whose parameters are plain names. Otherwise which term the
//!   application stands for depends on what a program writes, and it is
//!   refused;
//! - a desugar clause's alternatives `A | B` become one clause per alternative
//!   ([`alternatives`]): static expansion does not match an or-pattern, and a
//!   desugar runs only forward, so `A | B` means "either", which one clause
//!   each states exactly. An alias clause's subject holds no `|` (NT-Q5);
//! - a Bytes token is written as a program writes it
//!   ([`krs_ir::bytes_token::program_spelling`]): static expansion compares
//!   tokens as they are written.
//!
//! An alias clause also runs backwards: when a result is printed, each term its result matches
//! prints as its subject, built from what the match bound. So below its root the subject holds
//! nothing printing cannot build (`reversible_subject`); the constructs the expander's walker
//! refuses by their spelling are refused there.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinSort, GrammarProductionItemKind, NodeOrigin, ProductionAttribute,
    SemanticId, SemanticIdKind, SentenceKind, SourceMapKey, StableItemId,
};
use krs_ir_levels::{
    IrTermKind, ListOperands, MapOperands, SemanticModule, SemanticRule, SemanticSortRef,
    SemanticTerm, SemanticVariable, SetOperands,
};

use super::catalog::semantic_is_subsort;
use super::error::DescriptorLoweringError;
use crate::partition::production_display_name;

/// The most static applications KRS expands in one clause's subject, counting
/// each recursive step: a recursive production's ground expansion that has not
/// ended by then is refused.
const EXPANSION_STEPS: usize = 10_000;

/// The static mode of a production marker, with its attribute origin.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Mode {
    Alias,
    Desugar,
}

impl Mode {
    const fn attribute(self) -> &'static str {
        match self {
            Self::Alias => "#[k::alias]",
            Self::Desugar => "#[k::desugar]",
        }
    }

    const fn recursive_attribute(self) -> &'static str {
        match self {
            Self::Alias => "#[k::alias(recursive)]",
            Self::Desugar => "#[k::desugar(recursive)]",
        }
    }

    const fn clause(self) -> &'static str {
        match self {
            Self::Alias => "alias",
            Self::Desugar => "desugar",
        }
    }
}

/// One alias or desugar production: its mode, the marker's origin, and whether
/// it is recursive.
struct StaticProduction<'m> {
    mode: Mode,
    origin: &'m NodeOrigin,
    recursive: bool,
}

/// The productions of the modules: the static ones with their clauses, which
/// productions are functions, and each production's argument sorts.
struct Productions<'m> {
    statics: BTreeMap<&'m StableItemId, StaticProduction<'m>>,
    clauses: BTreeMap<&'m StableItemId, Vec<&'m SemanticRule>>,
    functions: BTreeSet<&'m StableItemId>,
    arguments: BTreeMap<&'m StableItemId, Vec<&'m SemanticSortRef>>,
    sort_parents: &'m BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
}

impl<'m> Productions<'m> {
    fn of(
        modules: &'m [SemanticModule],
        sort_parents: &'m BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    ) -> Self {
        let mut productions = Self {
            statics: BTreeMap::new(),
            clauses: BTreeMap::new(),
            functions: BTreeSet::new(),
            arguments: BTreeMap::new(),
            sort_parents,
        };
        for production in modules.iter().flat_map(SemanticModule::productions) {
            productions.arguments.insert(
                production.id(),
                production
                    .items()
                    .iter()
                    .filter_map(|item| match item.kind() {
                        GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
                        GrammarProductionItemKind::Terminal { .. }
                        | GrammarProductionItemKind::RegexTerminal { .. } => None,
                    })
                    .collect(),
            );
            for attribute in production.attributes() {
                let (mode, recursive) = match attribute {
                    ProductionAttribute::Alias { recursive, .. } => (Mode::Alias, *recursive),
                    ProductionAttribute::Desugar { recursive, .. } => (Mode::Desugar, *recursive),
                    ProductionAttribute::Function { .. } => {
                        productions.functions.insert(production.id());
                        continue;
                    }
                    _ => continue,
                };
                productions.statics.insert(
                    production.id(),
                    StaticProduction {
                        mode,
                        origin: attribute.origin(),
                        recursive,
                    },
                );
            }
        }
        for rule in modules.iter().flat_map(SemanticModule::rules) {
            if let Some(head) = clause_head(rule) {
                productions.clauses.entry(head).or_default().push(rule);
            }
        }
        productions
    }

    fn is_static(&self, production: &StableItemId) -> bool {
        self.statics.contains_key(production)
    }

    /// Whether `application` applies a function: a declared function, a builtin operation that is
    /// one, or a sort's generated predicate or projection.
    fn is_function(&self, application: &ApplicationRef<StableItemId, SemanticSortRef>) -> bool {
        match application {
            ApplicationRef::Declared(production) => self.functions.contains(production),
            ApplicationRef::Builtin(operation) => operation.is_functional(),
            ApplicationRef::Generated(_) => true,
        }
    }

    fn is_subsort(&self, candidate: &SemanticSortRef, expected: &SemanticSortRef) -> bool {
        semantic_is_subsort(candidate, expected, self.sort_parents)
    }
}

/// The production a static clause expands: the head of its subject's root.
fn clause_head(rule: &SemanticRule) -> Option<&StableItemId> {
    if !matches!(rule.kind(), SentenceKind::Alias | SentenceKind::Desugar) {
        return None;
    }
    match rule.body()?.from().kind() {
        IrTermKind::Application {
            application: ApplicationRef::Declared(production),
            ..
        } => Some(production),
        _ => None,
    }
}

/// Checks every alias and desugar clause against its head production, and every alias and
/// desugar production for a clause, in stable module order; then returns the modules with each
/// static clause as KRS emits it (the module documentation).
pub(super) fn static_clauses(
    modules: Vec<SemanticModule>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<Vec<SemanticModule>, DescriptorLoweringError> {
    let productions = Productions::of(&modules, sort_parents);
    let mut expanded = BTreeSet::<&StableItemId>::new();
    let mut restated = BTreeMap::<StableItemId, Vec<SemanticRule>>::new();
    let mut copies = 0_usize;
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        let mode = match rule.kind() {
            SentenceKind::Alias => Mode::Alias,
            SentenceKind::Desugar => Mode::Desugar,
            _ => continue,
        };
        expanded.insert(check_head(rule, mode, &productions)?);
        let Some(body) = rule.body() else {
            continue;
        };
        let mut expansion = Expansion {
            productions: &productions,
            clause: rule,
            mode,
            steps: EXPANSION_STEPS,
            copies: &mut copies,
        };
        let subject = expansion.subject(body.from())?;
        if mode == Mode::Alias {
            reversible_subject(rule.id(), &subject)?;
        }
        let subjects = if mode == Mode::Desugar {
            alternatives(&subject)
        } else {
            vec![subject]
        };
        let clauses = subjects
            .into_iter()
            .enumerate()
            .map(|(index, subject)| restate(rule, index, &written_tokens(&subject)))
            .collect::<Result<Vec<_>, _>>()?;
        restated.insert(rule.id().clone(), clauses);
    }
    check_every_production_expanded(&productions, &expanded)?;
    Ok(modules
        .into_iter()
        .map(|module| {
            if !module
                .rules()
                .iter()
                .any(|rule| restated.contains_key(rule.id()))
            {
                return module;
            }
            let rules = module
                .rules()
                .iter()
                .flat_map(|rule| {
                    restated
                        .remove(rule.id())
                        .unwrap_or_else(|| vec![rule.clone()])
                })
                .collect();
            module.with_rules(rules)
        })
        .collect())
}

/// Checks an alias or desugar clause, of mode `clause`, against its head production, which it
/// returns.
fn check_head<'m>(
    rule: &'m SemanticRule,
    clause: Mode,
    productions: &Productions<'_>,
) -> Result<&'m StableItemId, DescriptorLoweringError> {
    let head = rule.body().and_then(|body| match body.from().kind() {
        IrTermKind::Application {
            application: ApplicationRef::Declared(production),
            ..
        } => Some(production),
        _ => None,
    });
    let name = rule.id().item_name();
    // The clause's root is the production it expands, so a root that is none is the root's
    // mistake: it is reported there, or at the clause when the root has no range of its own.
    let at = rule
        .body()
        .map(|body| body.from().origin())
        .filter(|origin| origin.origin().exact_authored_range().is_some())
        .unwrap_or_else(|| rule.origin());
    let Some(head) = head else {
        return Err(invalid(
            rule.id(),
            format!(
                "{} clause `{name}` must have a production marked `{}` at the head of its pattern",
                clause.clause(),
                clause.attribute(),
            ),
            at,
        ));
    };
    match productions.statics.get(head) {
        Some(production) if production.mode == clause => Ok(head),
        Some(production) => Err(invalid(
            rule.id(),
            format!(
                "{} clause `{name}` expands `{}`, which is marked `{}`: a clause takes its production's mode, so write `{}` on the clause, or `{}` on the production",
                clause.clause(),
                production_display_name(head),
                production.mode.attribute(),
                production.mode.attribute(),
                clause.attribute(),
            ),
            at,
        )),
        None => Err(invalid(
            rule.id(),
            format!(
                "{} clause `{name}` expands `{}`, which is not marked `{}`; mark the production `{}` or `{}`",
                clause.clause(),
                production_display_name(head),
                clause.attribute(),
                clause.attribute(),
                clause.recursive_attribute(),
            ),
            at,
        )),
    }
}

/// Checks every alias and desugar production for a clause that expands it.
fn check_every_production_expanded(
    productions: &Productions<'_>,
    expanded: &BTreeSet<&StableItemId>,
) -> Result<(), DescriptorLoweringError> {
    for (production, StaticProduction { mode, origin, .. }) in &productions.statics {
        if !expanded.contains(production) {
            return Err(invalid(
                production,
                format!(
                    "`{}` is marked `{}` but no `{}` clause expands it, so nothing expands it; add a `{} fn` whose pattern is headed by `{}`",
                    production_display_name(production),
                    mode.attribute(),
                    mode.attribute(),
                    mode.attribute(),
                    production_display_name(production),
                ),
                origin,
            ));
        }
    }
    Ok(())
}

/// The expansion of the static applications below one clause's subject root.
struct Expansion<'p, 'm, 'c> {
    productions: &'p Productions<'m>,
    /// The clause whose subject is expanded.
    clause: &'m SemanticRule,
    mode: Mode,
    /// The applications left to expand before the expansion is refused as endless.
    steps: usize,
    /// The copies of terms made so far, which number the source-map keys of each copy.
    copies: &'c mut usize,
}

/// Whether a clause's subject matches a ground term.
enum Match {
    Yes,
    No,
    /// Telling takes more than comparing constructors, names and tokens.
    Unknown,
}

impl<'m> Expansion<'_, 'm, '_> {
    /// The clause's subject with every static application below its root, the production the
    /// clause expands, expanded.
    fn subject(&mut self, root: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        map_children(root, &mut |argument| self.term(argument, None))
    }

    /// `term` with its static applications expanded, innermost first, as a program's are; a
    /// refusal is told at `site`, the outermost static application the clause's subject writes,
    /// which is `term`'s own when `site` is `None`.
    fn term(
        &mut self,
        term: &SemanticTerm,
        site: Option<&NodeOrigin>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let site = match (site, term.kind()) {
            (
                None,
                IrTermKind::Application {
                    application: ApplicationRef::Declared(production),
                    ..
                },
            ) if self.productions.is_static(production) => Some(term.origin()),
            _ => site,
        };
        let term = map_children(term, &mut |child| self.term(child, site))?;
        match term.kind() {
            IrTermKind::Application {
                application: ApplicationRef::Declared(production),
                arguments,
                ..
            } if self.productions.is_static(production) => self.expand(
                production,
                arguments,
                site.expect("a static application is a site, or below one"),
            ),
            _ => Ok(term),
        }
    }

    /// The expansion of `production` applied to `arguments`, whose own static applications are
    /// expanded.
    fn expand(
        &mut self,
        production: &StableItemId,
        arguments: &[SemanticTerm],
        site: &NodeOrigin,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        if self.steps == 0 {
            return Err(self.refusal(
                production,
                site,
                &format!("expanding it takes more than {EXPANSION_STEPS} steps, so it may not end"),
            ));
        }
        self.steps -= 1;
        let (clause, bindings) = self
            .clause_for(production, arguments)
            .map_err(|reason| self.refusal(production, site, &reason))?;
        let result = clause
            .body()
            .expect("a static clause has a term rewrite")
            .to();
        let expanded = self
            .instantiate(result, &bindings)
            .map_err(|reason| self.refusal(production, site, &reason))?;
        self.term(&expanded, Some(site))
    }

    /// The clause that expands `production` applied to `arguments`, with what its parameters
    /// bind, or why the expansion needs a value.
    fn clause_for(
        &self,
        production: &StableItemId,
        arguments: &[SemanticTerm],
    ) -> Result<(&'m SemanticRule, BTreeMap<SemanticId, SemanticTerm>), String> {
        let clauses = self
            .productions
            .clauses
            .get(production)
            .map_or(&[][..], Vec::as_slice);
        if arguments.iter().all(|argument| self.ground(argument)) {
            self.matching_clause(production, clauses, arguments)
        } else {
            self.only_clause(production, clauses, arguments)
        }
    }

    /// The one clause of `clauses` whose subject matches the ground `arguments`, with what its
    /// names bind.
    fn matching_clause(
        &self,
        production: &StableItemId,
        clauses: &[&'m SemanticRule],
        arguments: &[SemanticTerm],
    ) -> Result<(&'m SemanticRule, BTreeMap<SemanticId, SemanticTerm>), String> {
        let name = production_display_name(production);
        let mut found = None;
        for clause in clauses {
            let root = clause
                .body()
                .expect("a static clause has a term rewrite")
                .from();
            let IrTermKind::Application {
                arguments: parameters,
                ..
            } = root.kind()
            else {
                continue;
            };
            let mut bindings = BTreeMap::new();
            match self.all_match(parameters, arguments, &mut bindings) {
                Match::No => {}
                Match::Unknown => {
                    return Err(format!(
                        "telling which clause of `{name}` matches these arguments takes more than comparing constructors, names and tokens"
                    ));
                }
                Match::Yes if found.is_some() => {
                    return Err(format!(
                        "more than one clause of `{name}` matches these arguments"
                    ));
                }
                Match::Yes => found = Some((*clause, bindings)),
            }
        }
        found.ok_or_else(|| {
            format!(
                "no clause of `{name}` matches these arguments, so a program's application stays unexpanded and this clause never applies"
            )
        })
    }

    /// The only clause of the production, not recursive, whose parameters are plain names, each
    /// bound to its argument, which may not be ground.
    fn only_clause(
        &self,
        production: &StableItemId,
        clauses: &[&'m SemanticRule],
        arguments: &[SemanticTerm],
    ) -> Result<(&'m SemanticRule, BTreeMap<SemanticId, SemanticTerm>), String> {
        let name = production_display_name(production);
        if self.productions.statics[production].recursive {
            return Err(format!(
                "these arguments are not ground, and `{name}` is recursive, so its expansion depends on the values a program gives them"
            ));
        }
        let [clause] = clauses else {
            return Err(format!(
                "these arguments are not ground, and `{name}` has {} clauses, so which one expands it depends on the values a program gives them",
                clauses.len()
            ));
        };
        let root = clause
            .body()
            .expect("a static clause has a term rewrite")
            .from();
        let sorts = self
            .productions
            .arguments
            .get(production)
            .map_or(&[][..], Vec::as_slice);
        let parameters = match root.kind() {
            IrTermKind::Application {
                arguments: parameters,
                ..
            } if parameters.len() == arguments.len() => parameters
                .iter()
                .zip(sorts)
                .map(|(parameter, sort)| match parameter.kind() {
                    IrTermKind::Variable { variable }
                        if self.productions.is_subsort(sort, parameter.sort()) =>
                    {
                        Some(variable)
                    }
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .filter(|parameters| {
                    parameters.iter().collect::<BTreeSet<_>>().len() == parameters.len()
                }),
            _ => None,
        };
        let Some(parameters) = parameters else {
            return Err(format!(
                "these arguments are not ground, and the parameters of `{name}`'s clause are not distinct plain names of its argument sorts, so whether the clause applies depends on the values a program gives them"
            ));
        };
        let result = clause
            .body()
            .expect("a static clause has a term rewrite")
            .to();
        for (index, (parameter, argument)) in parameters.iter().zip(arguments).enumerate() {
            let uses = occurrences(result, parameter);
            if uses == 0
                && let Some(bound) = first_binder(argument)
            {
                return Err(format!(
                    "its clause drops argument {}, which binds `{}` here, so `{}` would have no value",
                    index + 1,
                    bound.as_str(),
                    bound.as_str(),
                ));
            }
            if uses > 1 && !self.determined(argument) {
                return Err(format!(
                    "its clause copies argument {}, which here holds a pattern that matches more than one term apart from its names (`_`, `A | B`, `name @ P`), so each copy would match a term of its own",
                    index + 1
                ));
            }
        }
        let bindings = parameters
            .into_iter()
            .cloned()
            .zip(arguments.iter().cloned())
            .collect();
        Ok((*clause, bindings))
    }

    /// Whether `term` denotes one term, which a program writes as it stands: constructors,
    /// tokens and the collections they build, without a name, a pattern or a function.
    fn ground(&self, term: &SemanticTerm) -> bool {
        let below = || term.children().into_iter().all(|child| self.ground(child));
        match term.kind() {
            IrTermKind::Token { .. } => true,
            IrTermKind::Application { application, .. } => {
                !self.productions.is_function(application)
                    && !matches!(application, ApplicationRef::Declared(production) if self.productions.is_static(production))
                    && below()
            }
            IrTermKind::KSequence { .. } => below(),
            IrTermKind::List(operands) => {
                matches!(
                    **operands,
                    ListOperands::Empty | ListOperands::Item { .. } | ListOperands::Concat { .. }
                ) && below()
            }
            IrTermKind::Set(operands) => {
                matches!(
                    **operands,
                    SetOperands::Empty | SetOperands::Item { .. } | SetOperands::Concat { .. }
                ) && below()
            }
            IrTermKind::Map(operands) => {
                matches!(**operands, MapOperands::Empty | MapOperands::Items(_)) && below()
            }
            IrTermKind::Variable { .. }
            | IrTermKind::Cell { .. }
            | IrTermKind::Rewrite { .. }
            | IrTermKind::As { .. }
            | IrTermKind::Or { .. }
            | IrTermKind::Matches { .. }
            | IrTermKind::Let { .. } => false,
        }
    }

    /// Whether `term` is one term once its names are: constructors, tokens, the collections they
    /// build and names, so that two copies of it, matching their names alike, match one term.
    fn determined(&self, term: &SemanticTerm) -> bool {
        let below = || {
            term.children()
                .into_iter()
                .all(|child| self.determined(child))
        };
        match term.kind() {
            IrTermKind::Variable { variable } => matches!(variable.kind(), SemanticIdKind::Named),
            IrTermKind::Token { .. } => true,
            IrTermKind::Application { application, .. } => {
                !self.productions.is_function(application) && below()
            }
            IrTermKind::KSequence { .. } => below(),
            IrTermKind::List(operands) => {
                matches!(
                    **operands,
                    ListOperands::Empty | ListOperands::Item { .. } | ListOperands::Concat { .. }
                ) && below()
            }
            IrTermKind::Set(operands) => {
                matches!(**operands, SetOperands::Empty | SetOperands::Item { .. }) && below()
            }
            IrTermKind::Map(operands) => matches!(**operands, MapOperands::Empty) && below(),
            IrTermKind::Cell { .. }
            | IrTermKind::Rewrite { .. }
            | IrTermKind::As { .. }
            | IrTermKind::Or { .. }
            | IrTermKind::Matches { .. }
            | IrTermKind::Let { .. } => false,
        }
    }

    /// Whether each parameter matches its ground argument.
    fn all_match(
        &self,
        parameters: &[SemanticTerm],
        arguments: &[SemanticTerm],
        bindings: &mut BTreeMap<SemanticId, SemanticTerm>,
    ) -> Match {
        if parameters.len() != arguments.len() {
            return Match::No;
        }
        let mut unknown = false;
        for (parameter, argument) in parameters.iter().zip(arguments) {
            match self.matches(parameter, argument, bindings) {
                Match::No => return Match::No,
                Match::Unknown => unknown = true,
                Match::Yes => {}
            }
        }
        if unknown { Match::Unknown } else { Match::Yes }
    }

    /// Whether the clause pattern `pattern` matches the ground `term`, as static expansion
    /// compares them: a name binds a term of its sort (the same term where it occurs twice), a
    /// constructor's application or a token matches itself.
    fn matches(
        &self,
        pattern: &SemanticTerm,
        term: &SemanticTerm,
        bindings: &mut BTreeMap<SemanticId, SemanticTerm>,
    ) -> Match {
        match pattern.kind() {
            IrTermKind::Variable { variable } => self.bind(variable, pattern, term, bindings),
            IrTermKind::As {
                alias,
                pattern: aliased,
            } => match self.bind(alias, pattern, term, bindings) {
                Match::Yes => self.matches(aliased, term, bindings),
                other => other,
            },
            IrTermKind::Or { alternatives } => {
                let mut matched = Vec::new();
                for alternative in alternatives.iter() {
                    let mut tried = bindings.clone();
                    match self.matches(alternative, term, &mut tried) {
                        Match::Yes => matched.push(tried),
                        Match::No => {}
                        Match::Unknown => return Match::Unknown,
                    }
                }
                match matched.split_first() {
                    None => Match::No,
                    Some((first, rest)) => {
                        if rest.iter().all(|other| same_bindings(first, other)) {
                            *bindings = first.clone();
                            Match::Yes
                        } else {
                            Match::Unknown
                        }
                    }
                }
            }
            IrTermKind::Token { value } => match term.kind() {
                IrTermKind::Token { value: written } => {
                    if value == written && pattern.sort() == term.sort() {
                        Match::Yes
                    } else {
                        Match::No
                    }
                }
                IrTermKind::Application { .. } => Match::No,
                _ => Match::Unknown,
            },
            IrTermKind::Application {
                application,
                arguments: parameters,
                instance,
                ..
            } => {
                if self.productions.is_function(application)
                    || matches!(application, ApplicationRef::Declared(production) if self.productions.is_static(production))
                {
                    return Match::Unknown;
                }
                match term.kind() {
                    IrTermKind::Application {
                        application: written,
                        arguments,
                        instance: written_instance,
                        ..
                    } => {
                        if application == written && instance == written_instance {
                            self.all_match(parameters, arguments, bindings)
                        } else {
                            Match::No
                        }
                    }
                    IrTermKind::Token { .. } => Match::No,
                    _ => Match::Unknown,
                }
            }
            _ => {
                if same(pattern, term) {
                    Match::Yes
                } else {
                    Match::Unknown
                }
            }
        }
    }

    /// Binds the name `variable`, whose occurrence is `pattern`, to `term`, of the name's sort.
    fn bind(
        &self,
        variable: &SemanticId,
        pattern: &SemanticTerm,
        term: &SemanticTerm,
        bindings: &mut BTreeMap<SemanticId, SemanticTerm>,
    ) -> Match {
        if !self.productions.is_subsort(term.sort(), pattern.sort()) {
            return Match::No;
        }
        match bindings.get(variable) {
            Some(bound) if same(bound, term) => Match::Yes,
            Some(_) => Match::No,
            None => {
                bindings.insert(variable.clone(), term.clone());
                Match::Yes
            }
        }
    }

    /// The clause result `result` with its parameters replaced by what they bind, every node a
    /// copy under fresh source-map keys; or why it is no term this subject can hold.
    fn instantiate(
        &mut self,
        result: &SemanticTerm,
        bindings: &BTreeMap<SemanticId, SemanticTerm>,
    ) -> Result<SemanticTerm, String> {
        let computes = |what: &str| {
            format!(
                "its clause expands it to a term that computes ({what}), which this subject would match as written"
            )
        };
        match result.kind() {
            IrTermKind::Variable { variable } => bindings.get(variable).map_or_else(
                || {
                    Err(format!(
                        "its clause's result holds `{}`, which the clause's subject does not bind",
                        variable.as_str()
                    ))
                },
                |bound| Ok(self.copy(bound)),
            ),
            IrTermKind::Token { .. } => Ok(self.copy(result)),
            IrTermKind::Application { application, .. } => {
                if self.productions.is_function(application) {
                    return Err(computes(match application {
                        ApplicationRef::Declared(_) => "a function's application",
                        ApplicationRef::Builtin(_) => "a builtin function's application",
                        ApplicationRef::Generated(_) => "a sort test",
                    }));
                }
                self.instantiate_children(result, bindings)
            }
            IrTermKind::KSequence { .. } => self.instantiate_children(result, bindings),
            IrTermKind::List(operands)
                if matches!(
                    **operands,
                    ListOperands::Empty | ListOperands::Item { .. } | ListOperands::Concat { .. }
                ) =>
            {
                self.instantiate_children(result, bindings)
            }
            IrTermKind::Set(operands)
                if matches!(
                    **operands,
                    SetOperands::Empty | SetOperands::Item { .. } | SetOperands::Concat { .. }
                ) =>
            {
                self.instantiate_children(result, bindings)
            }
            IrTermKind::Map(operands)
                if matches!(**operands, MapOperands::Empty | MapOperands::Items(_)) =>
            {
                self.instantiate_children(result, bindings)
            }
            IrTermKind::List(_) | IrTermKind::Set(_) | IrTermKind::Map(_) => {
                Err(computes("a collection's function"))
            }
            IrTermKind::Let { .. } => Err(computes("a `let` block")),
            IrTermKind::Matches { .. } => Err(computes("`k::matches!`")),
            IrTermKind::Cell { .. } => Err(computes("a cell fragment")),
            IrTermKind::Rewrite { .. } | IrTermKind::As { .. } | IrTermKind::Or { .. } => {
                Err(computes("a pattern"))
            }
        }
    }

    fn instantiate_children(
        &mut self,
        result: &SemanticTerm,
        bindings: &BTreeMap<SemanticId, SemanticTerm>,
    ) -> Result<SemanticTerm, String> {
        let instantiated = map_children(result, &mut |child| self.instantiate(child, bindings))?;
        let origin = self.fresh(result.origin());
        Ok(instantiated.with_origin(origin))
    }

    /// `term` under fresh source-map keys, which no node of the theory has.
    fn copy(&mut self, term: &SemanticTerm) -> SemanticTerm {
        term.map_origins(&mut |origin| self.fresh(origin))
    }

    /// `origin` under a fresh source-map key, which no node of the theory has.
    fn fresh(&mut self, origin: &NodeOrigin) -> NodeOrigin {
        *self.copies += 1;
        suffixed(origin, &format!("~expansion-{}", self.copies))
    }

    /// The refusal of the static application of `production` at `site`, for `reason`.
    fn refusal(
        &self,
        production: &StableItemId,
        site: &NodeOrigin,
        reason: &str,
    ) -> DescriptorLoweringError {
        let name = production_display_name(production);
        DescriptorLoweringError::InvalidStaticClause {
            reason: format!(
                "{} clause `{}`: `{name}` is marked `{}`, so a program's `{name}` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but {reason}: write the term it expands to instead",
                self.mode.clause(),
                self.clause.id().item_name(),
                self.productions.statics[production].mode.attribute(),
            ),
            range: site.origin().exact_authored_range().map(Box::new),
            item: Some(Box::new(self.clause.id().clone())),
        }
    }
}

/// How many times `variable` occurs in `term`.
fn occurrences(term: &SemanticTerm, variable: &SemanticId) -> usize {
    let here = usize::from(
        matches!(term.kind(), IrTermKind::Variable { variable: name } if name == variable),
    );
    here + term
        .children()
        .into_iter()
        .map(|child| occurrences(child, variable))
        .sum::<usize>()
}

/// The first name `term` binds: a named variable, or an alias's.
fn first_binder(term: &SemanticTerm) -> Option<&SemanticId> {
    match term.kind() {
        IrTermKind::Variable { variable } if matches!(variable.kind(), SemanticIdKind::Named) => {
            Some(variable)
        }
        IrTermKind::As { alias, .. } => Some(alias),
        _ => term.children().into_iter().find_map(first_binder),
    }
}

/// Whether two terms are the same term, wherever each was written.
fn same(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    let origin = left.origin().clone();
    left.map_origins(&mut |_| origin.clone()) == right.map_origins(&mut |_| origin.clone())
}

fn same_bindings(
    left: &BTreeMap<SemanticId, SemanticTerm>,
    right: &BTreeMap<SemanticId, SemanticTerm>,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|((left_name, left), (right_name, right))| {
                left_name == right_name && same(left, right)
            })
}

/// `origin` under the source-map key `suffix` extends.
fn suffixed(origin: &NodeOrigin, suffix: &str) -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new(format!("{}{suffix}", origin.key().as_str()))
            .expect("a source-map key extended by a separator-free suffix is a key"),
        origin.origin().clone(),
    )
}

/// `term` with each child replaced by `map`'s image of it, in [`SemanticTerm::children`]'s order.
fn map_children<E>(
    term: &SemanticTerm,
    map: &mut impl FnMut(&SemanticTerm) -> Result<SemanticTerm, E>,
) -> Result<SemanticTerm, E> {
    let kind = match term.kind() {
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => return Ok(term.clone()),
        IrTermKind::Application {
            application,
            arguments,
            instance,
            head_instance_fixed,
        } => IrTermKind::Application {
            application: application.clone(),
            arguments: arguments.iter().map(&mut *map).collect::<Result<_, _>>()?,
            instance: instance.clone(),
            head_instance_fixed: *head_instance_fixed,
        },
        IrTermKind::KSequence { item_sort, items } => IrTermKind::KSequence {
            item_sort: item_sort.clone(),
            items: items.iter().map(&mut *map).collect::<Result<_, _>>()?,
        },
        IrTermKind::Map(operands) => IrTermKind::Map(Box::new(operands.try_map_ref(&mut *map)?)),
        IrTermKind::List(operands) => IrTermKind::List(Box::new(operands.try_map_ref(&mut *map)?)),
        IrTermKind::Set(operands) => IrTermKind::Set(Box::new(operands.try_map_ref(&mut *map)?)),
        IrTermKind::Cell { cell, children } => IrTermKind::Cell {
            cell: cell.clone(),
            children: children.iter().map(&mut *map).collect::<Result<_, _>>()?,
        },
        IrTermKind::Rewrite { from, to } => IrTermKind::Rewrite {
            from: Box::new(map(from)?),
            to: Box::new(map(to)?),
        },
        IrTermKind::As { alias, pattern } => IrTermKind::As {
            alias: alias.clone(),
            pattern: Box::new(map(pattern)?),
        },
        IrTermKind::Or { alternatives } => IrTermKind::Or {
            alternatives: alternatives.try_map_ref(&mut *map)?,
        },
        IrTermKind::Matches {
            subject,
            pattern,
            binds,
        } => IrTermKind::Matches {
            subject: Box::new(map(subject)?),
            pattern: Box::new(map(pattern)?),
            binds: binds.clone(),
        },
        IrTermKind::Let {
            pattern,
            value,
            body,
            binds,
        } => IrTermKind::Let {
            pattern: Box::new(map(pattern)?),
            value: Box::new(map(value)?),
            body: Box::new(map(body)?),
            binds: binds.clone(),
        },
    };
    Ok(term.with_kind(kind))
}

/// The alternatives of a desugar clause's subject, each one term with no `A | B` in it: a
/// production's application, an alias and a collection distribute over the alternatives of
/// each operand, as matching does (`f(A | B)` matches what `f(A)` or `f(B)` does).
fn alternatives(term: &SemanticTerm) -> Vec<SemanticTerm> {
    if let IrTermKind::Or {
        alternatives: branches,
    } = term.kind()
    {
        return branches.iter().flat_map(alternatives).collect();
    }
    let choices = term
        .children()
        .into_iter()
        .map(alternatives)
        .collect::<Vec<_>>();
    if choices.iter().all(|choice| choice.len() == 1) {
        return vec![term.clone()];
    }
    let mut combinations = vec![Vec::new()];
    for choice in &choices {
        combinations = combinations
            .into_iter()
            .flat_map(|combination: Vec<&SemanticTerm>| {
                choice.iter().map(move |child| {
                    let mut combination = combination.clone();
                    combination.push(child);
                    combination
                })
            })
            .collect();
    }
    combinations
        .into_iter()
        .map(|combination| {
            let mut children = combination.into_iter();
            map_children(term, &mut |_| {
                Ok::<_, std::convert::Infallible>(
                    children
                        .next()
                        .expect("a combination holds one alternative per child")
                        .clone(),
                )
            })
            .unwrap_or_else(|never| match never {})
        })
        .collect()
}

/// `subject` with each Bytes token in the spelling a program writes it in.
fn written_tokens(subject: &SemanticTerm) -> SemanticTerm {
    match subject.kind() {
        IrTermKind::Token { value }
            if *subject.sort() == SemanticSortRef::Builtin(BuiltinSort::Bytes) =>
        {
            krs_ir::bytes_token::decode(value).map_or_else(
                |_| subject.clone(),
                |bytes| {
                    subject.with_kind(IrTermKind::Token {
                        value: krs_ir::bytes_token::program_spelling(&bytes),
                    })
                },
            )
        }
        _ => map_children(subject, &mut |child| {
            Ok::<_, std::convert::Infallible>(written_tokens(child))
        })
        .unwrap_or_else(|never| match never {}),
    }
}

/// `rule` with `subject` as KRS emits it: in its place for the first alternative, and beside it,
/// under the rule's name with the alternative's number and fresh source-map keys, for each other
/// one. Its binders are those the new clause holds.
fn restate(
    rule: &SemanticRule,
    index: usize,
    subject: &SemanticTerm,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let body = rule.body().expect("a static clause has a term rewrite");
    let mut used = BTreeSet::new();
    binders(subject, &mut used);
    binders(body.to(), &mut used);
    let variables = rule
        .variables()
        .iter()
        .filter(|variable| used.contains(variable.id()))
        .cloned()
        .collect::<Vec<SemanticVariable>>();
    let restated = if index == 0 {
        rule.restated(
            rule.id().clone(),
            subject.clone(),
            variables,
            &mut |origin| origin.clone(),
        )
    } else {
        let id = rule.id();
        let suffix = format!("~alternative-{index}");
        let disambiguator = if id.disambiguator().is_empty() {
            format!("alternative-{index}")
        } else {
            format!("{}:alternative-{index}", id.disambiguator())
        };
        let sibling = StableItemId::new(
            id.package().clone(),
            id.module_path().iter().cloned(),
            id.item_name(),
            id.item_kind(),
            disambiguator,
        )
        .map_err(|error| {
            DescriptorLoweringError::unsupported_shape(
                "static clause alternative",
                error.to_string(),
            )
        })?;
        rule.restated(
            sibling,
            subject.map_origins(&mut |origin| suffixed(origin, &suffix)),
            variables,
            &mut |origin| suffixed(origin, &suffix),
        )
    };
    restated.ok_or_else(|| {
        DescriptorLoweringError::unsupported_shape(
            "static clause",
            format!("{} has a part no static clause has", rule.id()),
        )
    })
}

/// Every binder `term` names: its variables, aliases and local binders.
fn binders<'t>(term: &'t SemanticTerm, output: &mut BTreeSet<&'t SemanticId>) {
    match term.kind() {
        IrTermKind::Variable { variable } => {
            output.insert(variable);
        }
        IrTermKind::As { alias, .. } => {
            output.insert(alias);
        }
        IrTermKind::Matches { binds, .. } | IrTermKind::Let { binds, .. } => output.extend(binds),
        _ => {}
    }
    for child in term.children() {
        binders(child, output);
    }
}

/// What an alias clause's subject holds below its root must be built from what the clause's
/// result matched in a printed term (the module documentation), so it refuses, at the term, in
/// preorder, a set's concatenation `set::concat(a, b)` (K's `A B`), and a map's of more than one
/// entry: forward the clause matches only a term whose parts are disjoint, a test of the term;
/// the printed alias writes the parts the match bound, which may overlap, and a concatenation of
/// overlapping parts denotes no set or map. A list's concatenation is defined for any two lists,
/// and a single element or entry and the empty collection are no concatenation. Its static
/// applications are expanded first ([`Expansion`]).
fn reversible_subject(
    clause: &StableItemId,
    root: &SemanticTerm,
) -> Result<(), DescriptorLoweringError> {
    let name = clause.item_name();
    let mut pending = root.children();
    pending.reverse();
    while let Some(term) = pending.pop() {
        let refusal = match term.kind() {
            IrTermKind::Set(operands) if matches!(**operands, SetOperands::Concat { .. }) => {
                Some(format!(
                    "alias clause `{name}`: a set's concatenation matches only a set whose parts are disjoint, a test the backward reading cannot make: when a result is printed, each term the clause's result matches prints as its subject, built from what the match bound, and parts that overlap print as a concatenation that denotes no set (`SetItem ( 1 ) SetItem ( 1 )`); write `#[k::desugar]` for an expansion that runs one way"
                ))
            }
            IrTermKind::Map(operands) if matches!(&**operands, MapOperands::Items(entries) if entries.len() > 1) => {
                Some(format!(
                    "alias clause `{name}`: a map's concatenation of entries matches only a map whose keys are distinct, a test the backward reading cannot make: when a result is printed, each term the clause's result matches prints as its subject, built from what the match bound, and keys that coincide print as a concatenation that denotes no map; write `#[k::desugar]` for an expansion that runs one way"
                ))
            }
            _ => None,
        };
        if let Some(reason) = refusal {
            return Err(DescriptorLoweringError::IrreversibleAlias {
                reason,
                range: term.origin().origin().exact_authored_range().map(Box::new),
                item: Some(Box::new(clause.clone())),
            });
        }
        let mut children = term.children();
        children.reverse();
        pending.extend(children);
    }
    Ok(())
}

fn invalid(item: &StableItemId, reason: String, origin: &NodeOrigin) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidStaticClause {
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
        item: Some(Box::new(item.clone())),
    }
}
