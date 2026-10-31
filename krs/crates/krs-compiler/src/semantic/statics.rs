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
//!
//! A clause's result is the term a program's expansion writes in place of the production's
//! application, which then evaluates as the same term in a rule's result does; so it is a term of
//! the production's sort or of a sort below it ([`check_result_sort`]), since the production's
//! sort is what the application's place requires.
//!
//! An alias clause also runs backwards: when a result is printed, each term its result matches
//! prints as its subject, built from what the match bound. So below its root the subject holds
//! nothing printing cannot build (`reversible_subject`); the constructs the expander's walker
//! refuses by their spelling are refused there.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, GrammarProductionItemKind, NodeOrigin, ProductionAttribute, SemanticId,
    SemanticIdKind, SentenceKind, SourceMapKey, StableItemId,
};
use krs_ir_levels::{
    IrTermKind, ListOperands, MapOperands, SemanticModule, SemanticRule, SemanticSortRef,
    SemanticTerm, SemanticVariable, SetOperands,
};

use super::catalog::semantic_is_subsort;
use super::error::DescriptorLoweringError;
use super::overload::sort_name;
use crate::partition::production_display_name;

/// The most static applications KRS expands in one clause's subject, counting
/// each recursive step: a recursive production's ground expansion that has not
/// ended by then is refused.
const EXPANSION_STEPS: usize = 10_000;

/// The most rewrites KRS follows on one path of an expansion, one inside the result of
/// another: an expansion that grows without repeating an application, past this, is refused.
const EXPANSION_DEPTH: usize = 256;

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
        check_result_sort(rule, mode, body.from(), body.to(), &productions)?;
        let mut expansion = Expansion {
            productions: &productions,
            clause: rule,
            mode,
            steps: EXPANSION_STEPS,
            copies: &mut copies,
        };
        if let Some(collection) = first_collection_of_parts(body.from()) {
            return Err(collection_in_subject(rule, mode, collection));
        }
        let subject = expansion.subject(body.from())?;
        let subjects = if mode == Mode::Desugar {
            alternatives(&subject)
        } else {
            vec![subject]
        };
        let clauses = subjects
            .into_iter()
            .enumerate()
            .map(|(index, subject)| restate(rule, index, &subject))
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

/// Checks that the result of an alias or desugar clause, of mode `clause`, is a term of the sort
/// of the production its subject's root applies, or of a sort below it.
///
/// The clause says that the production's application is its result: a program's application is
/// replaced by the result where it stands, before anything evaluates, and the expanded term
/// evaluates as the same term in a rule's result does. Where the application stands, the
/// production's sort is required (a program's root, a constructor's field of that sort), and a
/// term of a sort not below it is no term there: `#[k::desugar] Cp() => "s"` makes a program's
/// `cp` the projection of `"s"` to `Stmt`, which has no value. The sort judges the result, not
/// the value one binding gives it: a `KItem` result is no `Stmt` for the bindings that are none.
fn check_result_sort(
    rule: &SemanticRule,
    clause: Mode,
    subject: &SemanticTerm,
    result: &SemanticTerm,
    productions: &Productions<'_>,
) -> Result<(), DescriptorLoweringError> {
    let (sort, result_sort) = (subject.sort(), result.sort());
    if productions.is_subsort(result_sort, sort) {
        return Ok(());
    }
    let production = clause_head(rule).map_or_else(String::new, |head| {
        format!(" `{}`", production_display_name(head))
    });
    let (sort, result_sort) = (sort_name(sort), sort_name(result_sort));
    Err(DescriptorLoweringError::InvalidTerm {
        id: Box::new(rule.id().clone()),
        detail: format!(
            "the result of {} clause `{}` has sort `{result_sort}`, which is not below `{sort}`, the sort of the production{production} it expands: a program's application of the production is replaced by the result where a `{sort}` stands, and a term of sort `{result_sort}` is none there; write a result of sort `{sort}`, or of a sort below it",
            clause.clause(),
            rule.id().item_name(),
        ),
        range: result
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
    })
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

/// What a program's expansion has done on the way to one of its terms: the clauses that
/// rewrote an enclosing application, each of which, unless its production is recursive,
/// applies no more on this path; the applications they rewrote; and how many there are.
#[derive(Clone, Default)]
struct Path<'m> {
    applied: BTreeSet<&'m StableItemId>,
    rewritten: Vec<SemanticTerm>,
}

/// Whether a clause's subject matches a ground term.
enum Match {
    Yes,
    No,
    /// Telling takes more than comparing constructors, names and tokens.
    Unknown,
}

/// Why KRS cannot write an application expanded, and what to write instead.
struct Refused {
    reason: String,
    instead: Instead,
}

/// What a refusal advises writing instead of the application.
enum Instead {
    /// The term it expands to, which the clauses determine.
    Expansion,
    /// One clause per clause of the inner production, each with its expansion written out: the
    /// expansion depends on what a program writes.
    Cases,
    /// Arguments a clause of the production matches.
    Arguments,
}

impl Refused {
    fn new(reason: String, instead: Instead) -> Self {
        Self { reason, instead }
    }
}

impl<'m> Expansion<'_, 'm, '_> {
    /// The clause's subject with every static application below its root, the production the
    /// clause expands, expanded. A program writes the subject's applications itself, so each is
    /// expanded from an empty path.
    fn subject(&mut self, root: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        map_children(root, &mut |argument| {
            self.term(argument, None, &Path::default())
        })
    }

    /// `term`, on the expansion path `path`, with its static applications expanded, innermost
    /// first, as a program's are; a refusal is told at `site`, the outermost static application
    /// the clause's subject writes, which is `term`'s own when `site` is `None`. Alternatives in
    /// a desugar's application's arguments are distributed first, since the application of each
    /// alternative is one term a program writes.
    fn term(
        &mut self,
        term: &SemanticTerm,
        site: Option<&NodeOrigin>,
        path: &Path<'m>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let is_static = matches!(
            term.kind(),
            IrTermKind::Application {
                application: ApplicationRef::Declared(production),
                ..
            } if self.productions.is_static(production)
        );
        let site = match site {
            None if is_static => Some(term.origin()),
            site => site,
        };
        if is_static && self.mode == Mode::Desugar {
            let mut branches = alternatives(term).into_iter();
            if let (Some(first), Some(second)) = (branches.next(), branches.next()) {
                let expand = |expansion: &mut Self, branch: SemanticTerm| {
                    expansion.term(&branch, site, path)
                };
                let first = expand(self, first)?;
                let second = expand(self, second)?;
                let rest = branches
                    .map(|branch| expand(self, branch))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(term.with_kind(IrTermKind::Or {
                    alternatives: krs_ir::AtLeastTwo::new(first, second, rest),
                }));
            }
        }
        let term = map_children(term, &mut |child| self.term(child, site, path))?;
        self.rewrite(term, site, path)
    }

    /// `term`, whose arguments are expanded, rewritten at its root as long as it is a static
    /// application: each rewrite's result is expanded below its root on the path the rewrite
    /// extends, and rewritten at its root again in this loop, so a chain of root rewrites takes
    /// no native stack. An application that repeats on its path, or a path past
    /// [`EXPANSION_DEPTH`] rewrites, would never end, and is refused.
    fn rewrite(
        &mut self,
        term: SemanticTerm,
        site: Option<&NodeOrigin>,
        path: &Path<'m>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let mut current = term;
        let mut path = path.clone();
        loop {
            let IrTermKind::Application {
                application: ApplicationRef::Declared(production),
                arguments,
                ..
            } = current.kind()
            else {
                return Ok(current);
            };
            if !self.productions.is_static(production) {
                return Ok(current);
            }
            let production = production.clone();
            let site = site.expect("a static application is a site, or below one");
            let refused =
                |expansion: &Self, refused: Refused| expansion.refusal(&production, site, &refused);
            if path.rewritten.iter().any(|earlier| same(earlier, &current)) {
                return Err(refused(
                    self,
                    Refused::new(
                        "its expansion writes this very application again on its own path, so it never ends"
                            .to_owned(),
                        Instead::Expansion,
                    ),
                ));
            }
            if path.rewritten.len() >= EXPANSION_DEPTH || self.steps == 0 {
                return Err(refused(
                    self,
                    Refused::new(
                        format!(
                            "expanding it takes more than {EXPANSION_DEPTH} nested or {EXPANSION_STEPS} rewrites, so it may not end"
                        ),
                        Instead::Expansion,
                    ),
                ));
            }
            self.steps -= 1;
            let (clause, bindings) = self
                .clause_for(&production, arguments, &path.applied)
                .map_err(|refusal| refused(self, refusal))?;
            let result = clause
                .body()
                .expect("a static clause has a term rewrite")
                .to();
            let expanded = self
                .instantiate(result, &bindings)
                .map_err(|reason| refused(self, Refused::new(reason, Instead::Expansion)))?;
            path.applied.insert(clause.id());
            path.rewritten.push(current.clone());
            current = map_children(&expanded, &mut |child| self.term(child, Some(site), &path))?;
        }
    }

    /// The clause that expands `production` applied to `arguments`, with what its parameters
    /// bind, or why the expansion needs a value; a clause in `applied`, which rewrote an
    /// application this one stands in, applies no more unless its production is recursive.
    fn clause_for(
        &self,
        production: &StableItemId,
        arguments: &[SemanticTerm],
        applied: &BTreeSet<&'m StableItemId>,
    ) -> Result<(&'m SemanticRule, BTreeMap<SemanticId, SemanticTerm>), Refused> {
        let clauses = self
            .productions
            .clauses
            .get(production)
            .map_or(&[][..], Vec::as_slice);
        let recursive = self.productions.statics[production].recursive;
        let blocked = |clause: &SemanticRule| !recursive && applied.contains(clause.id());
        if arguments.iter().all(|argument| self.ground(argument)) {
            self.matching_clause(production, clauses, arguments, &blocked)
        } else {
            self.only_clause(production, clauses, arguments, &blocked)
        }
    }

    /// The one clause of `clauses`, not `blocked`, whose subject matches the ground
    /// `arguments`, with what its names bind.
    fn matching_clause(
        &self,
        production: &StableItemId,
        clauses: &[&'m SemanticRule],
        arguments: &[SemanticTerm],
        blocked: &dyn Fn(&SemanticRule) -> bool,
    ) -> Result<(&'m SemanticRule, BTreeMap<SemanticId, SemanticTerm>), Refused> {
        let name = production_display_name(production);
        let mut found = None;
        let mut spent = None;
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
                    return Err(Refused::new(
                        format!(
                            "telling which clause of `{name}` matches these arguments takes more than comparing constructors, names and tokens"
                        ),
                        Instead::Expansion,
                    ));
                }
                Match::Yes if blocked(clause) => spent = Some(clause.id().item_name()),
                Match::Yes if found.is_some() => {
                    return Err(Refused::new(
                        format!("more than one clause of `{name}` matches these arguments"),
                        Instead::Expansion,
                    ));
                }
                Match::Yes => found = Some((*clause, bindings)),
            }
        }
        found.ok_or_else(|| match spent {
            Some(clause) => Refused::new(
                format!(
                    "the clause of `{name}` that matches it, `{clause}`, already rewrote an application this one stands in, and `{name}` is not recursive, so a program's expansion leaves this application unexpanded and this clause never applies"
                ),
                Instead::Expansion,
            ),
            None => Refused::new(
                format!(
                    "no clause of `{name}` matches these arguments, so a program's application stays unexpanded and this clause never applies"
                ),
                Instead::Arguments,
            ),
        })
    }

    /// The only clause of the production, not recursive, whose parameters are plain names, each
    /// bound to its argument, which may not be ground.
    fn only_clause(
        &self,
        production: &StableItemId,
        clauses: &[&'m SemanticRule],
        arguments: &[SemanticTerm],
        blocked: &dyn Fn(&SemanticRule) -> bool,
    ) -> Result<(&'m SemanticRule, BTreeMap<SemanticId, SemanticTerm>), Refused> {
        let name = production_display_name(production);
        if self.productions.statics[production].recursive {
            return Err(Refused::new(
                format!(
                    "these arguments are not ground, and `{name}` is recursive, so its expansion depends on the values a program gives them"
                ),
                Instead::Cases,
            ));
        }
        let [clause] = clauses else {
            return Err(Refused::new(
                format!(
                    "these arguments are not ground, and `{name}` has {} clauses, so which one expands it depends on the values a program gives them",
                    clauses.len()
                ),
                Instead::Cases,
            ));
        };
        if blocked(clause) {
            return Err(Refused::new(
                format!(
                    "its clause, `{}`, already rewrote an application this one stands in, and `{name}` is not recursive, so a program's expansion leaves this application unexpanded and this clause never applies",
                    clause.id().item_name()
                ),
                Instead::Expansion,
            ));
        }
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
            return Err(Refused::new(
                format!(
                    "these arguments are not ground, and the parameters of `{name}`'s clause are not distinct plain names of its argument sorts, so whether the clause applies depends on the values a program gives them"
                ),
                Instead::Cases,
            ));
        };
        let result = clause
            .body()
            .expect("a static clause has a term rewrite")
            .to();
        for (index, (parameter, argument)) in parameters.iter().zip(arguments).enumerate() {
            let uses = occurrences(result, parameter);
            if uses == 0
                && let Some(bound) = self.used_elsewhere(argument)
            {
                return Err(Refused::new(
                    format!(
                        "its clause drops argument {}, which binds `{}` here, a name this clause uses elsewhere, which would have no value",
                        index + 1,
                        bound.as_str(),
                    ),
                    Instead::Expansion,
                ));
            }
            if uses > 1 && !self.determined(argument) {
                return Err(Refused::new(
                    format!(
                        "its clause copies argument {}, which here holds a pattern that matches more than one term apart from its names (`_`, `A | B`), so each copy would match a term of its own",
                        index + 1
                    ),
                    Instead::Expansion,
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

    /// A name `argument` binds that this clause names outside it, in its result or elsewhere in
    /// its subject: dropped with the argument, it would have no value.
    fn used_elsewhere<'t>(&self, argument: &'t SemanticTerm) -> Option<&'t SemanticId> {
        let body = self
            .clause
            .body()
            .expect("a static clause has a term rewrite");
        let mut bound = BTreeSet::new();
        binders(argument, &mut bound);
        bound.into_iter().find(|name| {
            !matches!(name.kind(), SemanticIdKind::Wildcard)
                && occurrences(body.from(), name) + occurrences(body.to(), name)
                    > occurrences(argument, name)
        })
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
            IrTermKind::List(_) | IrTermKind::Set(_) | IrTermKind::Map(_) => {
                one_spelling(term) && below()
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

    /// Whether `term` is one term once its names are: constructors, tokens, the collections of
    /// one spelling they build, names, and a name's alias of such a term, so that two copies of
    /// it, matching their names alike, match one term.
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
            IrTermKind::KSequence { .. } | IrTermKind::As { .. } => below(),
            IrTermKind::List(_) | IrTermKind::Set(_) | IrTermKind::Map(_) => {
                one_spelling(term) && below()
            }
            IrTermKind::Cell { .. }
            | IrTermKind::Rewrite { .. }
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
            IrTermKind::List(_) | IrTermKind::Set(_) | IrTermKind::Map(_)
                if one_spelling(result) =>
            {
                self.instantiate_children(result, bindings)
            }
            IrTermKind::List(_) | IrTermKind::Set(_) | IrTermKind::Map(_)
                if collection_of_parts(result) =>
            {
                Err(format!(
                    "its clause expands it to {}, which matches only one way of writing it",
                    collection_noun(result)
                ))
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

    /// The refusal of the static application of `production` at `site`.
    fn refusal(
        &self,
        production: &StableItemId,
        site: &NodeOrigin,
        refused: &Refused,
    ) -> DescriptorLoweringError {
        let name = production_display_name(production);
        let instead = match refused.instead {
            Instead::Expansion => "write the term it expands to instead".to_owned(),
            Instead::Cases => format!(
                "write one clause for each clause of `{name}` instead, each with that clause's arguments and its expansion written out"
            ),
            Instead::Arguments => format!("write arguments a clause of `{name}` matches"),
        };
        DescriptorLoweringError::InvalidStaticClause {
            reason: format!(
                "{} clause `{}`: `{name}` is marked `{}`, so a program's `{name}` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but {}: {instead}",
                self.mode.clause(),
                self.clause.id().item_name(),
                self.productions.statics[production].mode.attribute(),
                refused.reason,
            ),
            range: site.origin().exact_authored_range().map(Box::new),
            item: Some(Box::new(self.clause.id().clone())),
        }
    }
}

/// Whether `term`, a collection, has one spelling: the empty collection, one element or one
/// entry. Static expansion compares a collection's parts as they are written, without reordering
/// a set's elements or a map's entries or regrouping a list's (`[1, 2, 3]` meets `list::concat([1],
/// [2, 3])` and misses `list::concat([1, 2], [3])`), so a collection of two or more parts matches
/// only one of its spellings.
fn one_spelling(term: &SemanticTerm) -> bool {
    match term.kind() {
        IrTermKind::List(operands) => {
            matches!(**operands, ListOperands::Empty | ListOperands::Item { .. })
        }
        IrTermKind::Set(operands) => {
            matches!(**operands, SetOperands::Empty | SetOperands::Item { .. })
        }
        IrTermKind::Map(operands) => match &**operands {
            MapOperands::Empty => true,
            MapOperands::Items(entries) => entries.len() == 1,
            _ => false,
        },
        _ => false,
    }
}

/// Whether `term` is a collection of two or more parts: a concatenation of lists or of sets, or
/// a map of several entries.
fn collection_of_parts(term: &SemanticTerm) -> bool {
    match term.kind() {
        IrTermKind::List(operands) => matches!(**operands, ListOperands::Concat { .. }),
        IrTermKind::Set(operands) => matches!(**operands, SetOperands::Concat { .. }),
        IrTermKind::Map(operands) => {
            matches!(&**operands, MapOperands::Items(entries) if entries.len() > 1)
        }
        _ => false,
    }
}

/// What a collection of parts is, for a diagnostic.
fn collection_noun(term: &SemanticTerm) -> &'static str {
    match term.kind() {
        IrTermKind::List(_) => "a list of two or more parts",
        IrTermKind::Set(_) => "a set of two or more parts",
        _ => "a map of two or more entries",
    }
}

/// The first collection of two or more parts below the subject's root, in preorder.
fn first_collection_of_parts(subject: &SemanticTerm) -> Option<&SemanticTerm> {
    subject.children().into_iter().find_map(|child| {
        if collection_of_parts(child) {
            Some(child)
        } else {
            first_collection_of_parts(child)
        }
    })
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

/// The refusal of `collection`, a collection of two or more parts below the subject's root of
/// `rule`, a clause of `mode`.
fn collection_in_subject(
    rule: &SemanticRule,
    mode: Mode,
    collection: &SemanticTerm,
) -> DescriptorLoweringError {
    DescriptorLoweringError::CollectionInStaticSubject {
        reason: format!(
            "{} clause `{}`: {} matches only one way of writing it: static expansion matches a program's terms as they are written, before anything evaluates, and does not reorder a set's elements or a map's entries or regroup a list's parts, so the clause would rewrite one spelling of the collection and not the others (`[1, 2, 3]` but not `list::concat([1, 2], [3])`); the empty collection and one element or entry have one spelling: write the parts as a constructor's arguments, or rewrite the collection with a rule",
            mode.clause(),
            rule.id().item_name(),
            collection_noun(collection),
        ),
        range: collection
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
        item: Some(Box::new(rule.id().clone())),
    }
}

fn invalid(item: &StableItemId, reason: String, origin: &NodeOrigin) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidStaticClause {
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
        item: Some(Box::new(item.clone())),
    }
}
