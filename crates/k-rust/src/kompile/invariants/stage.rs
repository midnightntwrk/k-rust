//! The stage checker.
//!
//! A rewrite relates instances of its left-hand side to instances of its right-hand side, so a
//! right-hand-side variable that no binding position binds and no exemption quantifies has no
//! value when the rule applies. The user-facing definition check rejects such a variable in the
//! input; every stage of the pipeline must then keep every right-hand-side variable bound, or the
//! stage has built a rule that denotes nothing.
//!
//! [`StageChecks`] decides the obligation on the pipeline input and checks rule R3 at every stage
//! boundary while the obligation is [`Obligation::Preserved`]:
//!
//! - R3: no rule, claim, context or context alias of any module has a right-hand-side variable
//!   outside the exemptions of [`right_hand_side_binding`] (`?X`, `!X`, `THIS_CONFIGURATION`,
//!   `HOLE` of a context alias, and the names a rule or claim lists in `unboundVariables`),
//!   refined by two pipeline protocols:
//!   the entry `_` of `unboundVariables` names the anonymous variables of the rule, which
//!   `resolve anonymous variables` renames to `_Gen` followed by digits, so it covers exactly
//!   those names;
//!   `#Configuration` names the whole configuration and is bound by the left-hand side only once
//!   a stage providing [`Artifacts::CONFIGURATION_VARIABLES_BOUND`] has run, and never in a
//!   macro-like rule, whose expansion substitutes it into a use site that binds it.
//!
//! The unbound names come from the computation the user-facing check reports from, so the two
//! cannot disagree on what binds a variable.
//!
//! A condition is matched against nothing, so a variable that only a condition holds names no
//! matched term: a stage that introduces one into a `requires` (where it is a variable no match
//! binds) or an `ensures` (where it is universal over the rule) changes what the sentence states.
//! R3 checks right-hand sides and, for a backend that reads a `requires` as part of the left-hand
//! side, treats the `requires` as binding, so it cannot see such a variable there. [`StageChecks`]
//! therefore also checks rule C1 at every stage boundary:
//!
//! - C1: every variable free in the `requires` or `ensures` of a rule, claim, context or context
//!   alias after a stage occurs in the sentence's body, or occurred free in a condition of the
//!   same sentence before the stage, or is `HOLE` of a context alias. A variable a `#Exists` or
//!   `#Forall` of the condition binds is not free.
//!   The same sentence before the stage is every rule-like sentence before it that shares one of
//!   its input addresses ([`Attributes::input_addresses`], which provenance carries through every
//!   stage), so a stage that copies an authored condition into a sentence it derives from it
//!   (contexts into heating and cooling rules, a strict alias into its contexts) keeps C1, and one
//!   that invents a name does not, whatever other sentences of the module hold. Only a sentence
//!   without an input address is compared with every condition of its module before the stage.
//!   Two stages generate a name into conditions by protocol, and each is exempt at that stage
//!   only:
//!   `resolve anonymous variables` renames each anonymous variable `_`, `?_`, `!_` or `@_` to its
//!   prefix followed by `_Gen` and digits, so at that stage such a name is exempt in a sentence
//!   whose conditions held the anonymous variable of that prefix before it (the stage renames an
//!   authored variable, it adds none);
//!   `resolve function configuration` passes `#Configuration` to the configuration-reading
//!   functions a condition calls, so at that stage `#Configuration` is exempt. After it,
//!   `#Configuration` is checked like any other condition variable, until a stage providing
//!   [`Artifacts::CONFIGURATION_VARIABLES_BOUND`] has run; from then on it must occur in the body
//!   of a sentence that is not macro-like, whatever the conditions held before (that stage binds
//!   it in the body of every rule whose conditions hold it).
//!
//! C1 holds on the pipeline input by definition, so it needs no obligation decided there.
//!
//! [`Attributes::input_addresses`]: crate::definition::Attributes::input_addresses

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::definition::checks::{CheckedRoot, right_hand_side_binding};
use crate::definition::{AttributeKey, Definition, Sentence, StructuralCheckOptions};
use crate::kast::{InternalLabel, Term};
use crate::kompile::CompileOptions;
use crate::kompile::pipeline::{Artifacts, Stage};
use crate::provenance::InputAddress;

use super::emitted::emitted_from;

/// The variable that names the whole configuration in a rule of a function that reads it.
const CONFIGURATION_VARIABLE: &str = "#Configuration";

/// The stage that renames anonymous variables (C1's first exemption).
const ANONYMOUS_RENAMING_STAGE: &str = "resolve anonymous variables";

/// The stage that passes `#Configuration` to the configuration-reading functions a condition
/// calls (C1's second exemption).
const CONFIGURATION_PASSING_STAGE: &str = "resolve function configuration";

/// Whether `name` is an anonymous variable as written: `_`, `?_`, `!_` or `@_`.
fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

/// Checks every stage boundary of the table-driven pipeline against R3 and C1 and names the first
/// stage that breaks one.
#[derive(Debug)]
pub(crate) struct StageChecks {
    binding: Obligation,
    /// The union of the `provides` of every stage run so far.
    available: Artifacts,
    /// The condition variables at the last boundary checked (C1); `None` before the first.
    conditions: Option<ConditionVariables>,
}

/// The variables free in the conditions of the rule-like sentences of a definition (C1).
#[derive(Debug, Default)]
struct ConditionVariables {
    /// Per input address, those of the sentences that carry it.
    by_input: BTreeMap<InputAddress, BTreeSet<String>>,
    /// Per module, those of all its sentences.
    by_module: BTreeMap<String, BTreeSet<String>>,
}

impl ConditionVariables {
    fn of(definition: &Definition) -> Self {
        let mut variables = Self::default();
        for module in &definition.modules {
            let in_module = variables.by_module.entry(module.name.clone()).or_default();
            for sentence in &module.local_sentences {
                let Some((_, conditions, _)) = rule_like_parts(sentence) else {
                    continue;
                };
                let mut names = BTreeSet::new();
                for (_, condition) in conditions {
                    names.extend(free_variables(condition));
                }
                for address in sentence.attributes().input_addresses() {
                    variables
                        .by_input
                        .entry(address.clone())
                        .or_default()
                        .extend(names.iter().cloned());
                }
                in_module.extend(names);
            }
        }
        variables
    }

    /// The condition variables of `sentence` of module `module` before the stage: those of the
    /// sentences before it that share one of its input addresses, or, for a sentence without an
    /// address, those of the whole module.
    fn before(&self, module: &str, sentence: &Sentence) -> BTreeSet<String> {
        let addresses = sentence.attributes().input_addresses();
        if addresses.is_empty() {
            return self.by_module.get(module).cloned().unwrap_or_default();
        }
        addresses
            .iter()
            .filter_map(|address| self.by_input.get(address))
            .flatten()
            .cloned()
            .collect()
    }
}

/// How C1 treats `#Configuration` in a condition at a boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConfigurationRule {
    /// At the stage that passes it to configuration-reading functions: exempt.
    Introduced,
    /// Like any other condition variable.
    Ordinary,
    /// Once a stage has bound it, in a sentence that is not macro-like: it must occur in the body.
    Bound,
}

impl Default for StageChecks {
    fn default() -> Self {
        Self {
            binding: Obligation::Pending,
            available: Artifacts::NONE,
            conditions: None,
        }
    }
}

/// Whether a stage can be blamed for breaking an invariant.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Obligation {
    /// The boundary that decides it has not been reached.
    #[default]
    Pending,
    /// The invariant held when decided, so every later boundary must keep it.
    Preserved,
    /// The invariant was broken when decided, by a diagnostic the caller's policy demoted, so no
    /// stage is to blame.
    Waived,
}

impl StageChecks {
    /// Decide the binding obligation on the pipeline input; does nothing once it is decided, so
    /// the emission run keeps the decision of the transform run.
    pub(crate) fn start(&mut self, input: &Definition, options: &CompileOptions) {
        if self.conditions.is_none() {
            self.conditions = Some(ConditionVariables::of(input));
        }
        if self.binding != Obligation::Pending {
            return;
        }
        let structural = structural_options(options);
        let holds = input.modules.iter().all(|module| {
            module
                .local_sentences
                .iter()
                .all(|sentence| self.unbound(sentence, &structural).is_empty())
        });
        self.binding = if holds {
            Obligation::Preserved
        } else {
            Obligation::Waived
        };
    }

    /// Check the output of `stage`; panics with the invariant, the stage name and call, the
    /// module, the sentence index, the origin record's pass, and the rendered sentence.
    pub(crate) fn after(&mut self, stage: &Stage, output: &Definition, options: &CompileOptions) {
        self.available = self.available.union(stage.provides);
        self.check_conditions(stage, output);
        if self.binding != Obligation::Preserved {
            return;
        }
        let structural = structural_options(options);
        for module in &output.modules {
            // Invariant: every sentence of `module` before `index` satisfies R3.
            for (index, sentence) in module.local_sentences.iter().enumerate() {
                let unbound = self.unbound(sentence, &structural);
                if !unbound.is_empty() {
                    panic!(
                        "kompile invariant R3 (right-hand-side binding) broken by stage {:?} ({}): \
                         {} bound by no left-hand side and covered by no exemption\n  in {}\n  sentence: {}",
                        stage.name,
                        stage.call,
                        describe_unbound(&unbound),
                        emitted_from(
                            &format!("sentence {index} of module {}", module.name),
                            sentence.attributes().origin_record(),
                        ),
                        render_sentence(sentence),
                    );
                }
            }
        }
    }

    /// Check C1 on the output of `stage` against the conditions before it, then record the
    /// output's conditions for the next boundary; panics like R3 when it is broken.
    fn check_conditions(&mut self, stage: &Stage, output: &Definition) {
        if let Some(earlier) = &self.conditions {
            let renames_anonymous = stage.name == ANONYMOUS_RENAMING_STAGE;
            for module in &output.modules {
                // Invariant: every sentence of `module` before `index` satisfies C1.
                for (index, sentence) in module.local_sentences.iter().enumerate() {
                    let configuration = if stage.name == CONFIGURATION_PASSING_STAGE {
                        ConfigurationRule::Introduced
                    } else if self
                        .available
                        .contains(Artifacts::CONFIGURATION_VARIABLES_BOUND)
                        && !sentence.attributes().has_any(&AttributeKey::MACRO_LIKE)
                    {
                        ConfigurationRule::Bound
                    } else {
                        ConfigurationRule::Ordinary
                    };
                    let introduced = introduced_condition_variables(
                        sentence,
                        &earlier.before(&module.name, sentence),
                        renames_anonymous,
                        configuration,
                    );
                    if !introduced.is_empty() {
                        panic!(
                            "kompile invariant C1 (condition binding) broken by stage {:?} ({}): \
                             {} occur in no body and in no condition of the sentence before the stage\n  in {}\n  sentence: {}",
                            stage.name,
                            stage.call,
                            describe_condition_variables(&introduced),
                            emitted_from(
                                &format!("sentence {index} of module {}", module.name),
                                sentence.attributes().origin_record(),
                            ),
                            render_sentence(sentence),
                        );
                    }
                }
            }
        }
        self.conditions = Some(ConditionVariables::of(output));
    }

    /// The right-hand-side variables of `sentence`, per checked root, outside the exemptions of
    /// R3 at the current boundary; empty for a sentence that is not rule-like.
    fn unbound(
        &self,
        sentence: &Sentence,
        options: &StructuralCheckOptions,
    ) -> Vec<(CheckedRoot, BTreeSet<String>)> {
        let Some(binding) = right_hand_side_binding(sentence, options) else {
            return Vec::new();
        };
        let anonymous_listed = binding.listed.contains("_");
        let configuration_exempt = !self
            .available
            .contains(Artifacts::CONFIGURATION_VARIABLES_BOUND)
            || sentence.attributes().has_any(&AttributeKey::MACRO_LIKE);
        binding
            .unbound
            .into_iter()
            .filter_map(|(root, mut names)| {
                names.retain(|name| {
                    !(anonymous_listed && is_renamed_anonymous(name)
                        || configuration_exempt && name == CONFIGURATION_VARIABLE)
                });
                (!names.is_empty()).then_some((root, names))
            })
            .collect()
    }
}

/// The body of a rule-like sentence, its conditions, and whether it is a context alias.
type RuleLikeParts<'a> = (&'a Term, Vec<(CheckedRoot, &'a Term)>, bool);

/// The body and the conditions of a rule-like sentence (C1), and whether it is a context alias.
fn rule_like_parts(sentence: &Sentence) -> Option<RuleLikeParts<'_>> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => Some((
            body,
            vec![
                (CheckedRoot::Requires, requires),
                (CheckedRoot::Ensures, ensures),
            ],
            false,
        )),
        Sentence::Context { body, requires, .. } => {
            Some((body, vec![(CheckedRoot::Requires, requires)], false))
        }
        Sentence::ContextAlias { body, requires, .. } => {
            Some((body, vec![(CheckedRoot::Requires, requires)], true))
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => None,
    }
}

/// The condition variables of `sentence` that break C1 against `before`, the condition variables
/// of the same sentence before the stage, per condition.
fn introduced_condition_variables(
    sentence: &Sentence,
    before: &BTreeSet<String>,
    renames_anonymous: bool,
    configuration: ConfigurationRule,
) -> Vec<(CheckedRoot, BTreeSet<String>)> {
    let Some((body, conditions, is_alias)) = rule_like_parts(sentence) else {
        return Vec::new();
    };
    let mut in_body = BTreeSet::new();
    body.visit_preorder(&mut |node| {
        if let Term::Variable { name, .. } = node.unannotated() {
            in_body.insert(name.clone());
        }
    });
    conditions
        .into_iter()
        .filter_map(|(root, condition)| {
            let mut names = free_variables(condition);
            names.retain(|name| {
                let allowed = if name == CONFIGURATION_VARIABLE {
                    match configuration {
                        ConfigurationRule::Introduced => true,
                        ConfigurationRule::Ordinary => {
                            in_body.contains(name) || before.contains(name)
                        }
                        ConfigurationRule::Bound => in_body.contains(name),
                    }
                } else {
                    in_body.contains(name)
                        || before.contains(name)
                        || is_alias && name == "HOLE"
                        || renames_anonymous
                            && renamed_anonymous_prefix(name)
                                .is_some_and(|prefix| before.contains(&format!("{prefix}_")))
                };
                !allowed
            });
            (!names.is_empty()).then_some((root, names))
        })
        .collect()
}

/// The variables free in `term`: every variable occurrence outside the scope of a `#Exists` or
/// `#Forall` that binds its name (the variables of a quantifier's first argument, in its second).
/// Each anonymous variable is a variable of its own, so a quantified `_` binds no other `_`.
fn free_variables(term: &Term) -> BTreeSet<String> {
    let mut free = BTreeSet::new();
    // Each item is a term and the number of entries of `bound` in its scope.
    let mut bound: Vec<String> = Vec::new();
    let mut pending: Vec<(&Term, usize)> = vec![(term, 0)];
    // Invariant: every term popped from `pending` is a subterm of `term`, visited once, so the
    // loop ends; `bound[..scope]` is the binders in scope of each pending term.
    while let Some((node, scope)) = pending.pop() {
        bound.truncate(scope);
        match node.unannotated() {
            Term::Variable { name, .. } => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }
            Term::Apply { label, arguments }
                if (label.is(InternalLabel::Exists) || label.is(InternalLabel::Forall))
                    && arguments.len() == 2 =>
            {
                arguments[0].visit_preorder(&mut |binder| {
                    if let Term::Variable { name, .. } = binder.unannotated()
                        && !is_anonymous(name)
                    {
                        bound.push(name.clone());
                    }
                });
                pending.push((&arguments[1], bound.len()));
            }
            other @ (Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Apply { .. }
            | Term::Token { .. }
            | Term::Annotated { .. }) => {
                for child in other.children() {
                    pending.push((child, scope));
                }
            }
        }
    }
    free
}

fn describe_condition_variables(introduced: &[(CheckedRoot, BTreeSet<String>)]) -> String {
    let mut text = String::from("condition variables");
    // Invariant: `text` lists the variables of every condition before `root`.
    for (position, (root, names)) in introduced.iter().enumerate() {
        let separator = if position == 0 { " " } else { "; " };
        let names = names.iter().map(String::as_str).collect::<Vec<_>>();
        let _ = write!(text, "{separator}{} in {}", names.join(", "), root.as_str());
    }
    text
}

/// The options the user-facing check applies to `options`' backend and check mode.
fn structural_options(options: &CompileOptions) -> StructuralCheckOptions {
    options
        .backend
        .structural_check_options(options.check_mode.clone(), Vec::new())
}

/// Whether `name` is a name `resolve anonymous variables` gives an anonymous `_`: `_Gen`
/// followed by one or more digits.
fn is_renamed_anonymous(name: &str) -> bool {
    renamed_anonymous_prefix(name) == Some("")
}

/// The prefix (`""`, `"?"`, `"!"` or `"@"`) of the anonymous variable that `resolve anonymous
/// variables` renames to `name`, when `name` is such a renaming: the prefix, `_Gen`, and one or
/// more digits.
fn renamed_anonymous_prefix(name: &str) -> Option<&'static str> {
    ["", "?", "!", "@"].into_iter().find(|prefix| {
        name.strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix("_Gen"))
            .is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
    })
}

fn describe_unbound(unbound: &[(CheckedRoot, BTreeSet<String>)]) -> String {
    let mut text = String::from("right-hand-side variables");
    // Invariant: `text` lists the variables of every root before `root`.
    for (position, (root, names)) in unbound.iter().enumerate() {
        let separator = if position == 0 { " " } else { "; " };
        let names = names.iter().map(String::as_str).collect::<Vec<_>>();
        let _ = write!(text, "{separator}{} in {}", names.join(", "), root.as_str());
    }
    text
}

fn render_sentence(sentence: &Sentence) -> String {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } => format!("rule {body} requires {requires} ensures {ensures}"),
        Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => format!("claim {body} requires {requires} ensures {ensures}"),
        Sentence::Context { body, requires, .. } => {
            format!("context {body} requires {requires}")
        }
        Sentence::ContextAlias { body, requires, .. } => {
            format!("context alias {body} requires {requires}")
        }
        other @ Sentence::SyntaxSort { .. }
        | other @ Sentence::SortSynonym { .. }
        | other @ Sentence::SyntaxLexical { .. }
        | other @ Sentence::Production { .. }
        | other @ Sentence::SyntaxAssociativity { .. }
        | other @ Sentence::SyntaxPriority { .. }
        | other @ Sentence::Configuration { .. }
        | other @ Sentence::Bubble { .. } => format!("{other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::definition::{AttributeKey, Attributes, Definition, FlatModule, Sentence};
    use crate::kast::Term;
    use crate::kompile::CompileOptions;
    use crate::kompile::pipeline::{
        Artifacts, PassError, PassFn, PassInput, PassOutcome, PipelineState, Provenance, Stage,
        run_stages,
    };
    use crate::provenance::{InputAddress, InputSpace};
    use crate::timings::PhaseTimings;

    fn rule(left: Term, right: Term, attributes: Attributes) -> Sentence {
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            },
            requires: Term::apply("true", Vec::new()),
            ensures: Term::apply("true", Vec::new()),
            attributes,
        }
    }

    fn definition(sentences: Vec<Sentence>) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: sentences.into_iter().map(Arc::new).collect(),
                attributes: Default::default(),
            }],
            attributes: Default::default(),
        }
    }

    fn stage(name: &'static str, run: PassFn, provides: Artifacts) -> Stage {
        Stage {
            name,
            call: "test_stage",
            run,
            provenance: Provenance::None,
            behavior: "generating",
            requires: Artifacts::NONE,
            provides,
        }
    }

    fn identity(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
        Ok(PassOutcome::Changed(input.definition.clone()))
    }

    fn appending(input: &PassInput<'_>, sentence: Sentence) -> Result<PassOutcome, PassError> {
        let mut output = input.definition.clone();
        output.modules[0].local_sentences.push(Arc::new(sentence));
        Ok(PassOutcome::Changed(output))
    }

    fn run(stages: &[Stage], input: Definition) -> Definition {
        run_stages(
            stages,
            input,
            &mut PipelineState::default(),
            &CompileOptions::default(),
            &mut PhaseTimings::default(),
        )
        .expect("the test stages succeed")
    }

    fn panic_message(run: impl FnOnce() + std::panic::UnwindSafe) -> String {
        let payload = std::panic::catch_unwind(run).expect_err("the stage checker panics");
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                payload
                    .downcast_ref::<&str>()
                    .map(|text| (*text).to_owned())
            })
            .expect("a formatted panic message")
    }

    fn foo_x_to_bar(name: &str, attributes: Attributes) -> Sentence {
        rule(
            Term::apply("foo", vec![Term::variable("X")]),
            Term::apply("bar", vec![Term::variable(name)]),
            attributes,
        )
    }

    fn anonymous_listed() -> Attributes {
        let mut attributes = Attributes::default();
        attributes.set(
            AttributeKey::UnboundVariables,
            serde_json::Value::String("_".into()),
        );
        attributes
    }

    #[test]
    fn a_stage_appending_an_unbound_right_hand_side_variable_panics_naming_it() {
        fn append(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            appending(input, foo_x_to_bar("Y", Attributes::default()))
        }
        let message = panic_message(|| {
            run(
                &[
                    stage("first stage", identity, Artifacts::NONE),
                    stage("appending stage", append, Artifacts::NONE),
                ],
                definition(Vec::new()),
            );
        });
        assert!(message.contains("R3"), "{message}");
        assert!(
            message.contains("\"appending stage\" (test_stage)"),
            "{message}"
        );
        assert!(message.contains("variables Y in body"), "{message}");
        assert!(message.contains("sentence 0 of module MAIN"), "{message}");
        assert!(message.contains("rule foo(X)=>bar(Y)"), "{message}");
    }

    #[test]
    fn unbound_variables_anonymous_entry_covers_exactly_the_renamed_anonymous_variables() {
        fn append_gen(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            appending(input, foo_x_to_bar("_Gen0", anonymous_listed()))
        }
        fn append_dot_var(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            appending(input, foo_x_to_bar("_DotVar0", anonymous_listed()))
        }
        let output = run(
            &[stage("appending stage", append_gen, Artifacts::NONE)],
            definition(Vec::new()),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 1);

        let message = panic_message(|| {
            run(
                &[stage("appending stage", append_dot_var, Artifacts::NONE)],
                definition(Vec::new()),
            );
        });
        assert!(message.contains("R3"), "{message}");
        assert!(message.contains("\"appending stage\""), "{message}");
        assert!(message.contains("variables _DotVar0 in body"), "{message}");
    }

    fn configuration_rule(attributes: Attributes) -> Sentence {
        rule(
            Term::apply("f", vec![Term::variable("X")]),
            Term::apply("g", vec![Term::variable("#Configuration")]),
            attributes,
        )
    }

    fn macro_attributes() -> Attributes {
        let mut attributes = Attributes::default();
        attributes.mark(AttributeKey::Macro);
        attributes
    }

    #[test]
    fn configuration_is_exempt_until_a_stage_binds_it_and_always_in_a_macro() {
        fn append_rule(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            appending(input, configuration_rule(Attributes::default()))
        }
        fn append_macro(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            appending(input, configuration_rule(macro_attributes()))
        }

        // Before the binding stage: the free `#Configuration` is allowed.
        let output = run(
            &[
                stage("appending stage", append_rule, Artifacts::NONE),
                stage("later stage", identity, Artifacts::NONE),
            ],
            definition(Vec::new()),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 1);

        // At the stage that provides the binding, the free `#Configuration` it leaves panics.
        let message = panic_message(|| {
            run(
                &[
                    stage("appending stage", append_rule, Artifacts::NONE),
                    stage(
                        "binding stage",
                        identity,
                        Artifacts::CONFIGURATION_VARIABLES_BOUND,
                    ),
                ],
                definition(Vec::new()),
            );
        });
        assert!(message.contains("R3"), "{message}");
        assert!(message.contains("\"binding stage\""), "{message}");
        assert!(
            message.contains("variables #Configuration in body"),
            "{message}"
        );

        // After it, a stage that introduces one panics too.
        let message = panic_message(|| {
            run(
                &[
                    stage(
                        "binding stage",
                        identity,
                        Artifacts::CONFIGURATION_VARIABLES_BOUND,
                    ),
                    stage("appending stage", append_rule, Artifacts::NONE),
                ],
                definition(Vec::new()),
            );
        });
        assert!(message.contains("\"appending stage\""), "{message}");

        // A macro-like rule keeps `#Configuration` free at every stage.
        let output = run(
            &[
                stage(
                    "binding stage",
                    identity,
                    Artifacts::CONFIGURATION_VARIABLES_BOUND,
                ),
                stage("appending stage", append_macro, Artifacts::NONE),
                stage("later stage", identity, Artifacts::NONE),
            ],
            definition(Vec::new()),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 1);
    }

    #[test]
    fn an_input_with_an_unbound_variable_waives_the_obligation() {
        fn append(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            appending(input, foo_x_to_bar("Z", Attributes::default()))
        }
        let output = run(
            &[
                stage("appending stage", append, Artifacts::NONE),
                stage(
                    "binding stage",
                    identity,
                    Artifacts::CONFIGURATION_VARIABLES_BOUND,
                ),
            ],
            definition(vec![foo_x_to_bar("Y", Attributes::default())]),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 2);
    }

    fn conditioned(requires: Term) -> Sentence {
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply("foo", vec![Term::variable("X")])),
                right: Box::new(Term::apply("bar", vec![Term::variable("X")])),
            },
            requires,
            ensures: Term::apply("true", Vec::new()),
            attributes: Attributes::default(),
        }
    }

    fn replace_requires(
        input: &PassInput<'_>,
        rewrite: impl Fn(Term) -> Term,
    ) -> Result<PassOutcome, PassError> {
        let mut output = input.definition.clone();
        for sentence in &mut output.modules[0].local_sentences {
            if let Sentence::Rule { requires, .. } = crate::definition::sentence_mut(sentence) {
                let taken = std::mem::replace(requires, Term::Sequence(Vec::new()));
                *requires = rewrite(taken);
            }
        }
        Ok(PassOutcome::Changed(output))
    }

    fn is_int_or_bool() -> Term {
        Term::apply(
            "#Or",
            vec![
                Term::apply("isInt", vec![Term::variable("X")]),
                Term::apply("isBool", vec![Term::variable("X")]),
            ],
        )
    }

    #[test]
    fn a_stage_adding_a_fresh_variable_to_a_requires_breaks_c1_naming_it() {
        fn add_fresh(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            replace_requires(input, |requires| {
                Term::apply("_andBool_", vec![requires, Term::variable("Fresh")])
            })
        }
        let message = panic_message(|| {
            run(
                &[
                    stage("first stage", identity, Artifacts::NONE),
                    stage("conditioning stage", add_fresh, Artifacts::NONE),
                ],
                definition(vec![conditioned(Term::apply("true", Vec::new()))]),
            );
        });
        assert!(message.contains("C1"), "{message}");
        assert!(
            message.contains("\"conditioning stage\" (test_stage)"),
            "{message}"
        );
        assert!(message.contains("Fresh in requires"), "{message}");
        assert!(message.contains("sentence 0 of module MAIN"), "{message}");
    }

    /// The guard alias `guard_or_patterns` gave a disjunction in a requires before MLP/1: a
    /// variable that no match binds, which C1 names.
    #[test]
    fn a_guard_alias_of_a_condition_disjunction_breaks_c1() {
        fn alias(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            replace_requires(input, |requires| Term::As {
                pattern: Box::new(requires),
                alias: Box::new(Term::variable("_Gen0")),
            })
        }
        let message = panic_message(|| {
            run(
                &[stage("guard or-patterns", alias, Artifacts::NONE)],
                definition(vec![conditioned(is_int_or_bool())]),
            );
        });
        assert!(message.contains("C1"), "{message}");
        assert!(message.contains("\"guard or-patterns\""), "{message}");
        assert!(message.contains("_Gen0 in requires"), "{message}");
    }

    /// A condition variable the body holds, one the conditions held before the stage, and a
    /// variable a quantifier binds are not new condition variables.
    #[test]
    fn bound_and_earlier_condition_variables_keep_c1() {
        fn conjoin(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            replace_requires(input, |requires| {
                Term::apply(
                    "#And",
                    vec![
                        requires,
                        Term::apply(
                            "#Exists",
                            vec![
                                Term::variable("Y"),
                                Term::apply("isInt", vec![Term::variable("Y")]),
                            ],
                        ),
                    ],
                )
            })
        }
        let earlier = Term::apply(
            "_andBool_",
            vec![is_int_or_bool(), Term::variable("Authored")],
        );
        let output = run(
            &[stage("conjoining stage", conjoin, Artifacts::NONE)],
            definition(vec![conditioned(earlier)]),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 1);
    }

    /// Renaming an authored anonymous condition variable is C1's anonymous exemption, at the
    /// renaming stage only.
    #[test]
    fn renaming_an_anonymous_condition_variable_keeps_c1_only_at_the_renaming_stage() {
        fn rename(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            replace_requires(input, |_| exists("_Gen0", "_Gen1"))
        }
        // `#Exists _ . isInt(_)`: two anonymous variables, the second free in the condition.
        fn exists(binder: &str, used: &str) -> Term {
            Term::apply(
                "#Exists",
                vec![
                    Term::variable(binder),
                    Term::apply("isInt", vec![Term::variable(used)]),
                ],
            )
        }
        let anonymous = || definition(vec![conditioned(exists("_", "_"))]);
        let output = run(
            &[stage(
                "resolve anonymous variables",
                rename,
                Artifacts::NONE,
            )],
            anonymous(),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 1);
        let message = panic_message(|| {
            run(
                &[stage("other stage", rename, Artifacts::NONE)],
                anonymous(),
            );
        });
        assert!(message.contains("C1"), "{message}");
        assert!(message.contains("_Gen1 in requires"), "{message}");
    }

    /// `#Configuration` in a condition is exempt until the binding stage; after it the body must
    /// hold it, whatever the conditions held before.
    #[test]
    fn a_condition_configuration_must_be_bound_once_the_binding_stage_has_run() {
        fn configure(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            replace_requires(input, |_| {
                Term::apply("isZero", vec![Term::variable("#Configuration")])
            })
        }
        let input = || definition(vec![conditioned(Term::apply("true", Vec::new()))]);
        let output = run(
            &[
                stage("resolve function configuration", configure, Artifacts::NONE),
                stage("later stage", identity, Artifacts::NONE),
            ],
            input(),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 1);
        let message = panic_message(|| {
            run(
                &[
                    stage("resolve function configuration", configure, Artifacts::NONE),
                    stage(
                        "binding stage",
                        identity,
                        Artifacts::CONFIGURATION_VARIABLES_BOUND,
                    ),
                ],
                input(),
            );
        });
        assert!(message.contains("C1"), "{message}");
        assert!(message.contains("\"binding stage\""), "{message}");
        assert!(message.contains("#Configuration in requires"), "{message}");
    }

    fn addressed(mut sentence: Sentence, index: u32) -> Sentence {
        sentence
            .attributes_mut()
            .set_input_addresses(vec![InputAddress::new(InputSpace::Compile, "MAIN", index)]);
        sentence
    }

    fn is_int(name: &str) -> Term {
        Term::apply("isInt", vec![Term::variable(name)])
    }

    /// The reviewer's escape: a rule of the module whose own condition holds the name the guard
    /// minted (`requires X ==Int _Gen0`, a user existential) does not hide the alias the stage adds
    /// to another rule's condition, because the earlier conditions are those of the sentence.
    #[test]
    fn another_sentences_condition_variable_does_not_hide_a_guard_alias() {
        fn alias_first(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            let mut output = input.definition.clone();
            if let Sentence::Rule { requires, .. } =
                crate::definition::sentence_mut(&mut output.modules[0].local_sentences[0])
            {
                let taken = std::mem::replace(requires, Term::Sequence(Vec::new()));
                *requires = Term::As {
                    pattern: Box::new(taken),
                    alias: Box::new(Term::variable("_Gen0")),
                };
            }
            Ok(PassOutcome::Changed(output))
        }
        let user = conditioned(Term::apply(
            "_==Int_",
            vec![Term::variable("X"), Term::variable("_Gen0")],
        ));
        let message = panic_message(|| {
            run(
                &[stage("guard or-patterns", alias_first, Artifacts::NONE)],
                definition(vec![
                    addressed(conditioned(is_int_or_bool()), 0),
                    addressed(user, 1),
                ]),
            );
        });
        assert!(message.contains("C1"), "{message}");
        assert!(message.contains("_Gen0 in requires"), "{message}");
        assert!(message.contains("sentence 0 of module MAIN"), "{message}");
    }

    /// `resolve anonymous variables` renames `_`, `?_`, `!_` and `@_` to the same prefix followed
    /// by `_Gen` and digits; each renamed name is the sentence's own authored variable.
    #[test]
    fn every_anonymous_prefix_is_covered_by_the_renaming_exemption() {
        /// `isInt(P_)` becomes `isInt(P_Gen0)`, as the renaming stage writes it.
        fn rename(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            replace_requires(input, |requires| {
                let mut anonymous = None;
                requires.visit_preorder(&mut |node| {
                    if let Term::Variable { name, .. } = node {
                        anonymous = Some(name.clone());
                    }
                });
                let name = anonymous.expect("the test condition is isInt of a variable");
                is_int(&format!("{name}Gen0"))
            })
        }
        fn rename_to_existential(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            replace_requires(input, |_| is_int("?_Gen0"))
        }
        for prefix in ["", "?", "!", "@"] {
            let output = run(
                &[stage(
                    "resolve anonymous variables",
                    rename,
                    Artifacts::NONE,
                )],
                definition(vec![addressed(
                    conditioned(is_int(&format!("{prefix}_"))),
                    0,
                )]),
            );
            assert_eq!(output.modules[0].local_sentences.len(), 1, "{prefix}");
        }
        // A name of another prefix than the anonymous variable the sentence held is not its
        // renaming.
        let message = panic_message(|| {
            run(
                &[stage(
                    "resolve anonymous variables",
                    rename_to_existential,
                    Artifacts::NONE,
                )],
                definition(vec![addressed(conditioned(is_int("_")), 0)]),
            );
        });
        assert!(message.contains("?_Gen0 in requires"), "{message}");
    }

    /// The anonymous exemption is per sentence: renaming one sentence's `_` does not license a
    /// `_Gen` name in another sentence whose conditions held no anonymous variable.
    #[test]
    fn the_anonymous_exemption_covers_only_the_sentence_that_held_the_anonymous_variable() {
        fn rename(input: &PassInput<'_>, _: &mut PipelineState) -> Result<PassOutcome, PassError> {
            let mut output = input.definition.clone();
            for (index, sentence) in output.modules[0].local_sentences.iter_mut().enumerate() {
                if let Sentence::Rule { requires, .. } = crate::definition::sentence_mut(sentence) {
                    *requires = is_int(if index == 0 { "_Gen0" } else { "_Gen1" });
                }
            }
            Ok(PassOutcome::Changed(output))
        }
        let message = panic_message(|| {
            run(
                &[stage(
                    "resolve anonymous variables",
                    rename,
                    Artifacts::NONE,
                )],
                definition(vec![
                    addressed(conditioned(is_int("_")), 0),
                    addressed(conditioned(Term::apply("true", Vec::new())), 1),
                ]),
            );
        });
        assert!(message.contains("_Gen1 in requires"), "{message}");
        assert!(message.contains("sentence 1 of module MAIN"), "{message}");
    }

    /// `#Configuration` is exempt only at the stage that passes it to configuration-reading
    /// functions; any other stage that introduces it into a condition breaks C1, and a stage that
    /// copies a condition holding it into a sentence of the same input keeps C1.
    #[test]
    fn only_the_function_configuration_stage_introduces_a_condition_configuration() {
        fn configure(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            replace_requires(input, |_| {
                Term::apply("isZero", vec![Term::variable("#Configuration")])
            })
        }
        fn copy_first(
            input: &PassInput<'_>,
            _: &mut PipelineState,
        ) -> Result<PassOutcome, PassError> {
            let mut output = input.definition.clone();
            let copy = output.modules[0].local_sentences[0].clone();
            output.modules[0].local_sentences.push(copy);
            Ok(PassOutcome::Changed(output))
        }
        let input = || {
            definition(vec![addressed(
                conditioned(Term::apply("true", Vec::new())),
                0,
            )])
        };
        let output = run(
            &[
                stage("resolve function configuration", configure, Artifacts::NONE),
                stage("copying stage", copy_first, Artifacts::NONE),
            ],
            input(),
        );
        assert_eq!(output.modules[0].local_sentences.len(), 2);
        let message = panic_message(|| {
            run(
                &[stage("another stage", configure, Artifacts::NONE)],
                input(),
            );
        });
        assert!(message.contains("C1"), "{message}");
        assert!(message.contains("\"another stage\""), "{message}");
        assert!(message.contains("#Configuration in requires"), "{message}");
    }
}
