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

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::definition::checks::{CheckedRoot, right_hand_side_binding};
use crate::definition::{AttributeKey, Definition, Sentence, StructuralCheckOptions};
use crate::kompile::CompileOptions;
use crate::kompile::pipeline::{Artifacts, Stage};

use super::emitted::emitted_from;

/// The variable that names the whole configuration in a rule of a function that reads it.
const CONFIGURATION_VARIABLE: &str = "#Configuration";

/// Checks every stage boundary of the table-driven pipeline against R3 and names the first stage
/// that breaks it.
#[derive(Debug)]
pub(crate) struct StageChecks {
    binding: Obligation,
    /// The union of the `provides` of every stage run so far.
    available: Artifacts,
}

impl Default for StageChecks {
    fn default() -> Self {
        Self {
            binding: Obligation::Pending,
            available: Artifacts::NONE,
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

/// The options the user-facing check applies to `options`' backend and check mode.
fn structural_options(options: &CompileOptions) -> StructuralCheckOptions {
    options
        .backend
        .structural_check_options(options.check_mode.clone(), Vec::new())
}

/// Whether `name` is a name `resolve anonymous variables` gives an anonymous `_`: `_Gen`
/// followed by one or more digits.
fn is_renamed_anonymous(name: &str) -> bool {
    name.strip_prefix("_Gen").is_some_and(|suffix| {
        !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
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
}
