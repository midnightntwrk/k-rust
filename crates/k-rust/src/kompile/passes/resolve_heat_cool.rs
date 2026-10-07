//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Lower `heat` and `cool` attributes into explicit side conditions.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{fmt, mem};

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{FrontendSort, Label, Sort, Term},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveHeatCoolError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveHeatCoolError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "heat/cool attribute resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveHeatCoolError {}

/// Lower `heat` and `cool` attributes into explicit side conditions.
pub fn resolve_heat_cool_attributes(
    definition: &Definition,
) -> Result<Definition, ResolveHeatCoolError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_heat_cool_attributes_pass,
        Some(GeneratingPass::ResolveHeatCool),
    )
}

pub(crate) fn resolve_heat_cool_attributes_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveHeatCoolError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveHeatCoolError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidHeatCool,
            message: error.to_string(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        }],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let sorts = views.sort_catalog(module_id);
        // The first heat or cool sentence of the module given a condition, which the module's
        // `BOOL` import is for; it locates the error when the definition has no `BOOL`.
        let mut first_lowered = None;
        // Invariant: every heat or cool rule or context of `module.local_sentences` before `sentence` has its `requires` conjoined with its result predicate on `HOLE` (negated for heat), `first_lowered` locates the first of them, and `diagnostics` holds one error for each such sentence whose predicate is missing; each iteration consumes one sentence.
        for sentence in &mut module.local_sentences {
            // Only heat and cool sentences change. Their attributes are checked before taking a
            // mutable sentence, which copies a shared one, so every other sentence stays shared;
            // the kind is decided below.
            if !sentence.attributes().has(AttributeKey::Heat)
                && !sentence.attributes().has(AttributeKey::Cool)
            {
                continue;
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let attributes = sentence.attributes();
            let heat = attributes.has(AttributeKey::Heat);
            let cool = attributes.has(AttributeKey::Cool);
            if !heat && !cool {
                continue;
            }
            // Heat/cool lowering is defined only for rules and contexts, the sentences that state
            // evaluation steps. Every other kind is left unchanged before the result predicate is
            // resolved, so an unrelated production or claim never fails for a missing predicate.
            match sentence {
                Sentence::Rule { .. } | Sentence::Context { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let result_sort = attributes
                .string(AttributeKey::Result)
                .unwrap_or(FrontendSort::KResult.as_str());
            let predicate_label = Label::sort_predicate(&Sort::new(result_sort)).name;
            // A declared result sort whose role has no sort predicate (a numeral, a `#` sort) has
            // no K terms, so no strict argument can ever cool to it.
            if let Err(missing) = super::sort_predicate_in_module(productions, sorts, result_sort) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidHeatCool,
                    format!(
                        "Definition is missing function {predicate_label} required for strictness. {}",
                        missing.remedy(result_sort, &predicate_label)
                    ),
                    sentence,
                ));
                continue;
            }
            // Heating moves the subterm the rule matches as `HOLE` to the front of the computation
            // while it is not yet a result, and cooling plugs it back once it is: the condition
            // below is on that matched subterm. A sentence whose left-hand side does not match
            // `HOLE` leaves the condition on a variable nothing binds, which holds or fails for
            // values unrelated to the term being rewritten.
            let body = match &*sentence {
                Sentence::Rule { body, .. } | Sentence::Context { body, .. } => body,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => unreachable!("the kind is decided above"),
            };
            if !matches_hole(body) {
                let (attribute, state) = if heat {
                    ("heat", "is not yet")
                } else {
                    ("cool", "is")
                };
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidHeatCool,
                    format!(
                        "A {attribute} rule must match HOLE on its left-hand side: it applies only when the subterm it matches as HOLE {state} of the result sort {result_sort}, and this rule matches none."
                    ),
                    sentence,
                ));
                continue;
            }
            let requires = match sentence {
                Sentence::Rule { requires, .. } | Sentence::Context { requires, .. } => requires,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => unreachable!("the kind is decided above"),
            };
            let predicate = Term::apply(predicate_label, vec![Term::variable("HOLE")]);
            let condition = if heat {
                Term::apply("notBool_", vec![predicate])
            } else {
                predicate
            };
            let original = mem::replace(requires, Term::Sequence(Vec::new()));
            *requires = Term::apply("_andBool_", vec![original, condition]);
            if first_lowered.is_none() {
                first_lowered = Some(Diagnostic::error(
                    DiagnosticCode::InvalidHeatCool,
                    super::missing_bool_message("A heat or cool attribute"),
                    sentence,
                ));
            }
        }
        if let Some(missing_bool) = first_lowered
            && !super::import_bool(module, resolved)
        {
            diagnostics.push(missing_bool);
        }
    }
    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ResolveHeatCoolError { diagnostics })
    }
}

/// Whether the left-hand side of `body` matches `HOLE`: the variable occurs outside every
/// rewrite or on the left of one.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn matches_hole(body: &Term) -> bool {
    match body.unannotated() {
        Term::Variable { name, .. } => name == "HOLE",
        Term::Rewrite { left, .. } => matches_hole(left),
        Term::Apply { arguments, .. } => arguments.iter().any(matches_hole),
        Term::Sequence(items) => items.iter().any(matches_hole),
        Term::As { pattern, alias } => matches_hole(pattern) || matches_hole(alias),
        _ => false,
    }
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::{
        definition::Sentence,
        diagnostic::DiagnosticCode,
        kompile::stage_harness::{run_to_stage, sentence_changes},
    };

    /// Heating takes the subterm matched as HOLE out for evaluation while it is not yet a
    /// result; cooling puts it back once it is one. So the stage conjoins `notBool
    /// isKResult(HOLE)` to the condition of every heating rule and `isKResult(HOLE)` to that of
    /// every cooling rule, keeping the condition the rule already has. The rules it receives
    /// are the ones context lowering produced from strictness, which is where most heating and
    /// cooling rules of a definition come from.
    #[test]
    fn heating_waits_for_a_non_result_and_cooling_for_a_result() {
        let run = run_to_stage(
            r#"
module BOOL
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val | seq(Exp, Exp) [seqstrict, symbol(seq)]
  configuration <k> v </k>
endmodule
"#,
            "resolve heat/cool attributes",
        );
        let (added, removed) = sentence_changes(&run.input, run.output());
        let conditions = |sentences: &[(&str, &Sentence)]| {
            let mut conditions = sentences
                .iter()
                .map(|(_, sentence)| {
                    let Sentence::Rule {
                        body,
                        requires,
                        attributes,
                        ..
                    } = sentence
                    else {
                        panic!("the stage changed a sentence that is not a rule: {sentence:?}")
                    };
                    let kind = if attributes.get("heat").is_some() {
                        "heat"
                    } else {
                        assert!(attributes.get("cool").is_some(), "{body}");
                        "cool"
                    };
                    (kind, body.to_string(), requires.to_string())
                })
                .collect::<Vec<_>>();
            conditions.sort();
            conditions
        };
        let (before, after) = (conditions(&removed), conditions(&added));
        // The two heating and two cooling rules of `seq`, each rewritten once, bodies kept.
        assert_eq!(before.len(), 4, "{before:#?}");
        assert_eq!(after.len(), 4, "{after:#?}");
        for ((kind, body, old), (new_kind, new_body, new)) in before.iter().zip(&after) {
            assert_eq!((kind, body), (new_kind, new_body));
            let test = match *kind {
                "heat" => "`notBool_`(isKResult(HOLE))",
                _ => "isKResult(HOLE)",
            };
            assert_eq!(new, &format!("`_andBool_`({old},{test})"), "{body}");
        }
    }

    /// A heating or cooling rule applies only when the subterm it matches as HOLE is not yet,
    /// or is, a result. A rule that matches no HOLE on its left-hand side, including one that
    /// names HOLE only in its condition, would test a variable nothing binds: each is rejected
    /// at the rule, and all of them in one run.
    #[test]
    fn heat_and_cool_rules_without_a_matched_hole_are_rejected_at_the_rule() {
        let run = run_to_stage(
            r#"
module BOOL
endmodule
module MAIN
  syntax K
  syntax Bool
  syntax KResult ::= Op
  syntax Op ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax Bool ::= p(Op) [function, symbol(p)]
  rule a => b [heat]
  rule b => a [cool]
  rule a => b requires p(HOLE:Op) [heat]
endmodule
"#,
            "resolve heat/cool attributes",
        );
        let error = run.error();
        assert_eq!(error.stage, "resolve heat/cool attributes");
        let mut rejected = error
            .diagnostics
            .iter()
            .map(|diagnostic| {
                assert_eq!(diagnostic.code, DiagnosticCode::InvalidHeatCool);
                let location = diagnostic.location.expect("the diagnostic is located");
                (
                    location.start_line,
                    location.start_column,
                    diagnostic.message.split(':').next().unwrap().to_owned(),
                )
            })
            .collect::<Vec<_>>();
        rejected.sort();
        assert_eq!(
            rejected,
            [
                (
                    10,
                    3,
                    "A heat rule must match HOLE on its left-hand side".to_owned()
                ),
                (
                    11,
                    3,
                    "A cool rule must match HOLE on its left-hand side".to_owned()
                ),
                (
                    12,
                    3,
                    "A heat rule must match HOLE on its left-hand side".to_owned()
                ),
            ]
        );
    }
}
