//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Propagate production macro kinds onto their defining rules.
#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::AttributeKey;
use crate::definition::{
    Definition, HeadShape, LabelHead, ProductionCatalog, ResolveError, RuleHead, Sentence,
};

/// Mark each rule with the macro kind of the production its top-level rewrite's left side applies.
pub fn propagate_macro_attributes(definition: &Definition) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(definition, propagate_macro_attributes_pass, None)
}

pub(crate) fn propagate_macro_attributes_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            propagate_macro_attribute(crate::definition::sentence_mut(sentence), productions);
        }
    }
    Ok(output)
}

/// Mark one rule with the macro kind of the production its top-level rewrite's left side applies
/// ([`RuleHead::of`], root aliases looked through).
///
/// `productions` is the catalog of the module that declares the rule. Simplification rules and
/// sentences that are not rules are left unchanged.
pub(crate) fn propagate_macro_attribute(
    sentence: &mut Sentence,
    productions: &ProductionCatalog<'_>,
) {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return;
    };
    if attributes.has(AttributeKey::Simplification) {
        return;
    }
    // The head is the rule's head as every stage and check reads it, root aliases looked
    // through: `m(X) #as V => R` is a rule of `m` as `m(X) => R[m(X)/V]` is. A body without a
    // top rewrite states no expansion of the head, so it is not a macro rule.
    let head = RuleHead::of(body);
    if head.shape() != HeadShape::TopRewrite || head.context.is_some() {
        return;
    }
    let Some(label) = head.label() else {
        return;
    };
    if !productions.macro_labels().contains(&LabelHead::from(label)) {
        return;
    }
    let Some(production_attributes) = productions.attributes_for(&LabelHead::from(label)) else {
        return;
    };
    if let Some(attribute) = AttributeKey::MACRO_LIKE
        .into_iter()
        .find(|attribute| production_attributes.has(*attribute))
    {
        attributes.mark(attribute);
    }
}

#[cfg(test)]
mod tests {
    use crate::definition::AttributeKey;
    use crate::kompile::stage_harness::{labelled, render, run_to_stage};

    const SOURCE: &str = r#"
module MAIN
  syntax K
  syntax Exp ::= "a" [symbol(a)] | "b" [symbol(b)] | done(Exp) [symbol(done)]
  syntax Exp ::= m(Exp) [macro, symbol(m)]
  syntax Exp ::= h(Exp) [function, symbol(h)]
  configuration <k> a </k>
  rule m(X) #as _T => done(X) [label(macroRule)]
  rule h(X) => m(X) [label(user)]
endmodule
"#;

    /// `m(X) #as _T => done(X)` is a rule of the macro production `m` (an alias names the
    /// matched term and constrains nothing), so it receives the production's `macro` kind, and
    /// expansion then rewrites the application of `m` in `h`'s right side as it would with
    /// `m(X) => done(X)`.
    #[test]
    fn an_aliased_rule_of_a_macro_production_is_a_macro_rule() {
        let propagated = run_to_stage(SOURCE, "propagate macro attributes");
        let rule = labelled(propagated.output(), "MAIN", "macroRule");
        assert_eq!(rule.len(), 1);
        assert!(
            rule[0].attributes().has(AttributeKey::Macro),
            "{}",
            render(rule[0])
        );

        let expanded = run_to_stage(SOURCE, "expand macros");
        let user = labelled(expanded.output(), "MAIN", "user");
        assert_eq!(user.len(), 1);
        let rendered = render(user[0]);
        assert!(
            rendered.contains("done(") && !rendered.contains("m("),
            "{rendered}"
        );
    }
}
