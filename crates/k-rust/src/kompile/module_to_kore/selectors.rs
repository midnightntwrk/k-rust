//! Exact contracts of compiler sort projections, using their actual injected embedding.
//!
//! The forward equation alone does not exclude additional inputs from a projection's domain.
//! These ordinary ML axioms state that domain and its conditional inverse explicitly, so all
//! consumers of the emitted definition see the same meaning. Field projections are separate.

use super::*;

/// The suffixes of a contract's `UNIQUE_ID` after its forward equation's: the exact domain, then
/// the conditional inverse.
const CONTRACT_SUFFIXES: [&str; 2] = ["selector-domain", "selector-inverse"];

/// The `UNIQUE_ID` of the forward equation a selector contract `id` was emitted beside, when
/// `id` is a contract's. A contract is generated from the sort projection, as its forward
/// equation is, so its provenance names the pass that generated that equation.
pub(crate) fn contract_forward_id(id: &str) -> Option<&str> {
    let (forward, suffix) = id.rsplit_once('.')?;
    CONTRACT_SUFFIXES.contains(&suffix).then_some(forward)
}

/// Companion axioms of a canonical generated sort projection's identity equation.
/// The marker selects this compiler feature; the checked identity supplies its embedding.
pub(super) fn contracts(
    sentence: &Sentence,
    context: &RuleEmissionContext<'_, '_>,
) -> Result<Vec<(KoreSentence, KAttributes)>, ModuleToKoreError> {
    if !sentence.attributes().has(AttributeKey::Projection)
        || !sentence.attributes().input_addresses().is_empty()
        || [
            AttributeKey::Concrete,
            AttributeKey::Symbolic,
            AttributeKey::Owise,
            AttributeKey::Priority,
            AttributeKey::Simplification,
            AttributeKey::Anywhere,
        ]
        .into_iter()
        .any(|key| sentence.attributes().has(key))
    {
        return Ok(Vec::new());
    }
    let (injected, variables) = context.injector.inject_sentence_bound(sentence)?;
    let Sentence::Rule {
        body,
        requires,
        ensures,
        attributes,
    } = &injected
    else {
        return Ok(Vec::new());
    };
    let truth = |term: &Term| {
        matches!(term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort.is_builtin(BuiltinSort::Bool))
    };
    if !truth(requires) || !truth(ensures) || variables.names().next().is_some() {
        return Ok(Vec::new());
    }
    let Term::Rewrite { left, right } = body.unannotated() else {
        return Ok(Vec::new());
    };
    let Term::Variable {
        sort: Some(sort), ..
    } = right.unannotated()
    else {
        return Ok(Vec::new());
    };
    let Term::Apply { label, arguments } = left.unannotated() else {
        return Ok(Vec::new());
    };
    if Label::projection(sort).as_ref() != Some(label) || arguments.len() != 1 {
        return Ok(Vec::new());
    }
    // An authored override or an additional equation is not the compiler's canonical
    // selector implementation. Do not strengthen that source with a generated exact domain.
    let offered = context
        .module_rules
        .iter()
        .filter(|rule| {
            let Sentence::Rule { body, .. } = rule else {
                return false;
            };
            let Term::Rewrite { left, .. } = body.unannotated() else {
                return false;
            };
            matches!(left.unannotated(), Term::Apply { label: head, .. } if head.name == label.name)
        })
        .count();
    if offered != 1 {
        return Ok(Vec::new());
    }
    let converter = context.converter.with_sort_variables(&variables);
    let converted_left = converter.convert(left)?;
    let Pattern::Application { symbol, arguments } = &converted_left else {
        return Ok(Vec::new());
    };
    let converted_right = converter.convert(right)?;
    let Pattern::Variable(value) = &converted_right else {
        return Ok(Vec::new());
    };
    let Some(embedding) = arguments.first() else {
        return Ok(Vec::new());
    };
    // An embedding is one occurrence of the source value, wrapped only by the compiler's
    // injections and K-sequence singleton. Never strengthen an arbitrary projection rule.
    fn is_embedding(pattern: &Pattern, value: &Variable) -> bool {
        if pattern == &Pattern::Variable(value.clone()) {
            return true;
        }
        let Pattern::Application { symbol, arguments } = pattern else {
            return false;
        };
        match arguments.as_slice() {
            [inner] if symbol.is(WellKnownSymbol::Inj) => is_embedding(inner, value),
            [
                inner,
                Pattern::Application {
                    symbol: end,
                    arguments: empty,
                },
            ] if symbol.is(WellKnownSymbol::KSeq)
                && end.is(WellKnownSymbol::DotK)
                && empty.is_empty() =>
            {
                is_embedding(inner, value)
            }
            _ => false,
        }
    }
    if !is_embedding(embedding, value) {
        return Ok(Vec::new());
    }
    let predicate_sort = KoreSort::Variable("R".into());
    let input_sort = converter.convert_sort(&Sort::builtin(BuiltinSort::K))?;
    let input = Variable {
        kind: VariableKind::Element,
        name: "SelectorInput".into(),
        sort: input_sort.clone(),
    };
    let application = Pattern::Application {
        symbol: symbol.clone(),
        arguments: vec![Pattern::Variable(input.clone())],
    };
    let domain = Pattern::Ceil {
        operand_sort: Box::new(value.sort.clone()),
        result_sort: predicate_sort.clone(),
        argument: Box::new(application.clone()),
    };
    // A generated binder: K3 holds, since `is_embedding` found `value` in the embedding.
    let image = super::binders::generated_exists(
        predicate_sort.clone(),
        value.clone(),
        Pattern::Equals {
            operand_sort: Box::new(input_sort.clone()),
            result_sort: predicate_sort.clone(),
            left: Box::new(Pattern::Variable(input.clone())),
            right: Box::new(embedding.clone()),
        },
    );
    let reconstructed = embedding
        .substitute_free(value, &application)
        .expect("an embedding has no binders");
    let domain_axiom = Pattern::Implies {
        sort: predicate_sort.clone(),
        left: Box::new(Pattern::Top {
            sort: predicate_sort.clone(),
        }),
        right: Box::new(Pattern::Equals {
            operand_sort: Box::new(predicate_sort.clone()),
            result_sort: predicate_sort.clone(),
            left: Box::new(domain.clone()),
            right: Box::new(image),
        }),
    };
    let inverse_axiom = Pattern::Implies {
        sort: predicate_sort.clone(),
        left: Box::new(domain),
        right: Box::new(Pattern::Equals {
            operand_sort: Box::new(input_sort.clone()),
            result_sort: predicate_sort,
            left: Box::new(reconstructed),
            right: Box::new(Pattern::And {
                sort: input_sort.clone(),
                arguments: vec![Pattern::Variable(input), Pattern::Top { sort: input_sort }],
            }),
        }),
    };
    Ok([
        (CONTRACT_SUFFIXES[0], domain_axiom),
        (CONTRACT_SUFFIXES[1], inverse_axiom),
    ]
    .into_iter()
    .map(|(suffix, pattern)| {
        let mut source = attributes.clone();
        if let Some(id) = attributes.string(AttributeKey::UniqueId) {
            source.set(
                AttributeKey::UniqueId,
                Value::String(format!("{id}.{suffix}")),
            );
        }
        // The inverse is a local conditional equality, not a competing function row.
        if suffix == "selector-inverse" {
            source.mark(AttributeKey::Simplification);
        }
        let attributes =
            emit_attributes(source.semantic_entries(), context.valued, &BTreeMap::new());
        (
            KoreSentence::Axiom {
                parameters: vec!["R".into()],
                pattern: Box::new(pattern),
                attributes,
            },
            source,
        )
    })
    .collect())
}
