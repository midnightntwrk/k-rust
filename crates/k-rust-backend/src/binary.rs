//! Definition-aware binary KORE input for backend terms and constrained states.

use std::{error::Error, fmt};

use k_rust_kore::kore::{
    ast as kore,
    binary::{self as wire, BinaryError},
};

use crate::{
    definition::{BackendDefinition, DefinitionError},
    rewrite::Pattern,
    rule::Predicate,
    term::{Sort, Term, TermKind},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    Binary(BinaryError),
    Definition(DefinitionError),
    MalformedConstraint,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Binary(error) => error.fmt(formatter),
            Self::Definition(error) => error.fmt(formatter),
            Self::MalformedConstraint => write!(
                formatter,
                "binary KORE constraint must be \\equals(predicate, true)"
            ),
        }
    }
}

impl Error for DecodeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Binary(error) => Some(error),
            Self::Definition(error) => Some(error),
            Self::MalformedConstraint => None,
        }
    }
}

impl From<BinaryError> for DecodeError {
    fn from(error: BinaryError) -> Self {
        Self::Binary(error)
    }
}

impl From<DefinitionError> for DecodeError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

/// Decode and validate one binary KORE backend term.
pub fn decode_term(definition: &BackendDefinition, input: &[u8]) -> Result<Term, DecodeError> {
    let syntax = strip_raw_term(wire::decode_term(input)?);
    Ok(definition.internalize_term(&syntax, &[])?)
}

/// Decode and validate a binary KORE term with Booster-style constraints.
pub fn decode_pattern(
    definition: &BackendDefinition,
    input: &[u8],
) -> Result<Pattern, DecodeError> {
    let syntax = wire::decode_pattern(input)?;
    let term = definition.internalize_term(&strip_raw_term(syntax.term), &[])?;
    let constraints = syntax
        .constraints
        .iter()
        .map(|constraint| decode_constraint(definition, constraint))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Pattern { term, constraints })
}

fn decode_constraint(
    definition: &BackendDefinition,
    syntax: &kore::Pattern,
) -> Result<Predicate, DecodeError> {
    let kore::Pattern::Application { symbol, arguments } = syntax else {
        return Err(DecodeError::MalformedConstraint);
    };
    let [left, right] = arguments.as_slice() else {
        return Err(DecodeError::MalformedConstraint);
    };
    if symbol.name != "\\equals" || !symbol.sort_parameters.is_empty() {
        return Err(DecodeError::MalformedConstraint);
    }

    let left = definition.internalize_term(left, &[])?;
    let right = definition.internalize_term(right, &[])?;
    if is_true_bool(&right) {
        Ok(Predicate::Term(left))
    } else if is_true_bool(&left) {
        Ok(Predicate::Term(right))
    } else {
        Err(DecodeError::MalformedConstraint)
    }
}

fn is_true_bool(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "true"
    )
}

/// Apply the compatibility rewrite used by the pinned backend for LLVM's
/// `rawTerm(inj{S, SortKItem}(X))` wrapper.
fn strip_raw_term(syntax: kore::Pattern) -> kore::Pattern {
    let kore::Pattern::Application { symbol, arguments } = &syntax else {
        return syntax;
    };
    if symbol.name != "rawTerm" || !symbol.sort_parameters.is_empty() {
        return syntax;
    }
    let [
        kore::Pattern::Application {
            symbol: injection,
            arguments: injected,
        },
    ] = arguments.as_slice()
    else {
        return syntax;
    };
    let [_, target] = injection.sort_parameters.as_slice() else {
        return syntax;
    };
    let [inner] = injected.as_slice() else {
        return syntax;
    };
    if injection.name == "inj" && is_sort_k_item(target) {
        inner.clone()
    } else {
        syntax
    }
}

fn is_sort_k_item(sort: &kore::Sort) -> bool {
    matches!(sort, kore::Sort::Application { name, arguments } if name == "SortKItem" && arguments.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust_kore::kore::{
        binary::{ConstrainedPattern, encode_pattern, encode_term},
        parser::{parse_definition, parse_pattern},
    };

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"
            []
            module TEST
              sort SortS{} []
              sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
              sort SortKItem{} []
              symbol state{}(SortS{}) : SortS{} [constructor{}()]
              symbol value{}() : SortS{} [constructor{}()]
            endmodule []
            "#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "TEST").expect("definition should internalize")
    }

    fn syntax(source: &str) -> kore::Pattern {
        parse_pattern(source).expect("pattern should parse")
    }

    #[test]
    fn decodes_definition_aware_terms() {
        let bytes = encode_term(&syntax("state{}(value{}())")).unwrap();
        let term = decode_term(&definition(), &bytes).unwrap();
        let TermKind::Application { symbol, .. } = term.kind() else {
            panic!("expected an application")
        };
        assert_eq!(symbol.name.as_ref(), "state");
    }

    #[test]
    fn decodes_booster_constraints() {
        let predicate = syntax("value{}()");
        let wrapper = kore::Pattern::Application {
            symbol: kore::Symbol {
                name: "\\equals".into(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![predicate.clone(), syntax(r#"\dv{SortBool{}}("true")"#)],
        };
        let bytes = encode_pattern(&ConstrainedPattern::new(
            syntax("state{}(value{}())"),
            vec![wrapper],
        ))
        .unwrap();
        let decoded = decode_pattern(&definition(), &bytes).unwrap();
        assert_eq!(decoded.constraints.len(), 1);
        let Predicate::Term(term) = &decoded.constraints[0] else {
            panic!("expected a Boolean term predicate")
        };
        assert_eq!(
            term,
            &definition().internalize_term(&predicate, &[]).unwrap()
        );
    }

    #[test]
    fn strips_llvm_raw_term_wrappers() {
        let wrapped = syntax("rawTerm{}(inj{SortS{}, SortKItem{}}(value{}()))");
        let bytes = encode_term(&wrapped).unwrap();
        let decoded = decode_term(&definition(), &bytes).unwrap();
        assert_eq!(
            decoded,
            definition()
                .internalize_term(&syntax("value{}()"), &[])
                .unwrap()
        );
    }

    #[test]
    fn rejects_unknown_symbols_and_malformed_constraints() {
        let unknown = encode_term(&syntax("missing{}()")).unwrap();
        assert!(matches!(
            decode_term(&definition(), &unknown),
            Err(DecodeError::Definition(DefinitionError::UnknownSymbol(name))) if name == "missing"
        ));

        let malformed = encode_pattern(&ConstrainedPattern::new(
            syntax("value{}()"),
            vec![syntax("value{}()")],
        ))
        .unwrap();
        assert_eq!(
            decode_pattern(&definition(), &malformed),
            Err(DecodeError::MalformedConstraint)
        );
    }
}
