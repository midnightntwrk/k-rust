//! Named constants (`#[k::constant]`): a declared sort and a ground value.
//!
//! A constant is a name for a term. Its value is a literal or a constructor
//! application whose arguments are ground values, possibly through other
//! constants, so it has no variables and evaluates nothing. The compiler
//! substitutes the value at every use before semantic analysis, so no
//! constant reaches the semantic IR or emitted K.

use serde::{Deserialize, Serialize};

use super::keys::WireKeys;
use crate::stage::stage_shape;
use crate::transport::grammar::{GrammarTransportError, Term};
use crate::{DescriptorStage, ProvenanceKey, ProvenanceRole};

stage_shape! {
    /// A named constant's declared sort and value.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "ConstantDescriptor",
        deny_unknown_fields,
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        )
    )]
    pub struct ConstantPayload<S: Stage> {
        /// The declared sort, keyed `constant_type`.
        pub sort: S::Sort => [sort],
        /// The value, whose nodes are keyed as a rule result's are.
        pub value: Term<S> => [nested],
    }
}

/// Stable descriptor-stage form of [`ConstantPayload`].
pub type ConstantDescriptor = ConstantPayload<DescriptorStage>;

impl ConstantDescriptor {
    /// The primary key of a constant descriptor: the constant's name.
    #[must_use]
    pub const fn expected_primary_key() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::ConstantDeclaration, 0)
    }

    /// The keys of the constant's wire nodes, with its fixed declaration
    /// key, the name.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] when a key has another role than
    /// its node's, or two nodes define one key.
    pub(crate) fn wire_keys(&self) -> Result<WireKeys, GrammarTransportError> {
        let mut keys = WireKeys::default();
        keys.fixed(ProvenanceRole::ConstantDeclaration)?;
        super::grammar::collect_constant_keys(self, &mut keys)?;
        Ok(keys)
    }
}

#[cfg(test)]
mod tests {
    use super::ConstantDescriptor;
    use crate::transport::detail::GrammarTermReason;
    use crate::{
        BuiltinSort, DescriptorLiteral, DescriptorSortRef, DescriptorSortReference, DescriptorTerm,
        GrammarTransportError, ProvenanceKey, ProvenanceRole,
    };

    fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
        ProvenanceKey::new(role, ordinal)
    }

    fn constant(value: DescriptorTerm) -> ConstantDescriptor {
        ConstantDescriptor {
            sort: DescriptorSortReference {
                key: key(ProvenanceRole::ConstantType, 0),
                sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
            },
            value,
        }
    }

    fn literal() -> DescriptorTerm {
        DescriptorTerm::Literal {
            key: key(ProvenanceRole::RuleRightLiteral, 0),
            literal: DescriptorLiteral::Int("1".into()),
        }
    }

    /// A constant's value is keyed as a rule result is, and holds what a
    /// rule result may: no claim or cell term, and no pattern.
    #[test]
    fn a_constant_value_is_a_result_term() {
        let anchors = [
            key(ProvenanceRole::ConstantDeclaration, 0),
            key(ProvenanceRole::ConstantType, 0),
            key(ProvenanceRole::ConstantValue, 0),
            key(ProvenanceRole::RuleRightLiteral, 0),
        ];
        constant(literal())
            .wire_keys()
            .unwrap()
            .close(&anchors)
            .unwrap();
        let anonymous = DescriptorTerm::Anonymous {
            key: key(ProvenanceRole::ClaimAnonymous, 0),
            sort: DescriptorSortReference {
                key: key(ProvenanceRole::ClaimAnonymousSort, 0),
                sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
            },
            spelling: "_x".into(),
        };
        assert_eq!(
            constant(anonymous).wire_keys().err(),
            Some(GrammarTransportError::InvalidTerm(
                GrammarTermReason::UnexpectedClaimTerm
            ))
        );
        let pattern = DescriptorTerm::As {
            key: key(ProvenanceRole::PatternAs, 0),
            binding_key: key(ProvenanceRole::PatternAsBinding, 0),
            name: "x".into(),
            pattern: Box::new(literal()),
        };
        assert_eq!(
            constant(pattern).wire_keys().err(),
            Some(GrammarTransportError::InvalidTerm(
                GrammarTermReason::PatternAsOutsideLeftHandSide
            ))
        );
    }
}
