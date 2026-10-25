//! Named constants (`#[k::constant]`): a declared sort and a ground value.
//!
//! A constant is a name for a term. Its value is a literal or a constructor
//! application whose arguments are ground values, possibly through other
//! constants, so it has no variables and evaluates nothing. The compiler
//! substitutes the value at every use before semantic analysis, so no
//! constant reaches the semantic IR or emitted K.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

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

    /// Every parser key the descriptor's provenance must hold: the name,
    /// the type, the value expression, and the value's nodes.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] when a key is not the parser's.
    pub(crate) fn expected_provenance_keys(
        &self,
    ) -> Result<BTreeSet<ProvenanceKey>, GrammarTransportError> {
        let mut keys = BTreeSet::from([
            Self::expected_primary_key(),
            ProvenanceKey::new(ProvenanceRole::ConstantValue, 0),
        ]);
        super::grammar::collect_constant_keys(self, &mut keys)?;
        Ok(keys)
    }
}
