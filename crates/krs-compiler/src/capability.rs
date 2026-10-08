//! Backend capability requirements of a definition (V8).
//!
//! The compiler derives a deterministic list of [`CapabilityRequirement`]s
//! from Definition IR. Each backend route states which features it lacks in
//! one table (`krs_k_rust::ROUTE_CAPABILITIES`); a route that lacks a required
//! feature refuses the definition with `krs::capability::unavailable` before
//! any compilation, and never weakens it. `krs emit-k` still writes the
//! faithful `.k`, marks each affected sentence with a `// krs-capability:`
//! comment, and records the requirements in `symbols.json`.
//!
//! Features are appended at the tail of [`CapabilityFeature`] and of the
//! derivation in [`sentence_features`].

use krs_ir::SourceMapKey;
use krs_ir_levels::{DefinitionIr, DefinitionSentence, RuleSentence};
use serde::{Deserialize, Serialize};

/// One language feature that some backend route cannot run.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CapabilityFeature {
    /// A rule with K's `anywhere` attribute (`#[k::rule(anywhere)]`).
    AnywhereRule,
}

impl CapabilityFeature {
    /// Every feature, in catalog order.
    pub const ALL: &'static [Self] = &[Self::AnywhereRule];

    /// The stable feature name used in sidecars, comments, and route tables.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AnywhereRule => "AnywhereRule",
        }
    }

    /// The noun phrase a refusal uses for the sentences that need the feature.
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::AnywhereRule => "anywhere rules",
        }
    }
}

/// One sentence that needs a capability.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CapabilityRequirement {
    feature: CapabilityFeature,
    /// Emitted name of the sentence (its K label).
    symbol: String,
    origin: SourceMapKey,
}

impl CapabilityRequirement {
    /// The required feature.
    #[must_use]
    pub const fn feature(&self) -> CapabilityFeature {
        self.feature
    }

    /// The emitted name of the sentence that needs it.
    #[must_use]
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    /// The source-map key of that sentence.
    #[must_use]
    pub const fn origin(&self) -> &SourceMapKey {
        &self.origin
    }
}

/// The features one rule sentence needs, in catalog order.
#[must_use]
pub fn sentence_features(sentence: &RuleSentence) -> Vec<CapabilityFeature> {
    let mut features = Vec::new();
    if sentence.anywhere().is_some() {
        features.push(CapabilityFeature::AnywhereRule);
    }
    features
}

/// Every capability requirement of a definition, ordered by feature, then sentence name.
#[must_use]
pub fn capability_requirements(definition: &DefinitionIr) -> Vec<CapabilityRequirement> {
    let mut requirements = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            let DefinitionSentence::Rule(rule) = sentence else {
                continue;
            };
            for feature in sentence_features(rule) {
                requirements.push(CapabilityRequirement {
                    feature,
                    symbol: rule.label().emitted_name().to_owned(),
                    origin: rule.origin().key().clone(),
                });
            }
        }
    }
    requirements.sort();
    requirements
}

/// The refusal text for a route that lacks `feature`, naming the sentences that need it.
#[must_use]
pub fn unavailable_message(
    feature: CapabilityFeature,
    route_reason: &str,
    requirements: &[CapabilityRequirement],
) -> String {
    let symbols = requirements
        .iter()
        .filter(|requirement| requirement.feature == feature)
        .map(CapabilityRequirement::symbol)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "definition contains {} [{symbols}]; {route_reason}",
        feature.description()
    )
}
