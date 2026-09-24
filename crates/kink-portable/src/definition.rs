use crate::identity::{
    BaselineFamily, DefinitionIdentityModule, DefinitionIdentitySummary, IdentityError,
    IdentityErrorKind, baseline_family_id, domain, exact_object, generated_lineage_id,
    input_lineage_id, malformed, nonempty_string, object, parse_digest, parse_u64,
};
use crate::json::{Digest, SemanticJson, digest};
use std::collections::{BTreeMap, BTreeSet};

/// One-based source range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Location {
    /// Inclusive start line.
    pub start_line: u64,
    /// Inclusive start column.
    pub start_column: u64,
    /// Inclusive end line.
    pub end_line: u64,
    /// Inclusive end column.
    pub end_column: u64,
}

impl Location {
    fn from_json(value: &SemanticJson) -> Result<Self, IdentityError> {
        let fields = exact_object(
            value,
            &["startLine", "startColumn", "endLine", "endColumn"],
            "location",
        )?;
        let location = Self {
            start_line: parse_u64(fields.get("startLine"), "startLine")?,
            start_column: parse_u64(fields.get("startColumn"), "startColumn")?,
            end_line: parse_u64(fields.get("endLine"), "endLine")?,
            end_column: parse_u64(fields.get("endColumn"), "endColumn")?,
        };
        if location.start_line == 0
            || location.start_column == 0
            || location.end_line == 0
            || location.end_column == 0
            || (location.end_line, location.end_column)
                < (location.start_line, location.start_column)
        {
            return Err(IdentityError::new(
                IdentityErrorKind::IllFormed,
                "location is not a nonempty ordered one-based range",
            ));
        }
        Ok(location)
    }

    /// Returns the closed location value.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        object([
            ("startLine", ordinal(self.start_line)),
            ("startColumn", ordinal(self.start_column)),
            ("endLine", ordinal(self.end_line)),
            ("endColumn", ordinal(self.end_column)),
        ])
    }
}

/// Closed v1 sentence kinds. Generated status is represented separately.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SentenceKind {
    /// Rewrite rule.
    Rule,
    /// Reachability claim.
    Claim,
    /// Context sentence.
    Context,
    /// Alias sentence.
    Alias,
    /// Configuration sentence.
    Configuration,
}

impl SentenceKind {
    fn parse(value: &str) -> Result<Self, IdentityError> {
        match value {
            "rule" => Ok(Self::Rule),
            "claim" => Ok(Self::Claim),
            "context" => Ok(Self::Context),
            "alias" => Ok(Self::Alias),
            "configuration" => Ok(Self::Configuration),
            _ => Err(IdentityError::new(
                IdentityErrorKind::UnsupportedForm,
                format!("unsupported sentence kind {value}"),
            )),
        }
    }

    /// Returns the frozen spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Rule => "rule",
            Self::Claim => "claim",
            Self::Context => "context",
            Self::Alias => "alias",
            Self::Configuration => "configuration",
        }
    }
}

/// Closed recursive portable-term-v1 node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermNode {
    /// Typed token text.
    Token { text: String },
    /// Typed sentence variable.
    Variable { name: String },
    /// Application with native-production identity separate from display label.
    Application {
        /// Fully qualified production identity.
        symbol_id: Digest,
        /// Display label.
        label: String,
        /// Ordered arguments.
        args: Vec<Term>,
    },
    /// Sort-preserving rewrite children.
    Rewrite { left: Box<Term>, right: Box<Term> },
    /// Ordered sequence with no invented homogeneous-sort law.
    Sequence { items: Vec<Term> },
    /// Explicit sort injection.
    Injection {
        /// Child sort.
        from_sort: String,
        /// Wrapper sort.
        to_sort: String,
        /// Injected child.
        term: Box<Term>,
    },
}

/// Typed portable-term-v1 value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
    /// Result sort.
    pub sort: String,
    /// Closed node.
    pub node: TermNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SymbolSignature {
    label: String,
    result_sort: String,
    argument_sorts: Vec<String>,
}

impl Term {
    fn from_json(
        value: &SemanticJson,
        signatures: &mut BTreeMap<Digest, SymbolSignature>,
        variables: &mut BTreeMap<String, String>,
    ) -> Result<Self, IdentityError> {
        let fields = exact_object(value, &["encoding", "sort", "node"], "term")?;
        match fields.get("encoding").and_then(SemanticJson::as_str) {
            Some("portable-term-v1") => {}
            Some(other) => {
                return Err(IdentityError::new(
                    IdentityErrorKind::UnsupportedForm,
                    format!("unsupported term encoding {other}"),
                ));
            }
            None => return Err(malformed("term encoding must be a string")),
        }
        let sort = nonempty_string(fields.get("sort"), "term sort")?;
        let node_fields = fields
            .get("node")
            .and_then(SemanticJson::as_object)
            .ok_or_else(|| malformed("term node must be an object"))?;
        let kind = node_fields
            .get("kind")
            .and_then(SemanticJson::as_str)
            .ok_or_else(|| malformed("term node kind must be a string"))?;
        let node = match kind {
            "token" => {
                exact_object(
                    fields.get("node").expect("checked"),
                    &["kind", "text"],
                    "token",
                )?;
                let text = node_fields
                    .get("text")
                    .and_then(SemanticJson::as_str)
                    .ok_or_else(|| malformed("token text must be a string"))?
                    .to_owned();
                TermNode::Token { text }
            }
            "variable" => {
                exact_object(
                    fields.get("node").expect("checked"),
                    &["kind", "name"],
                    "variable",
                )?;
                let name = nonempty_string(node_fields.get("name"), "variable name")?;
                if let Some(previous) = variables.insert(name.clone(), sort.clone())
                    && previous != sort
                {
                    return Err(IdentityError::new(
                        IdentityErrorKind::IllFormed,
                        format!("variable {name} has contradictory sorts"),
                    ));
                }
                TermNode::Variable { name }
            }
            "application" => {
                exact_object(
                    fields.get("node").expect("checked"),
                    &["kind", "symbolId", "label", "args"],
                    "application",
                )?;
                let symbol_id = parse_digest(node_fields.get("symbolId"), "symbolId")?;
                let label = nonempty_string(node_fields.get("label"), "application label")?;
                let arguments = node_fields
                    .get("args")
                    .and_then(SemanticJson::as_array)
                    .ok_or_else(|| malformed("application args must be an array"))?;
                let mut args = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    args.push(Self::from_json(argument, signatures, variables)?);
                }
                let signature = SymbolSignature {
                    label: label.clone(),
                    result_sort: sort.clone(),
                    argument_sorts: args.iter().map(|argument| argument.sort.clone()).collect(),
                };
                if let Some(previous) = signatures.insert(symbol_id.clone(), signature.clone())
                    && previous != signature
                {
                    return Err(IdentityError::new(
                        IdentityErrorKind::IllFormed,
                        format!("symbol {symbol_id} has contradictory signatures"),
                    ));
                }
                TermNode::Application {
                    symbol_id,
                    label,
                    args,
                }
            }
            "rewrite" => {
                exact_object(
                    fields.get("node").expect("checked"),
                    &["kind", "left", "right"],
                    "rewrite",
                )?;
                let left = Box::new(Self::from_json(
                    node_fields
                        .get("left")
                        .ok_or_else(|| malformed("missing rewrite left"))?,
                    signatures,
                    variables,
                )?);
                let right = Box::new(Self::from_json(
                    node_fields
                        .get("right")
                        .ok_or_else(|| malformed("missing rewrite right"))?,
                    signatures,
                    variables,
                )?);
                if left.sort != right.sort {
                    return Err(IdentityError::new(
                        IdentityErrorKind::IllFormed,
                        "rewrite children have different sorts",
                    ));
                }
                TermNode::Rewrite { left, right }
            }
            "sequence" => {
                exact_object(
                    fields.get("node").expect("checked"),
                    &["kind", "items"],
                    "sequence",
                )?;
                let item_values = node_fields
                    .get("items")
                    .and_then(SemanticJson::as_array)
                    .ok_or_else(|| malformed("sequence items must be an array"))?;
                let mut items = Vec::with_capacity(item_values.len());
                for item in item_values {
                    items.push(Self::from_json(item, signatures, variables)?);
                }
                TermNode::Sequence { items }
            }
            "injection" => {
                exact_object(
                    fields.get("node").expect("checked"),
                    &["kind", "fromSort", "toSort", "term"],
                    "injection",
                )?;
                let from_sort = nonempty_string(node_fields.get("fromSort"), "fromSort")?;
                let to_sort = nonempty_string(node_fields.get("toSort"), "toSort")?;
                let term = Box::new(Self::from_json(
                    node_fields
                        .get("term")
                        .ok_or_else(|| malformed("missing injected term"))?,
                    signatures,
                    variables,
                )?);
                if term.sort != from_sort || sort != to_sort {
                    return Err(IdentityError::new(
                        IdentityErrorKind::IllFormed,
                        "injection sorts disagree with child or wrapper",
                    ));
                }
                TermNode::Injection {
                    from_sort,
                    to_sort,
                    term,
                }
            }
            other => {
                return Err(IdentityError::new(
                    IdentityErrorKind::UnsupportedForm,
                    format!("unsupported portable term node {other}"),
                ));
            }
        };
        Ok(Self { sort, node })
    }

    /// Returns the exact portable-term-v1 value.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        let node = match &self.node {
            TermNode::Token { text } => object([
                ("kind", SemanticJson::String("token".to_owned())),
                ("text", SemanticJson::String(text.clone())),
            ]),
            TermNode::Variable { name } => object([
                ("kind", SemanticJson::String("variable".to_owned())),
                ("name", SemanticJson::String(name.clone())),
            ]),
            TermNode::Application {
                symbol_id,
                label,
                args,
            } => object([
                ("kind", SemanticJson::String("application".to_owned())),
                ("symbolId", SemanticJson::String(symbol_id.to_string())),
                ("label", SemanticJson::String(label.clone())),
                (
                    "args",
                    SemanticJson::Array(args.iter().map(Term::to_json).collect()),
                ),
            ]),
            TermNode::Rewrite { left, right } => object([
                ("kind", SemanticJson::String("rewrite".to_owned())),
                ("left", left.to_json()),
                ("right", right.to_json()),
            ]),
            TermNode::Sequence { items } => object([
                ("kind", SemanticJson::String("sequence".to_owned())),
                (
                    "items",
                    SemanticJson::Array(items.iter().map(Term::to_json).collect()),
                ),
            ]),
            TermNode::Injection {
                from_sort,
                to_sort,
                term,
            } => object([
                ("kind", SemanticJson::String("injection".to_owned())),
                ("fromSort", SemanticJson::String(from_sort.clone())),
                ("toSort", SemanticJson::String(to_sort.clone())),
                ("term", term.to_json()),
            ]),
        };
        object([
            (
                "encoding",
                SemanticJson::String("portable-term-v1".to_owned()),
            ),
            ("sort", SemanticJson::String(self.sort.clone())),
            ("node", node),
        ])
    }
}

/// Canonically ordered unique sentence attribute.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Attribute {
    /// Attribute name.
    pub name: String,
    /// Optional typed term value.
    pub value: Option<Term>,
}

impl Attribute {
    fn from_json(
        value: &SemanticJson,
        signatures: &mut BTreeMap<Digest, SymbolSignature>,
        variables: &mut BTreeMap<String, String>,
    ) -> Result<Self, IdentityError> {
        let fields = exact_object(value, &["name", "value"], "attribute")?;
        let name = nonempty_string(fields.get("name"), "attribute name")?;
        let value = match fields.get("value") {
            Some(SemanticJson::Null) => None,
            Some(term) => Some(Term::from_json(term, signatures, variables)?),
            None => return Err(malformed("attribute lacks value")),
        };
        Ok(Self { name, value })
    }

    /// Returns the exact attribute value.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        object([
            ("name", SemanticJson::String(self.name.clone())),
            (
                "value",
                self.value
                    .as_ref()
                    .map_or(SemanticJson::Null, Term::to_json),
            ),
        ])
    }
}

/// Portable semantic sentence body plus human provenance fields.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SentenceValue {
    /// Owning module.
    pub module: String,
    /// Closed sentence kind.
    pub kind: SentenceKind,
    /// Optional, non-unique label.
    pub label: Option<String>,
    /// Logical source URI.
    pub source: String,
    /// Source range.
    pub location: Location,
    /// Meaning-bearing body.
    pub body: Term,
    /// Optional Bool condition.
    pub requires: Option<Term>,
    /// Optional Bool condition.
    pub ensures: Option<Term>,
    /// Sorted unique attributes.
    pub attributes: Vec<Attribute>,
}

impl SentenceValue {
    fn from_json(
        value: &SemanticJson,
        signatures: &mut BTreeMap<Digest, SymbolSignature>,
    ) -> Result<Self, IdentityError> {
        let fields = exact_object(
            value,
            &[
                "encoding",
                "module",
                "kind",
                "label",
                "source",
                "location",
                "body",
                "requires",
                "ensures",
                "attributes",
            ],
            "sentence value",
        )?;
        match fields.get("encoding").and_then(SemanticJson::as_str) {
            Some("portable-semantic-sentence-v1") => {}
            Some(other) => {
                return Err(IdentityError::new(
                    IdentityErrorKind::UnsupportedForm,
                    format!("unsupported sentence encoding {other}"),
                ));
            }
            None => return Err(malformed("sentence encoding must be a string")),
        }
        let module = nonempty_string(fields.get("module"), "sentence module")?;
        let kind = SentenceKind::parse(
            fields
                .get("kind")
                .and_then(SemanticJson::as_str)
                .ok_or_else(|| malformed("sentence kind must be a string"))?,
        )?;
        let label = match fields.get("label") {
            Some(SemanticJson::Null) => None,
            Some(SemanticJson::String(value)) => Some(value.clone()),
            _ => return Err(malformed("sentence label must be string or null")),
        };
        let source = nonempty_string(fields.get("source"), "sentence source")?;
        validate_logical_source(&source)?;
        let location = Location::from_json(
            fields
                .get("location")
                .ok_or_else(|| malformed("sentence lacks location"))?,
        )?;
        let mut variables = BTreeMap::new();
        let body = Term::from_json(
            fields
                .get("body")
                .ok_or_else(|| malformed("sentence lacks body"))?,
            signatures,
            &mut variables,
        )?;
        let requires = optional_term(fields.get("requires"), signatures, &mut variables)?;
        let ensures = optional_term(fields.get("ensures"), signatures, &mut variables)?;
        for condition in [&requires, &ensures].into_iter().flatten() {
            if condition.sort != "Bool" {
                return Err(IdentityError::new(
                    IdentityErrorKind::IllFormed,
                    "requires and ensures must be Bool-sorted",
                ));
            }
        }
        let attribute_values = fields
            .get("attributes")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| malformed("sentence attributes must be an array"))?;
        let mut attributes = Vec::with_capacity(attribute_values.len());
        for attribute in attribute_values {
            attributes.push(Attribute::from_json(attribute, signatures, &mut variables)?);
        }
        let names: Vec<&str> = attributes
            .iter()
            .map(|attribute| attribute.name.as_str())
            .collect();
        if names.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(IdentityError::new(
                IdentityErrorKind::NonCanonicalSet,
                "attributes are not strictly sorted by unique name",
            ));
        }
        Ok(Self {
            module,
            kind,
            label,
            source,
            location,
            body,
            requires,
            ensures,
            attributes,
        })
    }

    /// Returns the exact portable semantic sentence value.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        object([
            (
                "encoding",
                SemanticJson::String("portable-semantic-sentence-v1".to_owned()),
            ),
            ("module", SemanticJson::String(self.module.clone())),
            ("kind", SemanticJson::String(self.kind.as_str().to_owned())),
            (
                "label",
                self.label.as_ref().map_or(SemanticJson::Null, |value| {
                    SemanticJson::String(value.clone())
                }),
            ),
            ("source", SemanticJson::String(self.source.clone())),
            ("location", self.location.to_json()),
            ("body", self.body.to_json()),
            (
                "requires",
                self.requires
                    .as_ref()
                    .map_or(SemanticJson::Null, Term::to_json),
            ),
            (
                "ensures",
                self.ensures
                    .as_ref()
                    .map_or(SemanticJson::Null, Term::to_json),
            ),
            (
                "attributes",
                SemanticJson::Array(self.attributes.iter().map(Attribute::to_json).collect()),
            ),
        ])
    }
}

/// Human and generated provenance with separate identity fields.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Provenance {
    /// Stable sentence lineage.
    pub lineage_id: Digest,
    /// Complete content fingerprint.
    pub content_fingerprint: Digest,
    /// Body/conditions fingerprint.
    pub body_fingerprint: Digest,
    /// Logical module.
    pub module: String,
    /// Optional, non-unique label.
    pub label: Option<String>,
    /// Semantic sentence kind.
    pub kind: SentenceKind,
    /// Logical source.
    pub source: String,
    /// Source range.
    pub location: Location,
    /// Generated status, orthogonal to kind.
    pub generated: bool,
    /// Ordered transformation chain.
    pub transformation_chain: Vec<Digest>,
}

impl Provenance {
    fn from_json(value: &SemanticJson) -> Result<Self, IdentityError> {
        let fields = exact_object(
            value,
            &[
                "lineageId",
                "contentFingerprint",
                "bodyFingerprint",
                "module",
                "label",
                "kind",
                "source",
                "location",
                "generated",
                "transformationChain",
            ],
            "provenance",
        )?;
        let label = match fields.get("label") {
            Some(SemanticJson::Null) => None,
            Some(SemanticJson::String(value)) => Some(value.clone()),
            _ => return Err(malformed("provenance label must be string or null")),
        };
        let chain = fields
            .get("transformationChain")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| malformed("transformationChain must be an array"))?;
        Ok(Self {
            lineage_id: parse_digest(fields.get("lineageId"), "lineageId")?,
            content_fingerprint: parse_digest(
                fields.get("contentFingerprint"),
                "contentFingerprint",
            )?,
            body_fingerprint: parse_digest(fields.get("bodyFingerprint"), "bodyFingerprint")?,
            module: nonempty_string(fields.get("module"), "provenance module")?,
            label,
            kind: SentenceKind::parse(
                fields
                    .get("kind")
                    .and_then(SemanticJson::as_str)
                    .ok_or_else(|| malformed("provenance kind must be a string"))?,
            )?,
            source: nonempty_string(fields.get("source"), "provenance source")?,
            location: Location::from_json(
                fields
                    .get("location")
                    .ok_or_else(|| malformed("provenance lacks location"))?,
            )?,
            generated: fields
                .get("generated")
                .and_then(SemanticJson::as_bool)
                .ok_or_else(|| malformed("generated must be boolean"))?,
            transformation_chain: chain
                .iter()
                .map(|item| parse_digest(Some(item), "transformationChain item"))
                .collect::<Result<_, _>>()?,
        })
    }

    /// Returns the exact provenance value.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        object([
            (
                "lineageId",
                SemanticJson::String(self.lineage_id.to_string()),
            ),
            (
                "contentFingerprint",
                SemanticJson::String(self.content_fingerprint.to_string()),
            ),
            (
                "bodyFingerprint",
                SemanticJson::String(self.body_fingerprint.to_string()),
            ),
            ("module", SemanticJson::String(self.module.clone())),
            (
                "label",
                self.label.as_ref().map_or(SemanticJson::Null, |value| {
                    SemanticJson::String(value.clone())
                }),
            ),
            ("kind", SemanticJson::String(self.kind.as_str().to_owned())),
            ("source", SemanticJson::String(self.source.clone())),
            ("location", self.location.to_json()),
            ("generated", SemanticJson::Bool(self.generated)),
            (
                "transformationChain",
                SemanticJson::Array(
                    self.transformation_chain
                        .iter()
                        .map(|value| SemanticJson::String(value.to_string()))
                        .collect(),
                ),
            ),
        ])
    }
}

/// Closed generated lineage roles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GeneratedRole {
    /// Derived claim.
    DerivedClaim,
    /// Derived rule.
    DerivedRule,
    /// Sentence-relative insertion after an anchor.
    InsertAfterLineage,
    /// Sentence-relative insertion before an anchor.
    InsertBeforeLineage,
    /// Parentless module-end insertion.
    InsertModuleEnd,
    /// Parentless module-start insertion.
    InsertModuleStart,
    /// Observation update.
    ObservationUpdate,
}

impl GeneratedRole {
    fn parse(value: &str) -> Result<Self, IdentityError> {
        match value {
            "derived-claim" => Ok(Self::DerivedClaim),
            "derived-rule" => Ok(Self::DerivedRule),
            "insert-after-lineage" => Ok(Self::InsertAfterLineage),
            "insert-before-lineage" => Ok(Self::InsertBeforeLineage),
            "insert-module-end" => Ok(Self::InsertModuleEnd),
            "insert-module-start" => Ok(Self::InsertModuleStart),
            "observation-update" => Ok(Self::ObservationUpdate),
            _ => Err(IdentityError::new(
                IdentityErrorKind::UnsupportedForm,
                format!("unsupported generated role {value}"),
            )),
        }
    }

    fn is_module_role(self) -> bool {
        matches!(self, Self::InsertModuleEnd | Self::InsertModuleStart)
    }

    fn is_sentence_insertion(self) -> bool {
        matches!(self, Self::InsertAfterLineage | Self::InsertBeforeLineage)
    }

    /// Returns the frozen spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DerivedClaim => "derived-claim",
            Self::DerivedRule => "derived-rule",
            Self::InsertAfterLineage => "insert-after-lineage",
            Self::InsertBeforeLineage => "insert-before-lineage",
            Self::InsertModuleEnd => "insert-module-end",
            Self::InsertModuleStart => "insert-module-start",
            Self::ObservationUpdate => "observation-update",
        }
    }
}

/// Generated lineage identity payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedIdentity {
    /// Generating transformation.
    pub transformation_id: Digest,
    /// Canonically sorted unique parents.
    pub parent_lineages: Vec<Digest>,
    /// Destination anchor identity.
    pub anchor_identity: Digest,
    /// Closed generated role.
    pub role: GeneratedRole,
    /// Deterministic ordinal.
    pub ordinal: u64,
}

impl GeneratedIdentity {
    fn from_json(value: &SemanticJson) -> Result<Self, IdentityError> {
        let fields = exact_object(
            value,
            &[
                "transformationId",
                "parentLineages",
                "anchorIdentity",
                "role",
                "ordinal",
            ],
            "generated identity",
        )?;
        let parent_values = fields
            .get("parentLineages")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| malformed("parentLineages must be an array"))?;
        let parent_lineages: Vec<Digest> = parent_values
            .iter()
            .map(|value| parse_digest(Some(value), "parentLineages item"))
            .collect::<Result<_, _>>()?;
        if parent_lineages.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(IdentityError::new(
                IdentityErrorKind::NonCanonicalSet,
                "generated parents are not strictly sorted and unique",
            ));
        }
        let role = GeneratedRole::parse(
            fields
                .get("role")
                .and_then(SemanticJson::as_str)
                .ok_or_else(|| malformed("generated role must be a string"))?,
        )?;
        if role.is_module_role() != parent_lineages.is_empty() {
            return Err(IdentityError::new(
                IdentityErrorKind::IllFormed,
                "only module-start/end roles are parentless",
            ));
        }
        Ok(Self {
            transformation_id: parse_digest(fields.get("transformationId"), "transformationId")?,
            parent_lineages,
            anchor_identity: parse_digest(fields.get("anchorIdentity"), "anchorIdentity")?,
            role,
            ordinal: parse_u64(fields.get("ordinal"), "generated ordinal")?,
        })
    }

    /// Returns the exact generated identity payload.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        object([
            (
                "transformationId",
                SemanticJson::String(self.transformation_id.to_string()),
            ),
            (
                "parentLineages",
                SemanticJson::Array(
                    self.parent_lineages
                        .iter()
                        .map(|value| SemanticJson::String(value.to_string()))
                        .collect(),
                ),
            ),
            (
                "anchorIdentity",
                SemanticJson::String(self.anchor_identity.to_string()),
            ),
            ("role", SemanticJson::String(self.role.as_str().to_owned())),
            ("ordinal", ordinal(self.ordinal)),
        ])
    }
}

/// One source or generated semantic sentence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sentence {
    /// Source occurrence ordinal; null for generated sentences.
    pub source_occurrence_ordinal: Option<u64>,
    /// Generated identity; null for source sentences.
    pub generated_identity: Option<GeneratedIdentity>,
    /// Derived provenance identities.
    pub provenance: Provenance,
    /// Portable sentence value.
    pub value: SentenceValue,
}

/// Ordered module in a portable definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    /// Module name.
    pub name: String,
    /// Contiguous definition ordinal.
    pub ordinal: u64,
    /// Derived module fingerprint.
    pub fingerprint: Digest,
    /// Ordered unique imports.
    pub imports: Vec<String>,
    /// Ordered sentences.
    pub sentences: Vec<Sentence>,
}

/// Complete frozen portable-mutation-semantic-slice-v1 definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortableDefinition {
    /// Family payload.
    pub family: BaselineFamily,
    /// Derived family identity.
    pub baseline_family_id: Digest,
    /// Derived definition identity.
    pub definition_digest: Digest,
    /// Ordered modules.
    pub modules: Vec<Module>,
}

impl PortableDefinition {
    /// Parses and validates one complete portable definition fixture.
    pub fn from_json(value: &SemanticJson) -> Result<Self, IdentityError> {
        let fields = exact_object(
            value,
            &[
                "schemaVersion",
                "representation",
                "family",
                "baselineFamilyId",
                "definitionDigest",
                "modules",
            ],
            "portable definition",
        )?;
        if fields.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1) {
            return Err(IdentityError::new(
                IdentityErrorKind::UnsupportedForm,
                "unsupported definition schemaVersion",
            ));
        }
        if fields.get("representation").and_then(SemanticJson::as_str)
            != Some("portable-mutation-semantic-slice-v1")
        {
            return Err(IdentityError::new(
                IdentityErrorKind::UnsupportedForm,
                "unsupported definition representation",
            ));
        }
        let family = BaselineFamily::from_json(
            fields
                .get("family")
                .ok_or_else(|| malformed("definition lacks family"))?,
        )?;
        let derived_family_id = baseline_family_id(&family)?;
        let supplied_family_id = parse_digest(fields.get("baselineFamilyId"), "baselineFamilyId")?;
        if derived_family_id != supplied_family_id {
            return Err(IdentityError::new(
                IdentityErrorKind::DigestMismatch,
                "baselineFamilyId does not match family payload",
            ));
        }
        let module_values = fields
            .get("modules")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| malformed("definition modules must be an array"))?;
        if module_values.is_empty() {
            return Err(malformed("definition must contain a module"));
        }
        let mut modules = Vec::with_capacity(module_values.len());
        let mut signatures = BTreeMap::new();
        for (expected_ordinal, module_value) in module_values.iter().enumerate() {
            modules.push(parse_module(
                module_value,
                u64::try_from(expected_ordinal).expect("usize fits u64"),
                &supplied_family_id,
                &mut signatures,
            )?);
        }
        let names: BTreeSet<&str> = modules.iter().map(|module| module.name.as_str()).collect();
        if names.len() != modules.len() {
            return Err(IdentityError::new(
                IdentityErrorKind::IllFormed,
                "definition repeats a module name",
            ));
        }
        for module in &modules {
            if module
                .imports
                .iter()
                .any(|import| !names.contains(import.as_str()))
            {
                return Err(IdentityError::new(
                    IdentityErrorKind::IllFormed,
                    format!("module {} has an unresolved import", module.name),
                ));
            }
        }
        validate_generated_graph(&modules)?;
        let summary = definition_summary(&supplied_family_id, &modules);
        let derived_definition = identity_digest(
            "k-in-k/definition/v1",
            &summary.identity_payload(),
            "definition summary",
        )?;
        let supplied_definition = parse_digest(fields.get("definitionDigest"), "definitionDigest")?;
        if derived_definition != supplied_definition {
            return Err(IdentityError::new(
                IdentityErrorKind::DigestMismatch,
                "definitionDigest does not match definition summary",
            ));
        }
        Ok(Self {
            family,
            baseline_family_id: supplied_family_id,
            definition_digest: supplied_definition,
            modules,
        })
    }

    /// Returns the exact definition identity projection.
    #[must_use]
    pub fn identity_summary(&self) -> DefinitionIdentitySummary {
        definition_summary(&self.baseline_family_id, &self.modules)
    }
}

fn parse_module(
    value: &SemanticJson,
    expected_ordinal: u64,
    family_id: &Digest,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
) -> Result<Module, IdentityError> {
    let fields = exact_object(
        value,
        &["name", "ordinal", "fingerprint", "imports", "sentences"],
        "module",
    )?;
    let name = nonempty_string(fields.get("name"), "module name")?;
    let module_ordinal = parse_u64(fields.get("ordinal"), "module ordinal")?;
    if module_ordinal != expected_ordinal {
        return Err(IdentityError::new(
            IdentityErrorKind::IllFormed,
            "module ordinals are not contiguous",
        ));
    }
    let import_values = fields
        .get("imports")
        .and_then(SemanticJson::as_array)
        .ok_or_else(|| malformed("module imports must be an array"))?;
    let imports: Vec<String> = import_values
        .iter()
        .map(|item| nonempty_string(Some(item), "import"))
        .collect::<Result<_, _>>()?;
    if imports.iter().collect::<BTreeSet<_>>().len() != imports.len() {
        return Err(IdentityError::new(
            IdentityErrorKind::NonCanonicalSet,
            "module repeats an import",
        ));
    }
    let sentence_values = fields
        .get("sentences")
        .and_then(SemanticJson::as_array)
        .ok_or_else(|| malformed("module sentences must be an array"))?;
    let mut sentences = Vec::with_capacity(sentence_values.len());
    for sentence in sentence_values {
        sentences.push(parse_sentence(sentence, &name, family_id, signatures)?);
    }
    let module_payload = module_payload(&name, module_ordinal, &imports, &sentences);
    let derived_fingerprint =
        identity_digest("k-in-k/module/v1", &module_payload, "module summary")?;
    let supplied_fingerprint = parse_digest(fields.get("fingerprint"), "module fingerprint")?;
    if derived_fingerprint != supplied_fingerprint {
        return Err(IdentityError::new(
            IdentityErrorKind::DigestMismatch,
            format!("module {name} fingerprint mismatch"),
        ));
    }
    Ok(Module {
        name,
        ordinal: module_ordinal,
        fingerprint: supplied_fingerprint,
        imports,
        sentences,
    })
}

fn parse_sentence(
    value: &SemanticJson,
    module: &str,
    family_id: &Digest,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
) -> Result<Sentence, IdentityError> {
    let fields = exact_object(
        value,
        &[
            "sourceOccurrenceOrdinal",
            "generatedIdentity",
            "provenance",
            "value",
        ],
        "sentence",
    )?;
    let sentence_value = SentenceValue::from_json(
        fields
            .get("value")
            .ok_or_else(|| malformed("sentence lacks value"))?,
        signatures,
    )?;
    let provenance = Provenance::from_json(
        fields
            .get("provenance")
            .ok_or_else(|| malformed("sentence lacks provenance"))?,
    )?;
    if sentence_value.module != module
        || provenance.module != module
        || provenance.label != sentence_value.label
        || provenance.kind != sentence_value.kind
        || provenance.source != sentence_value.source
        || provenance.location != sentence_value.location
    {
        return Err(IdentityError::new(
            IdentityErrorKind::IllFormed,
            "sentence value and provenance disagree",
        ));
    }
    let source_occurrence_ordinal = match fields.get("sourceOccurrenceOrdinal") {
        Some(SemanticJson::Null) => None,
        Some(value) => Some(parse_u64(Some(value), "sourceOccurrenceOrdinal")?),
        None => return Err(malformed("sentence lacks sourceOccurrenceOrdinal")),
    };
    let generated_identity = match fields.get("generatedIdentity") {
        Some(SemanticJson::Null) => None,
        Some(value) => Some(GeneratedIdentity::from_json(value)?),
        None => return Err(malformed("sentence lacks generatedIdentity")),
    };
    let lineage_id = match (
        &generated_identity,
        source_occurrence_ordinal,
        provenance.generated,
    ) {
        (None, Some(ordinal), false) => input_lineage_id(
            family_id,
            module,
            &sentence_value.source,
            &sentence_value.location,
            sentence_value.kind,
            ordinal,
        )?,
        (Some(identity), None, true) => {
            if provenance.transformation_chain.last() != Some(&identity.transformation_id) {
                return Err(IdentityError::new(
                    IdentityErrorKind::IllFormed,
                    "generated transformation chain does not end in its transformation",
                ));
            }
            generated_lineage_id(identity)?
        }
        _ => {
            return Err(IdentityError::new(
                IdentityErrorKind::IllFormed,
                "source/generated identity fields are inconsistent",
            ));
        }
    };
    if lineage_id != provenance.lineage_id {
        return Err(IdentityError::new(
            IdentityErrorKind::DigestMismatch,
            "sentence lineageId mismatch",
        ));
    }
    let body_payload = object([
        ("body", sentence_value.body.to_json()),
        (
            "requires",
            sentence_value
                .requires
                .as_ref()
                .map_or(SemanticJson::Null, Term::to_json),
        ),
        (
            "ensures",
            sentence_value
                .ensures
                .as_ref()
                .map_or(SemanticJson::Null, Term::to_json),
        ),
    ]);
    let body_fingerprint =
        identity_digest("k-in-k/sentence-body/v1", &body_payload, "sentence body")?;
    if body_fingerprint != provenance.body_fingerprint {
        return Err(IdentityError::new(
            IdentityErrorKind::DigestMismatch,
            "sentence bodyFingerprint mismatch",
        ));
    }
    let content_payload = object([
        ("lineageId", SemanticJson::String(lineage_id.to_string())),
        ("module", SemanticJson::String(module.to_owned())),
        (
            "label",
            sentence_value
                .label
                .as_ref()
                .map_or(SemanticJson::Null, |value| {
                    SemanticJson::String(value.clone())
                }),
        ),
        (
            "kind",
            SemanticJson::String(sentence_value.kind.as_str().to_owned()),
        ),
        (
            "source",
            SemanticJson::String(sentence_value.source.clone()),
        ),
        ("location", sentence_value.location.to_json()),
        ("generated", SemanticJson::Bool(provenance.generated)),
        (
            "bodyFingerprint",
            SemanticJson::String(body_fingerprint.to_string()),
        ),
        (
            "attributes",
            SemanticJson::Array(
                sentence_value
                    .attributes
                    .iter()
                    .map(Attribute::to_json)
                    .collect(),
            ),
        ),
        (
            "transformationChain",
            SemanticJson::Array(
                provenance
                    .transformation_chain
                    .iter()
                    .map(|value| SemanticJson::String(value.to_string()))
                    .collect(),
            ),
        ),
    ]);
    let content_fingerprint = identity_digest(
        "k-in-k/sentence-content/v1",
        &content_payload,
        "sentence content",
    )?;
    if content_fingerprint != provenance.content_fingerprint {
        return Err(IdentityError::new(
            IdentityErrorKind::DigestMismatch,
            "sentence contentFingerprint mismatch",
        ));
    }
    Ok(Sentence {
        source_occurrence_ordinal,
        generated_identity,
        provenance,
        value: sentence_value,
    })
}

fn validate_generated_graph(modules: &[Module]) -> Result<(), IdentityError> {
    let lineages: BTreeSet<&Digest> = modules
        .iter()
        .flat_map(|module| module.sentences.iter())
        .map(|sentence| &sentence.provenance.lineage_id)
        .collect();
    for identity in modules
        .iter()
        .flat_map(|module| module.sentences.iter())
        .filter_map(|sentence| sentence.generated_identity.as_ref())
    {
        if identity.role.is_module_role() {
            // Destination module anchors require the reviewed transformation
            // input definition and remain a later native/patch-boundary proof.
            continue;
        }
        if identity
            .parent_lineages
            .iter()
            .any(|parent| !lineages.contains(parent))
            || !lineages.contains(&identity.anchor_identity)
            || (identity.role.is_sentence_insertion()
                && !identity.parent_lineages.contains(&identity.anchor_identity))
        {
            return Err(IdentityError::new(
                IdentityErrorKind::IllFormed,
                "generated identity has a dangling or invalid destination anchor",
            ));
        }
    }
    Ok(())
}

fn definition_summary(family_id: &Digest, modules: &[Module]) -> DefinitionIdentitySummary {
    DefinitionIdentitySummary {
        baseline_family_id: family_id.clone(),
        modules: modules
            .iter()
            .map(|module| DefinitionIdentityModule {
                name: module.name.clone(),
                ordinal: module.ordinal,
                imports: module.imports.clone(),
                sentence_content_fingerprints: module
                    .sentences
                    .iter()
                    .map(|sentence| sentence.provenance.content_fingerprint.clone())
                    .collect(),
            })
            .collect(),
    }
}

fn module_payload(
    name: &str,
    module_ordinal: u64,
    imports: &[String],
    sentences: &[Sentence],
) -> SemanticJson {
    object([
        ("name", SemanticJson::String(name.to_owned())),
        ("ordinal", ordinal(module_ordinal)),
        (
            "imports",
            SemanticJson::Array(imports.iter().cloned().map(SemanticJson::String).collect()),
        ),
        (
            "sentenceContentFingerprints",
            SemanticJson::Array(
                sentences
                    .iter()
                    .map(|sentence| {
                        SemanticJson::String(sentence.provenance.content_fingerprint.to_string())
                    })
                    .collect(),
            ),
        ),
    ])
}

fn optional_term(
    value: Option<&SemanticJson>,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
    variables: &mut BTreeMap<String, String>,
) -> Result<Option<Term>, IdentityError> {
    match value {
        Some(SemanticJson::Null) => Ok(None),
        Some(value) => Term::from_json(value, signatures, variables).map(Some),
        None => Err(malformed("missing optional term field")),
    }
}

fn validate_logical_source(source: &str) -> Result<(), IdentityError> {
    match source.split_once("://") {
        Some(("repo" | "corpus" | "generated", tail))
            if !tail.is_empty() && !tail.starts_with('/') =>
        {
            Ok(())
        }
        _ => Err(IdentityError::new(
            IdentityErrorKind::IllFormed,
            "source is not a portable logical URI",
        )),
    }
}

fn ordinal(value: u64) -> SemanticJson {
    SemanticJson::Integer(i64::try_from(value).expect("v1 ordinal fits i64"))
}

fn identity_digest(
    domain_name: &str,
    value: &SemanticJson,
    context: &str,
) -> Result<Digest, IdentityError> {
    digest(&domain(domain_name), value).map_err(|error| {
        IdentityError::new(
            IdentityErrorKind::MalformedValue,
            format!("{context} is not valid semantic JSON: {error}"),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_json;
    use std::fs;
    use std::path::Path;

    /// Reads a definition fixture from `tests/data`.
    fn fixture(name: &str) -> SemanticJson {
        let data = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
        parse_json(&fs::read(data.join(name)).expect("fixture is present"))
            .expect("fixture is restricted JSON")
    }

    #[test]
    fn validates_memory_counter_and_generated_definition_identities() {
        for name in [
            "semantic-definition-memory.json",
            "semantic-definition-counter.json",
            "semantic-definition-generated.json",
        ] {
            PortableDefinition::from_json(&fixture(name))
                .unwrap_or_else(|failure| panic!("{name}: {failure}"));
        }
    }

    #[test]
    fn rejects_unsupported_term_and_sentence_forms_explicitly() {
        let mut definition = fixture("semantic-definition-memory.json");
        let SemanticJson::Object(root) = &mut definition else {
            panic!("fixture shape");
        };
        let SemanticJson::Array(modules) = root.get_mut("modules").expect("modules") else {
            panic!("fixture shape");
        };
        let SemanticJson::Object(module) = &mut modules[0] else {
            panic!("fixture shape");
        };
        let SemanticJson::Array(sentences) = module.get_mut("sentences").expect("sentences") else {
            panic!("fixture shape");
        };
        let SemanticJson::Object(sentence) = &mut sentences[0] else {
            panic!("fixture shape");
        };
        let SemanticJson::Object(value) = sentence.get_mut("value").expect("value") else {
            panic!("fixture shape");
        };
        value.insert(
            "kind".to_owned(),
            SemanticJson::String("generated-rule".to_owned()),
        );
        assert_eq!(
            PortableDefinition::from_json(&definition)
                .expect_err("open sentence kind must reject")
                .kind(),
            IdentityErrorKind::UnsupportedForm
        );
    }
}
