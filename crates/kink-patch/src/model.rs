use kink_portable::{
    Digest, DigestDomain, SemanticJson, canonical_json as checked_canonical_json,
    digest as checked_digest,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Closed patch-model failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatchModelErrorKind {
    /// The JSON shape is outside the frozen v1 model.
    MalformedPatch,
    /// The operation or position is outside the closed v1 algebra.
    UnsupportedOperation,
    /// A supplied edit or patch identity is not its derived identity.
    DigestMismatch,
    /// Edits were not supplied in their canonical order.
    NonCanonicalOrder,
}

/// Typed patch-model failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatchModelError {
    kind: PatchModelErrorKind,
    detail: String,
}

impl PatchModelError {
    fn new(kind: PatchModelErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the decision-bearing failure classification.
    #[must_use]
    pub const fn kind(&self) -> PatchModelErrorKind {
        self.kind
    }
}

impl fmt::Display for PatchModelError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for PatchModelError {}

/// Closed original-relative path step.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PathStep {
    /// A named semantic field.
    Field(String),
    /// An application argument in original coordinates.
    Argument(u64),
    /// A sequence item in original coordinates.
    SequenceItem(u64),
    /// The term below an explicit injection.
    InjectionTerm,
    /// An attribute selected by its unique name.
    Attribute(String),
}

impl PathStep {
    fn from_json(value: &SemanticJson) -> Result<Self, PatchModelError> {
        let fields = object(value, "path step")?;
        let kind = string(fields.get("kind"), "path step kind")?;
        match kind {
            "field" => {
                exact(fields, &["kind", "name"], "field path step")?;
                let name = string(fields.get("name"), "field name")?;
                if !matches!(
                    name,
                    "sentence" | "body" | "lhs" | "rhs" | "requires" | "ensures" | "attributes"
                ) {
                    return Err(malformed("unsupported named semantic field"));
                }
                Ok(Self::Field(name.to_owned()))
            }
            "argument" => {
                exact(fields, &["kind", "index"], "argument path step")?;
                Ok(Self::Argument(nonnegative(
                    fields.get("index"),
                    "argument index",
                )?))
            }
            "sequence-item" => {
                exact(fields, &["kind", "index"], "sequence path step")?;
                Ok(Self::SequenceItem(nonnegative(
                    fields.get("index"),
                    "sequence index",
                )?))
            }
            "injection-term" => {
                exact(fields, &["kind"], "injection path step")?;
                Ok(Self::InjectionTerm)
            }
            "attribute" => {
                exact(fields, &["kind", "name"], "attribute path step")?;
                let name = nonempty(fields.get("name"), "attribute name")?;
                Ok(Self::Attribute(name))
            }
            _ => Err(malformed("unsupported typed path step")),
        }
    }

    /// Returns the exact frozen JSON representation.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        match self {
            Self::Field(name) => json_object([
                ("kind", SemanticJson::String("field".to_owned())),
                ("name", SemanticJson::String(name.clone())),
            ]),
            Self::Argument(index) => json_object([
                ("kind", SemanticJson::String("argument".to_owned())),
                ("index", integer(*index)),
            ]),
            Self::SequenceItem(index) => json_object([
                ("kind", SemanticJson::String("sequence-item".to_owned())),
                ("index", integer(*index)),
            ]),
            Self::InjectionTerm => {
                json_object([("kind", SemanticJson::String("injection-term".to_owned()))])
            }
            Self::Attribute(name) => json_object([
                ("kind", SemanticJson::String("attribute".to_owned())),
                ("name", SemanticJson::String(name.clone())),
            ]),
        }
    }
}

/// A closed typed original-relative path.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct TypedPath(pub Vec<PathStep>);

impl TypedPath {
    fn from_json(value: &SemanticJson) -> Result<Self, PatchModelError> {
        let values = value
            .as_array()
            .ok_or_else(|| malformed("targetPath must be an array"))?;
        Ok(Self(
            values
                .iter()
                .map(PathStep::from_json)
                .collect::<Result<_, _>>()?,
        ))
    }

    /// Returns whether this path is a prefix of `other`.
    #[must_use]
    pub fn is_prefix_of(&self, other: &Self) -> bool {
        self.0.len() <= other.0.len() && self.0 == other.0[..self.0.len()]
    }

    /// Returns the exact frozen JSON representation.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        SemanticJson::Array(self.0.iter().map(PathStep::to_json).collect())
    }
}

/// Closed portable patch operation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Operation {
    /// Replace one typed term region.
    ReplaceTerm,
    /// Replace a complete sentence while preserving its lineage anchor.
    ReplaceSentence,
    /// Delete a complete sentence.
    DeleteSentence,
    /// Insert a generated sentence at an explicit position.
    InsertSentence,
    /// Replace `requires` or `ensures` with a Bool term.
    ReplaceCondition,
    /// Add a previously absent attribute.
    AddAttribute,
    /// Remove a fingerprinted attribute.
    RemoveAttribute,
    /// Replace a fingerprinted attribute.
    ReplaceAttribute,
}

impl Operation {
    fn parse(value: &str) -> Result<Self, PatchModelError> {
        match value {
            "replace-term" => Ok(Self::ReplaceTerm),
            "replace-sentence" => Ok(Self::ReplaceSentence),
            "delete-sentence" => Ok(Self::DeleteSentence),
            "insert-sentence" => Ok(Self::InsertSentence),
            "replace-condition" => Ok(Self::ReplaceCondition),
            "add-attribute" => Ok(Self::AddAttribute),
            "remove-attribute" => Ok(Self::RemoveAttribute),
            "replace-attribute" => Ok(Self::ReplaceAttribute),
            _ => Err(PatchModelError::new(
                PatchModelErrorKind::UnsupportedOperation,
                "unsupported patch operation",
            )),
        }
    }

    /// Returns the frozen spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReplaceTerm => "replace-term",
            Self::ReplaceSentence => "replace-sentence",
            Self::DeleteSentence => "delete-sentence",
            Self::InsertSentence => "insert-sentence",
            Self::ReplaceCondition => "replace-condition",
            Self::AddAttribute => "add-attribute",
            Self::RemoveAttribute => "remove-attribute",
            Self::ReplaceAttribute => "replace-attribute",
        }
    }
}

/// Closed deterministic insertion-position kind.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum InsertPositionKind {
    /// Immediately before a sentence lineage.
    BeforeLineage,
    /// Immediately after a sentence lineage.
    AfterLineage,
    /// At the start of one named module.
    ModuleStart,
    /// At the end of one named module.
    ModuleEnd,
}

impl InsertPositionKind {
    fn parse(value: &str) -> Result<Self, PatchModelError> {
        match value {
            "before-lineage" => Ok(Self::BeforeLineage),
            "after-lineage" => Ok(Self::AfterLineage),
            "module-start" => Ok(Self::ModuleStart),
            "module-end" => Ok(Self::ModuleEnd),
            _ => Err(PatchModelError::new(
                PatchModelErrorKind::UnsupportedOperation,
                "unsupported insertion position",
            )),
        }
    }

    /// Returns the frozen spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BeforeLineage => "before-lineage",
            Self::AfterLineage => "after-lineage",
            Self::ModuleStart => "module-start",
            Self::ModuleEnd => "module-end",
        }
    }

    /// Returns the generated-lineage role.
    #[must_use]
    pub const fn generated_role(self) -> &'static str {
        match self {
            Self::BeforeLineage => "insert-before-lineage",
            Self::AfterLineage => "insert-after-lineage",
            Self::ModuleStart => "insert-module-start",
            Self::ModuleEnd => "insert-module-end",
        }
    }
}

/// One explicit deterministic insertion position.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InsertPosition {
    /// Closed position kind.
    pub kind: InsertPositionKind,
    /// Sentence-relative anchor for before/after positions.
    pub anchor_lineage: Option<Digest>,
    /// Destination module for module-start/end positions.
    pub module: Option<String>,
    /// Ordering ordinal among insertions at the same anchor and side.
    pub ordinal: u64,
}

impl InsertPosition {
    fn from_json(value: &SemanticJson) -> Result<Self, PatchModelError> {
        let fields = object(value, "position")?;
        let kind = InsertPositionKind::parse(string(fields.get("kind"), "position kind")?)?;
        match kind {
            InsertPositionKind::BeforeLineage | InsertPositionKind::AfterLineage => {
                exact(fields, &["kind", "anchorLineage", "ordinal"], "position")?;
                Ok(Self {
                    kind,
                    anchor_lineage: Some(parse_digest(
                        fields.get("anchorLineage"),
                        "anchorLineage",
                    )?),
                    module: None,
                    ordinal: nonnegative(fields.get("ordinal"), "insertion ordinal")?,
                })
            }
            InsertPositionKind::ModuleStart | InsertPositionKind::ModuleEnd => {
                exact(fields, &["kind", "module", "ordinal"], "position")?;
                Ok(Self {
                    kind,
                    anchor_lineage: None,
                    module: Some(nonempty(fields.get("module"), "position module")?),
                    ordinal: nonnegative(fields.get("ordinal"), "insertion ordinal")?,
                })
            }
        }
    }

    /// Returns the exact frozen JSON representation.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        let mut fields = BTreeMap::from([
            (
                "kind".to_owned(),
                SemanticJson::String(self.kind.as_str().to_owned()),
            ),
            ("ordinal".to_owned(), integer(self.ordinal)),
        ]);
        if let Some(lineage) = &self.anchor_lineage {
            fields.insert(
                "anchorLineage".to_owned(),
                SemanticJson::String(lineage.to_string()),
            );
        }
        if let Some(module) = &self.module {
            fields.insert("module".to_owned(), SemanticJson::String(module.clone()));
        }
        SemanticJson::Object(fields)
    }
}

/// Closed tagged edit value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EditValue {
    /// A complete portable term.
    Term(SemanticJson),
    /// A complete portable semantic sentence value.
    Sentence(SemanticJson),
    /// A unique-name attribute.
    Attribute {
        /// Attribute name.
        name: String,
        /// Optional portable term value.
        value: Option<SemanticJson>,
    },
    /// A term selected from the immutable original definition.
    OriginalReference {
        /// Source sentence lineage.
        lineage: Digest,
        /// Source term path.
        path: TypedPath,
    },
    /// Explicit absence for delete/remove operations.
    None,
}

impl EditValue {
    fn from_json(value: &SemanticJson) -> Result<Self, PatchModelError> {
        let fields = object(value, "edit value")?;
        match string(fields.get("kind"), "edit value kind")? {
            "term" => {
                exact(fields, &["kind", "term"], "term edit value")?;
                Ok(Self::Term(
                    fields.get("term").expect("exact fields").clone(),
                ))
            }
            "sentence" => {
                exact(fields, &["kind", "sentence"], "sentence edit value")?;
                Ok(Self::Sentence(
                    fields.get("sentence").expect("exact fields").clone(),
                ))
            }
            "attribute" => {
                exact(fields, &["kind", "name", "value"], "attribute edit value")?;
                let value = match fields.get("value") {
                    Some(SemanticJson::Null) => None,
                    Some(value) => Some(value.clone()),
                    None => unreachable!("exact fields"),
                };
                Ok(Self::Attribute {
                    name: nonempty(fields.get("name"), "attribute value name")?,
                    value,
                })
            }
            "original-reference" => {
                exact(
                    fields,
                    &["kind", "fromOriginalLineage", "fromOriginalPath"],
                    "original reference",
                )?;
                Ok(Self::OriginalReference {
                    lineage: parse_digest(
                        fields.get("fromOriginalLineage"),
                        "fromOriginalLineage",
                    )?,
                    path: TypedPath::from_json(
                        fields.get("fromOriginalPath").expect("exact fields"),
                    )?,
                })
            }
            "none" => {
                exact(fields, &["kind"], "none edit value")?;
                Ok(Self::None)
            }
            _ => Err(malformed("unsupported edit value kind")),
        }
    }

    /// Returns the exact frozen JSON representation.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        match self {
            Self::Term(term) => json_object([
                ("kind", SemanticJson::String("term".to_owned())),
                ("term", term.clone()),
            ]),
            Self::Sentence(sentence) => json_object([
                ("kind", SemanticJson::String("sentence".to_owned())),
                ("sentence", sentence.clone()),
            ]),
            Self::Attribute { name, value } => json_object([
                ("kind", SemanticJson::String("attribute".to_owned())),
                ("name", SemanticJson::String(name.clone())),
                ("value", value.clone().unwrap_or(SemanticJson::Null)),
            ]),
            Self::OriginalReference { lineage, path } => json_object([
                (
                    "kind",
                    SemanticJson::String("original-reference".to_owned()),
                ),
                (
                    "fromOriginalLineage",
                    SemanticJson::String(lineage.to_string()),
                ),
                ("fromOriginalPath", path.to_json()),
            ]),
            Self::None => json_object([("kind", SemanticJson::String("none".to_owned()))]),
        }
    }
}

/// One fully materialized canonical edit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Edit {
    /// Derived edit identity.
    pub(crate) edit_id: Digest,
    /// Closed operation.
    pub(crate) operation: Operation,
    /// Target or sentence-anchor lineage.
    pub(crate) target_lineage: Option<Digest>,
    /// Expected immutable-baseline sentence content.
    pub(crate) expected_content: Option<Digest>,
    /// Expected old attribute fingerprint when the operation has one.
    pub(crate) expected_attribute_fingerprint: Option<Digest>,
    /// Expected immutable-baseline module fingerprint for module insertion.
    pub(crate) expected_module_fingerprint: Option<Digest>,
    /// Original-relative typed target path.
    pub(crate) target_path: TypedPath,
    /// Closed replacement value.
    pub(crate) value: EditValue,
    /// Explicit insertion position.
    pub(crate) position: Option<InsertPosition>,
}

impl Edit {
    /// Returns the derived edit identity.
    #[must_use]
    pub fn edit_id(&self) -> &Digest {
        &self.edit_id
    }

    /// Returns the closed operation.
    #[must_use]
    pub const fn operation(&self) -> Operation {
        self.operation
    }

    /// Returns the target lineage when the operation has one.
    #[must_use]
    pub fn target_lineage(&self) -> Option<&Digest> {
        self.target_lineage.as_ref()
    }

    /// Returns the original-relative target path.
    #[must_use]
    pub const fn target_path(&self) -> &TypedPath {
        &self.target_path
    }

    /// Returns the closed edit value.
    #[must_use]
    pub const fn value(&self) -> &EditValue {
        &self.value
    }

    /// Returns the deterministic insertion position when present.
    #[must_use]
    pub const fn position(&self) -> Option<&InsertPosition> {
        self.position.as_ref()
    }

    fn from_json(value: &SemanticJson) -> Result<Self, PatchModelError> {
        let fields = object(value, "edit")?;
        let operation = Operation::parse(string(fields.get("operation"), "operation")?)?;
        let expected_fields: &[&str] = match operation {
            Operation::ReplaceTerm
            | Operation::ReplaceSentence
            | Operation::DeleteSentence
            | Operation::ReplaceCondition => &[
                "editId",
                "operation",
                "targetLineage",
                "expectedContent",
                "targetPath",
                "value",
            ],
            Operation::InsertSentence => {
                let position = fields
                    .get("position")
                    .ok_or_else(|| malformed("insertion lacks position"))?;
                let position = InsertPosition::from_json(position)?;
                match position.kind {
                    InsertPositionKind::BeforeLineage | InsertPositionKind::AfterLineage => &[
                        "editId",
                        "operation",
                        "targetLineage",
                        "expectedContent",
                        "targetPath",
                        "value",
                        "position",
                    ],
                    InsertPositionKind::ModuleStart | InsertPositionKind::ModuleEnd => &[
                        "editId",
                        "operation",
                        "targetLineage",
                        "expectedContent",
                        "expectedModuleFingerprint",
                        "targetPath",
                        "value",
                        "position",
                    ],
                }
            }
            Operation::AddAttribute | Operation::RemoveAttribute | Operation::ReplaceAttribute => {
                &[
                    "editId",
                    "operation",
                    "targetLineage",
                    "expectedContent",
                    "expectedAttributeFingerprint",
                    "targetPath",
                    "value",
                ]
            }
        };
        exact(fields, expected_fields, "edit")?;

        let edit = Self {
            edit_id: parse_digest(fields.get("editId"), "editId")?,
            operation,
            target_lineage: nullable_digest(fields.get("targetLineage"), "targetLineage")?,
            expected_content: nullable_digest(fields.get("expectedContent"), "expectedContent")?,
            expected_attribute_fingerprint: if matches!(
                operation,
                Operation::AddAttribute | Operation::RemoveAttribute | Operation::ReplaceAttribute
            ) {
                nullable_digest(
                    fields.get("expectedAttributeFingerprint"),
                    "expectedAttributeFingerprint",
                )?
            } else {
                None
            },
            expected_module_fingerprint: if fields.contains_key("expectedModuleFingerprint") {
                nullable_digest(
                    fields.get("expectedModuleFingerprint"),
                    "expectedModuleFingerprint",
                )?
            } else {
                None
            },
            target_path: TypedPath::from_json(
                fields
                    .get("targetPath")
                    .ok_or_else(|| malformed("missing targetPath"))?,
            )?,
            value: EditValue::from_json(
                fields
                    .get("value")
                    .ok_or_else(|| malformed("missing edit value"))?,
            )?,
            position: fields
                .get("position")
                .map(InsertPosition::from_json)
                .transpose()?,
        };
        edit.validate_operation_shape()?;
        if edit.edit_id != edit.derived_id() {
            return Err(PatchModelError::new(
                PatchModelErrorKind::DigestMismatch,
                "editId does not match the edit payload",
            ));
        }
        Ok(edit)
    }

    fn validate_operation_shape(&self) -> Result<(), PatchModelError> {
        let target_pair = self.target_lineage.is_some() && self.expected_content.is_some();
        let empty_path = self.target_path.0.is_empty();
        let valid = match self.operation {
            Operation::ReplaceTerm => {
                target_pair
                    && !empty_path
                    && matches!(
                        self.value,
                        EditValue::Term(_) | EditValue::OriginalReference { .. }
                    )
                    && self.position.is_none()
            }
            Operation::ReplaceSentence => {
                target_pair
                    && empty_path
                    && matches!(self.value, EditValue::Sentence(_))
                    && self.position.is_none()
            }
            Operation::DeleteSentence => {
                target_pair
                    && empty_path
                    && self.value == EditValue::None
                    && self.position.is_none()
            }
            Operation::InsertSentence => {
                empty_path
                    && matches!(self.value, EditValue::Sentence(_))
                    && self.position.is_some()
            }
            Operation::ReplaceCondition => {
                target_pair
                    && matches!(self.value, EditValue::Term(_))
                    && matches!(
                        self.target_path.0.as_slice(),
                        [PathStep::Field(name)] if name == "requires" || name == "ensures"
                    )
                    && self.position.is_none()
            }
            Operation::AddAttribute => {
                target_pair
                    && self.expected_attribute_fingerprint.is_none()
                    && matches!(self.value, EditValue::Attribute { .. })
                    && self.attribute_path()
                    && self.position.is_none()
            }
            Operation::RemoveAttribute => {
                target_pair
                    && self.expected_attribute_fingerprint.is_some()
                    && self.value == EditValue::None
                    && self.attribute_path()
                    && self.position.is_none()
            }
            Operation::ReplaceAttribute => {
                target_pair
                    && self.expected_attribute_fingerprint.is_some()
                    && matches!(self.value, EditValue::Attribute { .. })
                    && self.attribute_path()
                    && self.position.is_none()
            }
        };
        if !valid {
            return Err(malformed("operation preconditions have an invalid shape"));
        }
        if let Some(position) = &self.position {
            match position.kind {
                InsertPositionKind::BeforeLineage | InsertPositionKind::AfterLineage => {
                    if self.target_lineage.as_ref() != position.anchor_lineage.as_ref()
                        || self.expected_content.is_none()
                        || position.module.is_some()
                        || self.expected_module_fingerprint.is_some()
                    {
                        return Err(malformed("sentence-relative insertion has invalid anchors"));
                    }
                }
                InsertPositionKind::ModuleStart | InsertPositionKind::ModuleEnd => {
                    if self.target_lineage.is_some()
                        || self.expected_content.is_some()
                        || position.anchor_lineage.is_some()
                        || position.module.is_none()
                        || self.expected_module_fingerprint.is_none()
                    {
                        return Err(malformed("module insertion has invalid anchors"));
                    }
                }
            }
        }
        Ok(())
    }

    fn attribute_path(&self) -> bool {
        matches!(
            self.target_path.0.as_slice(),
            [PathStep::Field(field), PathStep::Attribute(_)] if field == "attributes"
        )
    }

    /// Derives the edit ID over the edit without `editId`.
    #[must_use]
    pub fn derived_id(&self) -> Digest {
        digest(&domain("k-in-k/edit/v1"), &self.payload_json())
    }

    fn payload_json(&self) -> SemanticJson {
        let mut fields = self.fields(false);
        fields.remove("editId");
        SemanticJson::Object(fields)
    }

    /// Returns the exact frozen JSON representation.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        SemanticJson::Object(self.fields(true))
    }

    fn fields(&self, include_id: bool) -> BTreeMap<String, SemanticJson> {
        let mut fields = BTreeMap::new();
        if include_id {
            fields.insert(
                "editId".to_owned(),
                SemanticJson::String(self.edit_id.to_string()),
            );
        }
        fields.insert(
            "operation".to_owned(),
            SemanticJson::String(self.operation.as_str().to_owned()),
        );
        fields.insert(
            "targetLineage".to_owned(),
            self.target_lineage
                .as_ref()
                .map_or(SemanticJson::Null, |value| {
                    SemanticJson::String(value.to_string())
                }),
        );
        fields.insert(
            "expectedContent".to_owned(),
            self.expected_content
                .as_ref()
                .map_or(SemanticJson::Null, |value| {
                    SemanticJson::String(value.to_string())
                }),
        );
        if matches!(
            self.operation,
            Operation::AddAttribute | Operation::RemoveAttribute | Operation::ReplaceAttribute
        ) {
            fields.insert(
                "expectedAttributeFingerprint".to_owned(),
                self.expected_attribute_fingerprint
                    .as_ref()
                    .map_or(SemanticJson::Null, |value| {
                        SemanticJson::String(value.to_string())
                    }),
            );
        }
        if self.expected_module_fingerprint.is_some() {
            fields.insert(
                "expectedModuleFingerprint".to_owned(),
                self.expected_module_fingerprint
                    .as_ref()
                    .map_or(SemanticJson::Null, |value| {
                        SemanticJson::String(value.to_string())
                    }),
            );
        }
        fields.insert("targetPath".to_owned(), self.target_path.to_json());
        fields.insert("value".to_owned(), self.value.to_json());
        if let Some(position) = &self.position {
            fields.insert("position".to_owned(), position.to_json());
        }
        fields
    }

    fn canonical_key(&self) -> (String, String, &'static str, String) {
        (
            self.target_lineage
                .as_ref()
                .map_or_else(String::new, ToString::to_string),
            canonical_json(&self.target_path.to_json()),
            self.operation.as_str(),
            self.edit_id.to_string(),
        )
    }
}

/// One canonical portable semantic patch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Patch {
    /// Derived patch identity.
    pub(crate) patch_id: Digest,
    /// Operator identity spelling.
    pub(crate) operator_id: String,
    /// Positive operator version.
    pub(crate) operator_version: u64,
    /// Canonically ordered nonempty edits.
    pub(crate) edits: Vec<Edit>,
}

impl Patch {
    /// Returns the derived patch identity.
    #[must_use]
    pub fn patch_id(&self) -> &Digest {
        &self.patch_id
    }

    /// Returns the operator identity spelling.
    #[must_use]
    pub fn operator_id(&self) -> &str {
        &self.operator_id
    }

    /// Returns the positive operator version.
    #[must_use]
    pub const fn operator_version(&self) -> u64 {
        self.operator_version
    }

    /// Returns the canonical edit sequence.
    #[must_use]
    pub fn edits(&self) -> &[Edit] {
        &self.edits
    }

    /// Parses and validates an exact canonical patch value.
    pub fn from_json(value: &SemanticJson) -> Result<Self, PatchModelError> {
        value.validate().map_err(|error| {
            PatchModelError::new(
                PatchModelErrorKind::MalformedPatch,
                format!("patch is not valid semantic JSON: {error}"),
            )
        })?;
        let fields = object(value, "patch")?;
        exact(
            fields,
            &[
                "schemaVersion",
                "patchId",
                "operatorId",
                "operatorVersion",
                "edits",
            ],
            "patch",
        )?;
        if fields.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1) {
            return Err(malformed("unsupported patch schemaVersion"));
        }
        let edit_values = fields
            .get("edits")
            .and_then(SemanticJson::as_array)
            .ok_or_else(|| malformed("patch edits must be an array"))?;
        if edit_values.is_empty() {
            return Err(malformed("patch edits must not be empty"));
        }
        let edits: Vec<Edit> = edit_values
            .iter()
            .map(Edit::from_json)
            .collect::<Result<_, _>>()?;
        if edits
            .windows(2)
            .any(|pair| pair[0].canonical_key() > pair[1].canonical_key())
        {
            return Err(PatchModelError::new(
                PatchModelErrorKind::NonCanonicalOrder,
                "patch edits are not in canonical order",
            ));
        }
        let patch = Self {
            patch_id: parse_digest(fields.get("patchId"), "patchId")?,
            operator_id: nonempty(fields.get("operatorId"), "operatorId")?,
            operator_version: positive(fields.get("operatorVersion"), "operatorVersion")?,
            edits,
        };
        if patch.patch_id != patch.derived_id() {
            return Err(PatchModelError::new(
                PatchModelErrorKind::DigestMismatch,
                "patchId does not match canonical edits",
            ));
        }
        Ok(patch)
    }

    /// Derives the patch ID from schema version and canonical edits.
    #[must_use]
    pub fn derived_id(&self) -> Digest {
        digest(&domain("k-in-k/patch/v1"), &self.identity_payload())
    }

    /// Returns the frozen patch identity payload.
    #[must_use]
    pub fn identity_payload(&self) -> SemanticJson {
        json_object([
            ("schemaVersion", SemanticJson::Integer(1)),
            (
                "edits",
                SemanticJson::Array(self.edits.iter().map(Edit::to_json).collect()),
            ),
        ])
    }

    /// Returns the exact frozen JSON representation.
    #[must_use]
    pub fn to_json(&self) -> SemanticJson {
        json_object([
            ("schemaVersion", SemanticJson::Integer(1)),
            ("patchId", SemanticJson::String(self.patch_id.to_string())),
            ("operatorId", SemanticJson::String(self.operator_id.clone())),
            ("operatorVersion", integer(self.operator_version)),
            (
                "edits",
                SemanticJson::Array(self.edits.iter().map(Edit::to_json).collect()),
            ),
        ])
    }
}

pub(crate) fn domain(value: &str) -> DigestDomain {
    DigestDomain::new(value).expect("frozen digest domain is valid")
}

pub(crate) fn json_object<const N: usize>(fields: [(&str, SemanticJson); N]) -> SemanticJson {
    SemanticJson::Object(
        fields
            .into_iter()
            .map(|(name, value)| (name.to_owned(), value))
            .collect(),
    )
}

fn digest(domain: &DigestDomain, value: &SemanticJson) -> Digest {
    checked_digest(domain, value).expect("validated patch model forms semantic JSON")
}

fn canonical_json(value: &SemanticJson) -> String {
    checked_canonical_json(value).expect("validated typed path forms semantic JSON")
}

fn object<'a>(
    value: &'a SemanticJson,
    context: &str,
) -> Result<&'a BTreeMap<String, SemanticJson>, PatchModelError> {
    value
        .as_object()
        .ok_or_else(|| malformed(format!("{context} must be an object")))
}

fn exact(
    fields: &BTreeMap<String, SemanticJson>,
    expected: &[&str],
    context: &str,
) -> Result<(), PatchModelError> {
    let actual: BTreeSet<&str> = fields.keys().map(String::as_str).collect();
    let expected: BTreeSet<&str> = expected.iter().copied().collect();
    if actual != expected {
        return Err(malformed(format!("{context} has unsupported fields")));
    }
    Ok(())
}

fn string<'a>(value: Option<&'a SemanticJson>, field: &str) -> Result<&'a str, PatchModelError> {
    value
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| malformed(format!("{field} must be a string")))
}

fn nonempty(value: Option<&SemanticJson>, field: &str) -> Result<String, PatchModelError> {
    let value = string(value, field)?;
    if value.is_empty() {
        return Err(malformed(format!("{field} must not be empty")));
    }
    Ok(value.to_owned())
}

fn parse_digest(value: Option<&SemanticJson>, field: &str) -> Result<Digest, PatchModelError> {
    Digest::parse(string(value, field)?)
        .map_err(|_| malformed(format!("{field} must be lowercase SHA-256")))
}

fn nullable_digest(
    value: Option<&SemanticJson>,
    field: &str,
) -> Result<Option<Digest>, PatchModelError> {
    match value {
        Some(SemanticJson::Null) => Ok(None),
        Some(value) => parse_digest(Some(value), field).map(Some),
        None => Err(malformed(format!("missing {field}"))),
    }
}

fn nonnegative(value: Option<&SemanticJson>, field: &str) -> Result<u64, PatchModelError> {
    value
        .and_then(SemanticJson::as_i64)
        .and_then(|value| u64::try_from(value).ok())
        .ok_or_else(|| malformed(format!("{field} must be nonnegative")))
}

fn positive(value: Option<&SemanticJson>, field: &str) -> Result<u64, PatchModelError> {
    let value = nonnegative(value, field)?;
    if value == 0 {
        return Err(malformed(format!("{field} must be positive")));
    }
    Ok(value)
}

fn integer(value: u64) -> SemanticJson {
    SemanticJson::Integer(i64::try_from(value).expect("v1 ordinal fits signed-64"))
}

fn malformed(detail: impl Into<String>) -> PatchModelError {
    PatchModelError::new(PatchModelErrorKind::MalformedPatch, detail)
}
