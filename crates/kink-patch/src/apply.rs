use crate::failure::{PatchFailure, PatchFailureKind};
use crate::model::{
    Edit, EditValue, InsertPositionKind, Operation, Patch, PathStep, TypedPath, domain, json_object,
};
use kink_portable::{
    Digest, DigestDomain, PortableDefinition, SemanticJson, digest as checked_digest,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Portable application result. This is intentionally weaker than native proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortableApplication {
    /// Every edit committed atomically and the portable output is locally valid.
    AppliedAndLocallyWellFormed,
}

impl PortableApplication {
    /// Returns the frozen result spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        "applied-and-locally-well-formed"
    }
}

/// Native IR validation state at the portable patch boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeIrValidation {
    /// Native lowering/type proof remains an upstream Rust obligation.
    RustProofPending,
}

impl NativeIrValidation {
    /// Returns the frozen result spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        "rust-proof-pending"
    }
}

/// One accepted all-or-none portable patch transaction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedPatch {
    /// Exact refreshed portable output definition.
    pub output_definition: SemanticJson,
    /// Derived output definition identity.
    pub output_definition_digest: Digest,
    /// Patch-as-transformation identity.
    pub transformation_id: Digest,
    /// Candidate identity for identical-patch deduplication.
    pub candidate_id: Digest,
    /// Mutant identity over baseline and patch.
    pub mutant_id: Digest,
    /// Exact normalized structural diff.
    pub structural_diff: SemanticJson,
    /// Derived structural-diff identity.
    pub diff_id: Digest,
    /// Portable application authority.
    pub portable_application: PortableApplication,
    /// Explicitly pending native validation.
    pub native_ir_validation: NativeIrValidation,
    /// Number of edits committed together.
    pub applied_edit_count: usize,
}

/// Immutable portable staging data presented to one native validator.
///
/// The value exists only for the duration of the validator call.
/// The validator may inspect the immutable baseline and patch together with the complete portable result, but it cannot mutate the staged transaction through this boundary.
#[derive(Clone, Copy, Debug)]
pub struct StagedNativeInput<'a> {
    baseline: &'a SemanticJson,
    patch: &'a Patch,
    portable: &'a AppliedPatch,
}

impl<'a> StagedNativeInput<'a> {
    /// Returns the immutable portable baseline.
    #[must_use]
    pub const fn baseline(&self) -> &'a SemanticJson {
        self.baseline
    }

    /// Returns the supplied canonical patch.
    #[must_use]
    pub const fn patch(&self) -> &'a Patch {
        self.patch
    }

    /// Returns the staged portable application result.
    #[must_use]
    pub const fn portable(&self) -> &'a AppliedPatch {
        self.portable
    }
}

/// One portable patch and its validator-produced opaque native output.
///
/// Construction is restricted to [`apply_patch_with_native_validation`], so neither component is published unless portable staging and native validation both succeed.
/// This generic wrapper records transaction success; it does not by itself grant a native-proof receipt or bind toolchain pins, profiles, lowering provenance, or evaluator authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeValidatedPatch<N> {
    portable: AppliedPatch,
    native_output: N,
}

impl<N> NativeValidatedPatch<N> {
    /// Returns the committed portable application result.
    #[must_use]
    pub const fn portable(&self) -> &AppliedPatch {
        &self.portable
    }

    /// Returns the opaque native output accepted by the validator.
    #[must_use]
    pub const fn native_output(&self) -> &N {
        &self.native_output
    }

    /// Separates the committed portable and opaque native outputs.
    #[must_use]
    pub fn into_parts(self) -> (AppliedPatch, N) {
        (self.portable, self.native_output)
    }
}

/// Closed native-validator rejection classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeValidationRejectionKind {
    /// The validator rejected the privately staged portable result.
    ValidatorRejected,
}

impl NativeValidationRejectionKind {
    /// Returns the stable rejection spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        "validator-rejected"
    }
}

/// Boundary-owned native rejection with no validator-owned payload.
///
/// The transaction seam constructs this value after discarding the validator's error.
/// Its diagnostic is fixed by the closed classification and cannot carry staged portable output or output-derived identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NativeValidationRejection {
    kind: NativeValidationRejectionKind,
}

impl NativeValidationRejection {
    const fn validator_rejected() -> Self {
        Self {
            kind: NativeValidationRejectionKind::ValidatorRejected,
        }
    }

    /// Returns the decision-bearing rejection classification.
    #[must_use]
    pub const fn kind(self) -> NativeValidationRejectionKind {
        self.kind
    }

    /// Returns boundary-owned supplemental diagnostics.
    #[must_use]
    pub const fn diagnostic(self) -> &'static str {
        "the native validator rejected the privately staged portable result"
    }
}

impl fmt::Display for NativeValidationRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.diagnostic())
    }
}

impl std::error::Error for NativeValidationRejection {}

/// Failure of portable staging or subsequent native validation.
///
/// Neither branch contains staged output or any output-derived identity.
/// A validator-owned error is always discarded before the closed native branch is returned.
///
/// The NR-R0 error-payload recovery pattern is rejected at compile time because the native branch carries only [`NativeValidationRejection`]:
///
/// ```compile_fail
/// use kink_patch::{AppliedPatch, NativeTransactionFailure};
///
/// fn recover_staged_output(failure: NativeTransactionFailure) -> AppliedPatch {
///     match failure {
///         NativeTransactionFailure::Native(leak) => leak.staged,
///         NativeTransactionFailure::Portable(_) => panic!("no staged output"),
///     }
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NativeTransactionFailure {
    /// Portable application failed before native validation was invoked.
    Portable(PatchFailure),
    /// Native validation rejected, with its error payload discarded.
    Native(NativeValidationRejection),
}

impl NativeTransactionFailure {
    /// Failed staged transactions always publish zero committed edits.
    #[must_use]
    pub const fn committed_edit_count(&self) -> usize {
        0
    }
}

impl fmt::Display for NativeTransactionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Portable(failure) => write!(formatter, "portable staging failed: {failure}"),
            Self::Native(failure) => write!(formatter, "native validation failed: {failure}"),
        }
    }
}

impl std::error::Error for NativeTransactionFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Portable(failure) => Some(failure),
            Self::Native(failure) => Some(failure),
        }
    }
}

/// Applies a portable patch, validates the private staged result, and publishes both outputs together.
///
/// This function delegates portable behavior to [`apply_patch`].
/// The staged portable value stays local until `validator` returns `Ok`; either failure branch exposes zero committed edits and no boundary-owned output.
/// Atomicity here is in-memory ownership and publication atomicity, not durable storage or process isolation.
/// Validator panics are not converted into typed failures.
pub fn apply_patch_with_native_validation<N, E>(
    baseline: &SemanticJson,
    patch: &Patch,
    validator: impl FnOnce(StagedNativeInput<'_>) -> Result<N, E>,
) -> Result<NativeValidatedPatch<N>, NativeTransactionFailure> {
    let portable = apply_patch(baseline, patch).map_err(NativeTransactionFailure::Portable)?;
    let native_output = match validator(StagedNativeInput {
        baseline,
        patch,
        portable: &portable,
    }) {
        Ok(native_output) => native_output,
        Err(validator_error) => {
            drop(validator_error);
            return Err(NativeTransactionFailure::Native(
                NativeValidationRejection::validator_rejected(),
            ));
        }
    };
    Ok(NativeValidatedPatch {
        portable,
        native_output,
    })
}

/// Applies one canonical supplied patch against one immutable portable baseline.
///
/// All preflight reads resolve against `baseline`. No accepted output value or
/// output-derived identity exists on the error branch.
pub fn apply_patch(baseline: &SemanticJson, patch: &Patch) -> Result<AppliedPatch, PatchFailure> {
    let parsed_baseline = PortableDefinition::from_json(baseline).map_err(|failure| {
        PatchFailure::new(
            PatchFailureKind::LocallyIllFormed,
            format!("invalid immutable baseline: {failure}"),
        )
    })?;
    let index = sentence_index(baseline)?;
    let modules = module_index(baseline)?;
    let mut signatures = BTreeMap::new();
    seed_signatures(baseline, &mut signatures)?;

    for edit in &patch.edits {
        preflight_edit(baseline, edit, &index, &modules, &mut signatures)?;
    }
    validate_overlaps(&patch.edits)?;

    let transformation_id = digest(
        &domain("k-in-k/transformation/v1"),
        &json_object([
            ("kind", SemanticJson::String("mutation".to_owned())),
            (
                "operatorId",
                SemanticJson::String(patch.operator_id.clone()),
            ),
            (
                "operatorVersion",
                SemanticJson::Integer(to_i64(patch.operator_version)),
            ),
            (
                "inputDefinitionDigest",
                SemanticJson::String(parsed_baseline.definition_digest.to_string()),
            ),
            (
                "manifestDigest",
                SemanticJson::String(patch.patch_id.to_string()),
            ),
        ]),
    );

    let mut output = baseline.clone();
    commit_edits(
        &mut output,
        baseline,
        patch,
        &index,
        &modules,
        &transformation_id,
    )?;
    refresh_definition(&mut output)?;
    let parsed_output = PortableDefinition::from_json(&output).map_err(|failure| {
        PatchFailure::new(
            PatchFailureKind::LocallyIllFormed,
            format!("portable output validation failed: {failure}"),
        )
    })?;

    // Re-seed with the immutable baseline before checking the complete output.
    // This prevents replacing the last occurrence of a baseline-known symbol
    // with a contradictory signature.
    let mut output_signatures = BTreeMap::new();
    seed_signatures(baseline, &mut output_signatures)?;
    seed_signatures(&output, &mut output_signatures)?;

    let (structural_diff, diff_id) = build_diff(
        baseline,
        &output,
        patch,
        &index,
        &modules,
        &transformation_id,
        &parsed_baseline.definition_digest,
        &parsed_output.definition_digest,
    )?;
    let candidate_id = digest(
        &domain("k-in-k/candidate/v1"),
        &json_object([
            (
                "operatorId",
                SemanticJson::String(patch.operator_id.clone()),
            ),
            (
                "operatorVersion",
                SemanticJson::Integer(to_i64(patch.operator_version)),
            ),
            (
                "baselineDefinitionDigest",
                SemanticJson::String(parsed_baseline.definition_digest.to_string()),
            ),
            ("patchId", SemanticJson::String(patch.patch_id.to_string())),
        ]),
    );
    let mutant_id = digest(
        &domain("k-in-k/mutant/v1"),
        &json_object([
            (
                "baselineDefinitionDigest",
                SemanticJson::String(parsed_baseline.definition_digest.to_string()),
            ),
            ("patchId", SemanticJson::String(patch.patch_id.to_string())),
        ]),
    );

    Ok(AppliedPatch {
        output_definition: output,
        output_definition_digest: parsed_output.definition_digest,
        transformation_id,
        candidate_id,
        mutant_id,
        structural_diff,
        diff_id,
        portable_application: PortableApplication::AppliedAndLocallyWellFormed,
        native_ir_validation: NativeIrValidation::RustProofPending,
        applied_edit_count: patch.edits.len(),
    })
}

fn digest(domain: &DigestDomain, value: &SemanticJson) -> Digest {
    checked_digest(domain, value).expect("validated patch transaction forms semantic JSON")
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SymbolSignature {
    label: String,
    result_sort: String,
    argument_sorts: Vec<String>,
}

fn seed_signatures(
    definition: &SemanticJson,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
) -> Result<(), PatchFailure> {
    for module in array_field(object(definition)?, "modules")? {
        for sentence in array_field(object(module)?, "sentences")? {
            let sentence = object(sentence)?;
            validate_sentence(sentence.get("value").ok_or_else(ill_formed)?, signatures)?;
        }
    }
    Ok(())
}

fn validate_sentence(
    sentence: &SemanticJson,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
) -> Result<(), PatchFailure> {
    let fields = object(sentence)?;
    exact_fields(
        fields,
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
    )?;
    if string_field(fields, "encoding")? != "portable-semantic-sentence-v1"
        || string_field(fields, "module")?.is_empty()
        || !matches!(
            string_field(fields, "kind")?,
            "rule" | "claim" | "context" | "alias" | "configuration"
        )
        || string_field(fields, "source")?.is_empty()
    {
        return Err(ill_formed());
    }
    match fields.get("label") {
        Some(SemanticJson::Null | SemanticJson::String(_)) => {}
        _ => return Err(ill_formed()),
    }
    validate_location(fields.get("location").ok_or_else(ill_formed)?)?;
    let mut variables = BTreeMap::new();
    validate_term(
        fields.get("body").ok_or_else(ill_formed)?,
        signatures,
        &mut variables,
    )?;
    for condition_name in ["requires", "ensures"] {
        if let Some(condition) = fields.get(condition_name) {
            if *condition != SemanticJson::Null {
                validate_term(condition, signatures, &mut variables)?;
                if term_sort(condition)? != "Bool" {
                    return Err(ill_formed());
                }
            }
        } else {
            return Err(ill_formed());
        }
    }
    let attributes = array_field(fields, "attributes")?;
    let mut prior: Option<&str> = None;
    for attribute in attributes {
        let attribute = object(attribute)?;
        exact_fields(attribute, &["name", "value"])?;
        let name = string_field(attribute, "name")?;
        if name.is_empty() || prior.is_some_and(|prior| prior >= name) {
            return Err(ill_formed());
        }
        prior = Some(name);
        match attribute.get("value") {
            Some(SemanticJson::Null) => {}
            Some(term) => validate_term(term, signatures, &mut variables)?,
            None => return Err(ill_formed()),
        }
    }
    Ok(())
}

fn validate_location(value: &SemanticJson) -> Result<(), PatchFailure> {
    let fields = object(value)?;
    exact_fields(
        fields,
        &["startLine", "startColumn", "endLine", "endColumn"],
    )?;
    let start = (
        positive_i64(fields.get("startLine"))?,
        positive_i64(fields.get("startColumn"))?,
    );
    let end = (
        positive_i64(fields.get("endLine"))?,
        positive_i64(fields.get("endColumn"))?,
    );
    if end < start {
        return Err(ill_formed());
    }
    Ok(())
}

fn validate_term(
    term: &SemanticJson,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
    variables: &mut BTreeMap<String, String>,
) -> Result<(), PatchFailure> {
    let fields = object(term)?;
    exact_fields(fields, &["encoding", "sort", "node"])?;
    if string_field(fields, "encoding")? != "portable-term-v1" {
        return Err(ill_formed());
    }
    let sort = string_field(fields, "sort")?;
    if sort.is_empty() {
        return Err(ill_formed());
    }
    let node = object(fields.get("node").ok_or_else(ill_formed)?)?;
    match string_field(node, "kind")? {
        "token" => {
            exact_fields(node, &["kind", "text"])?;
            if !matches!(node.get("text"), Some(SemanticJson::String(_))) {
                return Err(ill_formed());
            }
        }
        "variable" => {
            exact_fields(node, &["kind", "name"])?;
            let name = string_field(node, "name")?;
            if name.is_empty() {
                return Err(ill_formed());
            }
            if let Some(previous) = variables.insert(name.to_owned(), sort.to_owned())
                && previous != sort
            {
                return Err(ill_formed());
            }
        }
        "application" => {
            exact_fields(node, &["kind", "symbolId", "label", "args"])?;
            let symbol_id = parse_digest_field(node, "symbolId")?;
            let label = string_field(node, "label")?;
            if label.is_empty() {
                return Err(ill_formed());
            }
            let args = array_field(node, "args")?;
            for argument in args {
                validate_term(argument, signatures, variables)?;
            }
            let signature = SymbolSignature {
                label: label.to_owned(),
                result_sort: sort.to_owned(),
                argument_sorts: args
                    .iter()
                    .map(term_sort)
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
            };
            if let Some(previous) = signatures.insert(symbol_id, signature.clone())
                && previous != signature
            {
                return Err(ill_formed());
            }
        }
        "rewrite" => {
            exact_fields(node, &["kind", "left", "right"])?;
            let left = node.get("left").ok_or_else(ill_formed)?;
            let right = node.get("right").ok_or_else(ill_formed)?;
            validate_term(left, signatures, variables)?;
            validate_term(right, signatures, variables)?;
            if term_sort(left)? != term_sort(right)? {
                return Err(ill_formed());
            }
        }
        "sequence" => {
            exact_fields(node, &["kind", "items"])?;
            for item in array_field(node, "items")? {
                validate_term(item, signatures, variables)?;
            }
        }
        "injection" => {
            exact_fields(node, &["kind", "fromSort", "toSort", "term"])?;
            let child = node.get("term").ok_or_else(ill_formed)?;
            validate_term(child, signatures, variables)?;
            if term_sort(child)? != string_field(node, "fromSort")?
                || sort != string_field(node, "toSort")?
            {
                return Err(ill_formed());
            }
        }
        _ => return Err(ill_formed()),
    }
    Ok(())
}

fn preflight_edit(
    baseline: &SemanticJson,
    edit: &Edit,
    index: &BTreeMap<Digest, (usize, usize)>,
    modules: &BTreeMap<String, usize>,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
) -> Result<(), PatchFailure> {
    if edit.operation == Operation::InsertSentence
        && matches!(
            edit.position.as_ref().map(|position| position.kind),
            Some(InsertPositionKind::ModuleStart | InsertPositionKind::ModuleEnd)
        )
    {
        let position = edit.position.as_ref().expect("model validation");
        let module_name = position.module.as_ref().expect("model validation");
        let module = module_at(baseline, *modules.get(module_name).ok_or_else(stale)?)?;
        if parse_digest_field(object(module)?, "fingerprint")?
            != *edit
                .expected_module_fingerprint
                .as_ref()
                .expect("model validation")
        {
            return Err(stale());
        }
        if sentence_module(edit_sentence(edit)?)? != module_name {
            return Err(invalid_position());
        }
    } else {
        let lineage = edit.target_lineage.as_ref().expect("model validation");
        let (module_ordinal, sentence_ordinal) = index.get(lineage).copied().ok_or_else(stale)?;
        let sentence = sentence_at(baseline, module_ordinal, sentence_ordinal)?;
        if provenance_digest(sentence, "contentFingerprint")?
            != *edit.expected_content.as_ref().expect("model validation")
        {
            return Err(stale());
        }
        if edit.operation == Operation::InsertSentence {
            let position = edit.position.as_ref().expect("model validation");
            if position.anchor_lineage.as_ref() != Some(lineage) {
                return Err(invalid_position());
            }
            let module = module_at(baseline, module_ordinal)?;
            let module_name = string_field(object(module)?, "name")?;
            if sentence_module(edit_sentence(edit)?)? != module_name {
                return Err(invalid_position());
            }
        }

        match edit.operation {
            Operation::ReplaceTerm | Operation::ReplaceCondition => {
                let sentence_value = sentence_value(sentence)?;
                let old = path_get(sentence_value, &edit.target_path)?;
                let replacement = replacement_term(baseline, edit, index)?;
                if edit.operation == Operation::ReplaceTerm
                    && term_sort(old)? != term_sort(replacement)?
                {
                    return Err(ill_formed());
                }
                if edit.operation == Operation::ReplaceCondition
                    && term_sort(replacement)? != "Bool"
                {
                    return Err(ill_formed());
                }
                validate_term(replacement, signatures, &mut BTreeMap::new())?;
                if old == replacement {
                    return Err(no_change());
                }
            }
            Operation::AddAttribute | Operation::RemoveAttribute | Operation::ReplaceAttribute => {
                preflight_attribute(sentence, edit, signatures)?;
            }
            Operation::ReplaceSentence => {
                let old = sentence_value(sentence)?;
                let replacement = edit_sentence(edit)?;
                if old == replacement {
                    return Err(no_change());
                }
                let old_fields = object(old)?;
                let replacement_fields = object(replacement)?;
                for field in ["module", "source", "kind", "location"] {
                    if old_fields.get(field) != replacement_fields.get(field) {
                        return Err(ill_formed());
                    }
                }
                validate_sentence(replacement, signatures)?;
            }
            Operation::DeleteSentence | Operation::InsertSentence => {}
        }
    }
    if edit.operation == Operation::InsertSentence {
        validate_sentence(edit_sentence(edit)?, signatures)?;
    }
    Ok(())
}

fn preflight_attribute(
    sentence: &SemanticJson,
    edit: &Edit,
    signatures: &mut BTreeMap<Digest, SymbolSignature>,
) -> Result<(), PatchFailure> {
    let PathStep::Attribute(name) = &edit.target_path.0[1] else {
        return Err(malformed_path());
    };
    let value_fields = object(sentence_value(sentence)?)?;
    let attributes = array_field(value_fields, "attributes")?;
    let matches: Vec<&SemanticJson> = attributes
        .iter()
        .filter(|attribute| {
            object(attribute)
                .ok()
                .and_then(|fields| fields.get("name"))
                .and_then(SemanticJson::as_str)
                == Some(name)
        })
        .collect();
    if edit.operation == Operation::AddAttribute {
        if !matches.is_empty() {
            return Err(stale());
        }
    } else {
        if matches.len() != 1 {
            return Err(stale());
        }
        let actual = digest(&domain("k-in-k/attribute/v1"), matches[0]);
        if Some(&actual) != edit.expected_attribute_fingerprint.as_ref() {
            return Err(stale());
        }
    }
    if let EditValue::Attribute {
        name: replacement_name,
        value,
    } = &edit.value
    {
        if replacement_name != name {
            return Err(ill_formed());
        }
        if let Some(value) = value {
            validate_term(value, signatures, &mut BTreeMap::new())?;
        }
        if edit.operation == Operation::ReplaceAttribute {
            let replacement = json_object([
                ("name", SemanticJson::String(replacement_name.clone())),
                ("value", value.clone().unwrap_or(SemanticJson::Null)),
            ]);
            if matches.first().copied() == Some(&replacement) {
                return Err(no_change());
            }
        }
    }
    Ok(())
}

fn validate_overlaps(edits: &[Edit]) -> Result<(), PatchFailure> {
    for (index, left) in edits.iter().enumerate() {
        for right in &edits[index + 1..] {
            if left.operation == Operation::InsertSentence
                && right.operation == Operation::InsertSentence
            {
                let left_position = left.position.as_ref().expect("model validation");
                let right_position = right.position.as_ref().expect("model validation");
                if left_position.kind == right_position.kind
                    && left_position.anchor_lineage == right_position.anchor_lineage
                    && left_position.module == right_position.module
                    && left_position.ordinal == right_position.ordinal
                {
                    return Err(duplicate_target());
                }
            }
            if left.target_lineage.is_some()
                && left.target_lineage == right.target_lineage
                && left.operation != Operation::InsertSentence
                && right.operation != Operation::InsertSentence
            {
                if left.target_path == right.target_path {
                    return Err(duplicate_target());
                }
                if left.target_path.is_prefix_of(&right.target_path)
                    || right.target_path.is_prefix_of(&left.target_path)
                {
                    return Err(overlapping());
                }
            }
            for (anchor, destructive) in [(left, right), (right, left)] {
                if anchor.operation == Operation::InsertSentence
                    && matches!(
                        anchor.position.as_ref().map(|position| position.kind),
                        Some(InsertPositionKind::BeforeLineage | InsertPositionKind::AfterLineage)
                    )
                    && matches!(
                        destructive.operation,
                        Operation::ReplaceSentence | Operation::DeleteSentence
                    )
                    && anchor
                        .position
                        .as_ref()
                        .and_then(|item| item.anchor_lineage.as_ref())
                        == destructive.target_lineage.as_ref()
                {
                    return Err(overlapping());
                }
            }
        }
    }
    Ok(())
}

type InsertionKey = (String, InsertPositionKind, String);

fn commit_edits(
    output: &mut SemanticJson,
    baseline: &SemanticJson,
    patch: &Patch,
    index: &BTreeMap<Digest, (usize, usize)>,
    modules: &BTreeMap<String, usize>,
    transformation_id: &Digest,
) -> Result<(), PatchFailure> {
    let mut deleted = BTreeSet::new();
    let mut insertions: BTreeMap<InsertionKey, Vec<(u64, SemanticJson)>> = BTreeMap::new();
    for edit in &patch.edits {
        if edit.operation == Operation::InsertSentence {
            let position = edit.position.as_ref().expect("model validation");
            let (module_name, parents, anchor_name, anchor_identity) = match position.kind {
                InsertPositionKind::BeforeLineage | InsertPositionKind::AfterLineage => {
                    let lineage = position.anchor_lineage.as_ref().expect("model validation");
                    let (module_ordinal, _) = index.get(lineage).copied().expect("preflight");
                    let module = module_at(baseline, module_ordinal)?;
                    (
                        string_field(object(module)?, "name")?.to_owned(),
                        vec![lineage.clone()],
                        lineage.to_string(),
                        lineage.clone(),
                    )
                }
                InsertPositionKind::ModuleStart | InsertPositionKind::ModuleEnd => {
                    let module_name = position.module.as_ref().expect("model validation");
                    let module = module_at(
                        baseline,
                        *modules.get(module_name).expect("preflight module exists"),
                    )?;
                    (
                        module_name.clone(),
                        Vec::new(),
                        module_name.clone(),
                        parse_digest_field(object(module)?, "fingerprint")?,
                    )
                }
            };
            let generated_payload = json_object([
                (
                    "transformationId",
                    SemanticJson::String(transformation_id.to_string()),
                ),
                (
                    "parentLineages",
                    SemanticJson::Array(
                        parents
                            .iter()
                            .map(|lineage| SemanticJson::String(lineage.to_string()))
                            .collect(),
                    ),
                ),
                (
                    "anchorIdentity",
                    SemanticJson::String(anchor_identity.to_string()),
                ),
                (
                    "role",
                    SemanticJson::String(position.kind.generated_role().to_owned()),
                ),
                ("ordinal", SemanticJson::Integer(to_i64(position.ordinal))),
            ]);
            let lineage = digest(&domain("k-in-k/generated-lineage/v1"), &generated_payload);
            let sentence_value = edit_sentence(edit)?.clone();
            let fields = object(&sentence_value)?;
            let inserted = json_object([
                ("sourceOccurrenceOrdinal", SemanticJson::Null),
                ("generatedIdentity", generated_payload),
                (
                    "provenance",
                    json_object([
                        ("lineageId", SemanticJson::String(lineage.to_string())),
                        ("contentFingerprint", SemanticJson::String("0".repeat(64))),
                        ("bodyFingerprint", SemanticJson::String("0".repeat(64))),
                        (
                            "module",
                            fields.get("module").expect("validated sentence").clone(),
                        ),
                        (
                            "label",
                            fields.get("label").expect("validated sentence").clone(),
                        ),
                        (
                            "kind",
                            fields.get("kind").expect("validated sentence").clone(),
                        ),
                        (
                            "source",
                            fields.get("source").expect("validated sentence").clone(),
                        ),
                        (
                            "location",
                            fields.get("location").expect("validated sentence").clone(),
                        ),
                        ("generated", SemanticJson::Bool(true)),
                        (
                            "transformationChain",
                            SemanticJson::Array(vec![SemanticJson::String(
                                transformation_id.to_string(),
                            )]),
                        ),
                    ]),
                ),
                ("value", sentence_value),
            ]);
            insertions
                .entry((module_name, position.kind, anchor_name))
                .or_default()
                .push((position.ordinal, inserted));
            continue;
        }

        let lineage = edit.target_lineage.as_ref().expect("model validation");
        match edit.operation {
            Operation::ReplaceTerm | Operation::ReplaceCondition => {
                let replacement = replacement_term(baseline, edit, index)?.clone();
                let sentence = find_sentence_mut(output, lineage)?;
                path_replace(
                    sentence_value_mut(sentence)?,
                    &edit.target_path,
                    replacement,
                )?;
            }
            Operation::ReplaceSentence => {
                let replacement = edit_sentence(edit)?.clone();
                let sentence = object_mut(find_sentence_mut(output, lineage)?)?;
                sentence.insert("value".to_owned(), replacement);
            }
            Operation::DeleteSentence => {
                deleted.insert(lineage.clone());
            }
            Operation::AddAttribute | Operation::RemoveAttribute | Operation::ReplaceAttribute => {
                commit_attribute(find_sentence_mut(output, lineage)?, edit)?;
            }
            Operation::InsertSentence => unreachable!("handled above"),
        }
    }

    let root = object_mut(output)?;
    let modules_value = root.get_mut("modules").ok_or_else(ill_formed)?;
    let SemanticJson::Array(output_modules) = modules_value else {
        return Err(ill_formed());
    };
    for module in output_modules {
        let module_fields = object_mut(module)?;
        let module_name = string_field(module_fields, "name")?.to_owned();
        let sentence_value = module_fields.get_mut("sentences").ok_or_else(ill_formed)?;
        let SemanticJson::Array(sentences) = sentence_value else {
            return Err(ill_formed());
        };
        let original_sentences = sentences.clone();
        let mut rebuilt = Vec::new();
        extend_insertions(
            &mut rebuilt,
            &mut insertions,
            &(
                module_name.clone(),
                InsertPositionKind::ModuleStart,
                module_name.clone(),
            ),
        );
        for sentence in original_sentences {
            let lineage = provenance_digest(&sentence, "lineageId")?;
            extend_insertions(
                &mut rebuilt,
                &mut insertions,
                &(
                    module_name.clone(),
                    InsertPositionKind::BeforeLineage,
                    lineage.to_string(),
                ),
            );
            if !deleted.contains(&lineage) {
                rebuilt.push(sentence);
            }
            extend_insertions(
                &mut rebuilt,
                &mut insertions,
                &(
                    module_name.clone(),
                    InsertPositionKind::AfterLineage,
                    lineage.to_string(),
                ),
            );
        }
        extend_insertions(
            &mut rebuilt,
            &mut insertions,
            &(
                module_name.clone(),
                InsertPositionKind::ModuleEnd,
                module_name,
            ),
        );
        *sentences = rebuilt;
    }
    if !insertions.is_empty() {
        return Err(invalid_position());
    }
    Ok(())
}

fn extend_insertions(
    output: &mut Vec<SemanticJson>,
    insertions: &mut BTreeMap<InsertionKey, Vec<(u64, SemanticJson)>>,
    key: &InsertionKey,
) {
    if let Some(mut values) = insertions.remove(key) {
        values.sort_by_key(|(ordinal, _)| *ordinal);
        output.extend(values.into_iter().map(|(_, sentence)| sentence));
    }
}

fn commit_attribute(sentence: &mut SemanticJson, edit: &Edit) -> Result<(), PatchFailure> {
    let PathStep::Attribute(name) = &edit.target_path.0[1] else {
        return Err(malformed_path());
    };
    let value = sentence_value_mut(sentence)?;
    let fields = object_mut(value)?;
    let attributes = fields.get_mut("attributes").ok_or_else(ill_formed)?;
    let SemanticJson::Array(attributes) = attributes else {
        return Err(ill_formed());
    };
    let replacement = match &edit.value {
        EditValue::Attribute { name, value } => Some(json_object([
            ("name", SemanticJson::String(name.clone())),
            ("value", value.clone().unwrap_or(SemanticJson::Null)),
        ])),
        EditValue::None => None,
        _ => return Err(ill_formed()),
    };
    match edit.operation {
        Operation::AddAttribute => attributes.push(replacement.expect("model validation")),
        Operation::RemoveAttribute => attributes.retain(|attribute| {
            object(attribute)
                .ok()
                .and_then(|fields| fields.get("name"))
                .and_then(SemanticJson::as_str)
                != Some(name)
        }),
        Operation::ReplaceAttribute => {
            let replacement = replacement.expect("model validation");
            for attribute in attributes.iter_mut() {
                if object(attribute)?
                    .get("name")
                    .and_then(SemanticJson::as_str)
                    == Some(name)
                {
                    *attribute = replacement.clone();
                }
            }
        }
        _ => unreachable!("attribute operation"),
    }
    attributes.sort_by(|left, right| attribute_name(left).cmp(attribute_name(right)));
    Ok(())
}

fn attribute_name(value: &SemanticJson) -> &str {
    value
        .as_object()
        .and_then(|fields| fields.get("name"))
        .and_then(SemanticJson::as_str)
        .unwrap_or("")
}

fn refresh_definition(definition: &mut SemanticJson) -> Result<(), PatchFailure> {
    let root = object_mut(definition)?;
    let schema_version = root.get("schemaVersion").cloned().ok_or_else(ill_formed)?;
    let representation = root.get("representation").cloned().ok_or_else(ill_formed)?;
    let baseline_family = root
        .get("baselineFamilyId")
        .cloned()
        .ok_or_else(ill_formed)?;
    let modules_value = root.get_mut("modules").ok_or_else(ill_formed)?;
    let SemanticJson::Array(modules) = modules_value else {
        return Err(ill_formed());
    };
    let mut module_payloads = Vec::new();
    for module in modules {
        let module_fields = object_mut(module)?;
        let name = module_fields.get("name").cloned().ok_or_else(ill_formed)?;
        let ordinal = module_fields
            .get("ordinal")
            .cloned()
            .ok_or_else(ill_formed)?;
        let imports = module_fields
            .get("imports")
            .cloned()
            .ok_or_else(ill_formed)?;
        let sentences_value = module_fields.get_mut("sentences").ok_or_else(ill_formed)?;
        let SemanticJson::Array(sentences) = sentences_value else {
            return Err(ill_formed());
        };
        let mut content_fingerprints = Vec::new();
        for sentence in sentences {
            let sentence_fields = object_mut(sentence)?;
            let value = sentence_fields
                .get("value")
                .cloned()
                .ok_or_else(ill_formed)?;
            let value_fields = object(&value)?;
            let provenance_value = sentence_fields
                .get_mut("provenance")
                .ok_or_else(ill_formed)?;
            let provenance = object_mut(provenance_value)?;
            for field in ["module", "label", "kind", "source", "location"] {
                provenance.insert(
                    field.to_owned(),
                    value_fields.get(field).cloned().ok_or_else(ill_formed)?,
                );
            }
            let body_payload = json_object([
                (
                    "body",
                    value_fields.get("body").cloned().ok_or_else(ill_formed)?,
                ),
                (
                    "requires",
                    value_fields
                        .get("requires")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
                (
                    "ensures",
                    value_fields
                        .get("ensures")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
            ]);
            let body_id = digest(&domain("k-in-k/sentence-body/v1"), &body_payload);
            provenance.insert(
                "bodyFingerprint".to_owned(),
                SemanticJson::String(body_id.to_string()),
            );
            let content_payload = json_object([
                (
                    "lineageId",
                    provenance
                        .get("lineageId")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
                (
                    "module",
                    value_fields.get("module").cloned().ok_or_else(ill_formed)?,
                ),
                (
                    "label",
                    value_fields.get("label").cloned().ok_or_else(ill_formed)?,
                ),
                (
                    "kind",
                    value_fields.get("kind").cloned().ok_or_else(ill_formed)?,
                ),
                (
                    "source",
                    value_fields.get("source").cloned().ok_or_else(ill_formed)?,
                ),
                (
                    "location",
                    value_fields
                        .get("location")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
                (
                    "generated",
                    provenance
                        .get("generated")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
                ("bodyFingerprint", SemanticJson::String(body_id.to_string())),
                (
                    "attributes",
                    value_fields
                        .get("attributes")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
                (
                    "transformationChain",
                    provenance
                        .get("transformationChain")
                        .cloned()
                        .ok_or_else(ill_formed)?,
                ),
            ]);
            let content_id = digest(&domain("k-in-k/sentence-content/v1"), &content_payload);
            provenance.insert(
                "contentFingerprint".to_owned(),
                SemanticJson::String(content_id.to_string()),
            );
            content_fingerprints.push(SemanticJson::String(content_id.to_string()));
        }
        let module_payload = json_object([
            ("name", name),
            ("ordinal", ordinal),
            ("imports", imports),
            (
                "sentenceContentFingerprints",
                SemanticJson::Array(content_fingerprints),
            ),
        ]);
        let module_id = digest(&domain("k-in-k/module/v1"), &module_payload);
        module_fields.insert(
            "fingerprint".to_owned(),
            SemanticJson::String(module_id.to_string()),
        );
        module_payloads.push(module_payload);
    }
    let definition_payload = json_object([
        ("schemaVersion", schema_version),
        ("representation", representation),
        ("baselineFamilyId", baseline_family),
        ("modules", SemanticJson::Array(module_payloads)),
    ]);
    let definition_id = digest(&domain("k-in-k/definition/v1"), &definition_payload);
    root.insert(
        "definitionDigest".to_owned(),
        SemanticJson::String(definition_id.to_string()),
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_diff(
    baseline: &SemanticJson,
    output: &SemanticJson,
    patch: &Patch,
    index: &BTreeMap<Digest, (usize, usize)>,
    modules: &BTreeMap<String, usize>,
    transformation_id: &Digest,
    baseline_digest: &Digest,
    output_digest: &Digest,
) -> Result<(SemanticJson, Digest), PatchFailure> {
    let output_index = sentence_index(output)?;
    let mut entries = Vec::new();
    for edit in &patch.edits {
        let (target_lineage, before, after, affected_provenance) = if edit.operation
            == Operation::InsertSentence
        {
            let position = edit.position.as_ref().expect("model validation");
            let (parents, anchor) = match position.kind {
                InsertPositionKind::BeforeLineage | InsertPositionKind::AfterLineage => {
                    let lineage = position.anchor_lineage.as_ref().expect("model validation");
                    (vec![lineage.clone()], lineage.clone())
                }
                InsertPositionKind::ModuleStart | InsertPositionKind::ModuleEnd => {
                    let module_name = position.module.as_ref().expect("model validation");
                    let module = module_at(
                        baseline,
                        *modules.get(module_name).expect("preflight module exists"),
                    )?;
                    (
                        Vec::new(),
                        parse_digest_field(object(module)?, "fingerprint")?,
                    )
                }
            };
            let identity = json_object([
                (
                    "transformationId",
                    SemanticJson::String(transformation_id.to_string()),
                ),
                (
                    "parentLineages",
                    SemanticJson::Array(
                        parents
                            .iter()
                            .map(|value| SemanticJson::String(value.to_string()))
                            .collect(),
                    ),
                ),
                ("anchorIdentity", SemanticJson::String(anchor.to_string())),
                (
                    "role",
                    SemanticJson::String(position.kind.generated_role().to_owned()),
                ),
                ("ordinal", SemanticJson::Integer(to_i64(position.ordinal))),
            ]);
            let lineage = digest(&domain("k-in-k/generated-lineage/v1"), &identity);
            let (module, sentence) = output_index.get(&lineage).copied().ok_or_else(ill_formed)?;
            let sentence = sentence_at(output, module, sentence)?;
            (
                lineage,
                SemanticJson::Null,
                SemanticJson::String(
                    provenance_digest(sentence, "contentFingerprint")?.to_string(),
                ),
                provenance(sentence)?.clone(),
            )
        } else {
            let lineage = edit
                .target_lineage
                .as_ref()
                .expect("model validation")
                .clone();
            let (module, sentence) = index.get(&lineage).copied().expect("preflight");
            let original_sentence = sentence_at(baseline, module, sentence)?;
            let affected = provenance(original_sentence)?.clone();
            if edit.operation == Operation::DeleteSentence {
                (
                    lineage,
                    SemanticJson::String(
                        provenance_digest(original_sentence, "contentFingerprint")?.to_string(),
                    ),
                    SemanticJson::Null,
                    affected,
                )
            } else if matches!(
                edit.operation,
                Operation::AddAttribute | Operation::RemoveAttribute | Operation::ReplaceAttribute
            ) {
                let PathStep::Attribute(name) = &edit.target_path.0[1] else {
                    return Err(malformed_path());
                };
                let old = find_attribute(sentence_value(original_sentence)?, name)?;
                let (output_module, output_sentence) =
                    output_index.get(&lineage).copied().ok_or_else(ill_formed)?;
                let new = find_attribute(
                    sentence_value(sentence_at(output, output_module, output_sentence)?)?,
                    name,
                )?;
                (
                    lineage,
                    optional_diff_digest(old),
                    optional_diff_digest(new),
                    affected,
                )
            } else {
                let old_region = if edit.target_path.0.is_empty() {
                    sentence_value(original_sentence)?
                } else {
                    path_get(sentence_value(original_sentence)?, &edit.target_path)?
                };
                let (output_module, output_sentence) =
                    output_index.get(&lineage).copied().ok_or_else(ill_formed)?;
                let output_sentence = sentence_at(output, output_module, output_sentence)?;
                let new_region = if edit.target_path.0.is_empty() {
                    sentence_value(output_sentence)?
                } else {
                    path_get(sentence_value(output_sentence)?, &edit.target_path)?
                };
                (
                    lineage,
                    SemanticJson::String(
                        digest(&domain("k-in-k/diff-value/v1"), old_region).to_string(),
                    ),
                    SemanticJson::String(
                        digest(&domain("k-in-k/diff-value/v1"), new_region).to_string(),
                    ),
                    affected,
                )
            }
        };
        entries.push(json_object([
            ("editId", SemanticJson::String(edit.edit_id.to_string())),
            (
                "operation",
                SemanticJson::String(edit.operation.as_str().to_owned()),
            ),
            (
                "targetLineage",
                SemanticJson::String(target_lineage.to_string()),
            ),
            ("targetPath", edit.target_path.to_json()),
            ("beforeFingerprint", before),
            ("afterFingerprint", after),
            ("affectedProvenance", affected_provenance),
        ]));
    }
    let payload = json_object([
        ("schemaVersion", SemanticJson::Integer(1)),
        (
            "baselineDefinitionDigest",
            SemanticJson::String(baseline_digest.to_string()),
        ),
        (
            "mutantDefinitionDigest",
            SemanticJson::String(output_digest.to_string()),
        ),
        (
            "portableApplication",
            SemanticJson::String(
                PortableApplication::AppliedAndLocallyWellFormed
                    .as_str()
                    .to_owned(),
            ),
        ),
        (
            "nativeIrValidation",
            SemanticJson::String(NativeIrValidation::RustProofPending.as_str().to_owned()),
        ),
        ("entries", SemanticJson::Array(entries)),
    ]);
    let diff_id = digest(&domain("k-in-k/structural-diff/v1"), &payload);
    let SemanticJson::Object(mut fields) = payload else {
        unreachable!("object helper")
    };
    fields.insert(
        "diffId".to_owned(),
        SemanticJson::String(diff_id.to_string()),
    );
    Ok((SemanticJson::Object(fields), diff_id))
}

fn optional_diff_digest(value: Option<&SemanticJson>) -> SemanticJson {
    value.map_or(SemanticJson::Null, |value| {
        SemanticJson::String(digest(&domain("k-in-k/diff-value/v1"), value).to_string())
    })
}

fn find_attribute<'a>(
    sentence_value: &'a SemanticJson,
    name: &str,
) -> Result<Option<&'a SemanticJson>, PatchFailure> {
    let fields = object(sentence_value)?;
    let matches: Vec<_> = array_field(fields, "attributes")?
        .iter()
        .filter(|attribute| {
            object(attribute)
                .ok()
                .and_then(|fields| fields.get("name"))
                .and_then(SemanticJson::as_str)
                == Some(name)
        })
        .collect();
    if matches.len() > 1 {
        return Err(ill_formed());
    }
    Ok(matches.first().copied())
}

fn replacement_term<'a>(
    baseline: &'a SemanticJson,
    edit: &'a Edit,
    index: &BTreeMap<Digest, (usize, usize)>,
) -> Result<&'a SemanticJson, PatchFailure> {
    match &edit.value {
        EditValue::Term(term) => Ok(term),
        EditValue::OriginalReference { lineage, path } => {
            let (module, sentence) = index.get(lineage).copied().ok_or_else(stale)?;
            path_get(
                sentence_value(sentence_at(baseline, module, sentence)?)?,
                path,
            )
        }
        _ => Err(ill_formed()),
    }
}

fn edit_sentence(edit: &Edit) -> Result<&SemanticJson, PatchFailure> {
    match &edit.value {
        EditValue::Sentence(value) => Ok(value),
        _ => Err(ill_formed()),
    }
}

fn sentence_module(sentence: &SemanticJson) -> Result<&str, PatchFailure> {
    string_field(object(sentence)?, "module")
}

fn path_get<'a>(
    sentence_value: &'a SemanticJson,
    path: &TypedPath,
) -> Result<&'a SemanticJson, PatchFailure> {
    let mut current = sentence_value;
    for step in &path.0 {
        current = path_child(current, sentence_value, step)?;
    }
    Ok(current)
}

fn path_child<'a>(
    current: &'a SemanticJson,
    root: &SemanticJson,
    step: &PathStep,
) -> Result<&'a SemanticJson, PatchFailure> {
    match step {
        PathStep::Field(name) if std::ptr::eq(current, root) => {
            if !matches!(
                name.as_str(),
                "body" | "requires" | "ensures" | "attributes"
            ) {
                return Err(malformed_path());
            }
            object(current)?.get(name).ok_or_else(malformed_path)
        }
        PathStep::Field(name) if name == "lhs" || name == "rhs" => {
            let node = term_node(current)?;
            if string_field(node, "kind")? != "rewrite" {
                return Err(malformed_path());
            }
            node.get(if name == "lhs" { "left" } else { "right" })
                .ok_or_else(malformed_path)
        }
        PathStep::Argument(index) => {
            let node = term_node(current)?;
            if string_field(node, "kind")? != "application" {
                return Err(malformed_path());
            }
            array_field(node, "args")?
                .get(to_usize(*index)?)
                .ok_or_else(malformed_path)
        }
        PathStep::SequenceItem(index) => {
            let node = term_node(current)?;
            if string_field(node, "kind")? != "sequence" {
                return Err(malformed_path());
            }
            array_field(node, "items")?
                .get(to_usize(*index)?)
                .ok_or_else(malformed_path)
        }
        PathStep::InjectionTerm => {
            let node = term_node(current)?;
            if string_field(node, "kind")? != "injection" {
                return Err(malformed_path());
            }
            node.get("term").ok_or_else(malformed_path)
        }
        PathStep::Attribute(name) => {
            let SemanticJson::Array(attributes) = current else {
                return Err(malformed_path());
            };
            let matches: Vec<_> = attributes
                .iter()
                .filter(|attribute| {
                    object(attribute)
                        .ok()
                        .and_then(|fields| fields.get("name"))
                        .and_then(SemanticJson::as_str)
                        == Some(name)
                })
                .collect();
            if matches.len() == 1 {
                Ok(matches[0])
            } else {
                Err(malformed_path())
            }
        }
        PathStep::Field(_) => Err(malformed_path()),
    }
}

fn path_replace(
    sentence_value: &mut SemanticJson,
    path: &TypedPath,
    replacement: SemanticJson,
) -> Result<(), PatchFailure> {
    if path.0.is_empty() {
        return Err(malformed_path());
    }
    path_replace_steps(sentence_value, &path.0, replacement, true)
}

fn path_replace_steps(
    current: &mut SemanticJson,
    path: &[PathStep],
    replacement: SemanticJson,
    is_root: bool,
) -> Result<(), PatchFailure> {
    let step = &path[0];
    if path.len() == 1 {
        return replace_child(current, step, replacement, is_root);
    }
    let child = child_mut(current, step, is_root)?;
    path_replace_steps(child, &path[1..], replacement, false)
}

fn child_mut<'a>(
    current: &'a mut SemanticJson,
    step: &PathStep,
    is_root: bool,
) -> Result<&'a mut SemanticJson, PatchFailure> {
    match step {
        PathStep::Field(name)
            if is_root
                && matches!(
                    name.as_str(),
                    "body" | "requires" | "ensures" | "attributes"
                ) =>
        {
            object_mut(current)?
                .get_mut(name)
                .ok_or_else(malformed_path)
        }
        PathStep::Field(name) if name == "lhs" || name == "rhs" => {
            let node = term_node_mut(current)?;
            if string_field(node, "kind")? != "rewrite" {
                return Err(malformed_path());
            }
            node.get_mut(if name == "lhs" { "left" } else { "right" })
                .ok_or_else(malformed_path)
        }
        PathStep::Argument(index) => {
            let node = term_node_mut(current)?;
            if string_field(node, "kind")? != "application" {
                return Err(malformed_path());
            }
            array_field_mut(node, "args")?
                .get_mut(to_usize(*index)?)
                .ok_or_else(malformed_path)
        }
        PathStep::SequenceItem(index) => {
            let node = term_node_mut(current)?;
            if string_field(node, "kind")? != "sequence" {
                return Err(malformed_path());
            }
            array_field_mut(node, "items")?
                .get_mut(to_usize(*index)?)
                .ok_or_else(malformed_path)
        }
        PathStep::InjectionTerm => {
            let node = term_node_mut(current)?;
            if string_field(node, "kind")? != "injection" {
                return Err(malformed_path());
            }
            node.get_mut("term").ok_or_else(malformed_path)
        }
        _ => Err(malformed_path()),
    }
}

fn replace_child(
    current: &mut SemanticJson,
    step: &PathStep,
    replacement: SemanticJson,
    is_root: bool,
) -> Result<(), PatchFailure> {
    *child_mut(current, step, is_root)? = replacement;
    Ok(())
}

fn sentence_index(
    definition: &SemanticJson,
) -> Result<BTreeMap<Digest, (usize, usize)>, PatchFailure> {
    let mut result = BTreeMap::new();
    for (module_ordinal, module) in array_field(object(definition)?, "modules")?
        .iter()
        .enumerate()
    {
        for (sentence_ordinal, sentence) in array_field(object(module)?, "sentences")?
            .iter()
            .enumerate()
        {
            let lineage = provenance_digest(sentence, "lineageId")?;
            if result
                .insert(lineage, (module_ordinal, sentence_ordinal))
                .is_some()
            {
                return Err(ill_formed());
            }
        }
    }
    Ok(result)
}

fn module_index(definition: &SemanticJson) -> Result<BTreeMap<String, usize>, PatchFailure> {
    let mut result = BTreeMap::new();
    for (ordinal, module) in array_field(object(definition)?, "modules")?
        .iter()
        .enumerate()
    {
        let name = string_field(object(module)?, "name")?.to_owned();
        if result.insert(name, ordinal).is_some() {
            return Err(ill_formed());
        }
    }
    Ok(result)
}

fn module_at(definition: &SemanticJson, ordinal: usize) -> Result<&SemanticJson, PatchFailure> {
    array_field(object(definition)?, "modules")?
        .get(ordinal)
        .ok_or_else(ill_formed)
}

fn sentence_at(
    definition: &SemanticJson,
    module: usize,
    sentence: usize,
) -> Result<&SemanticJson, PatchFailure> {
    array_field(object(module_at(definition, module)?)?, "sentences")?
        .get(sentence)
        .ok_or_else(ill_formed)
}

fn find_sentence_mut<'a>(
    definition: &'a mut SemanticJson,
    lineage: &Digest,
) -> Result<&'a mut SemanticJson, PatchFailure> {
    let modules = array_field_mut(object_mut(definition)?, "modules")?;
    for module in modules {
        let sentences = array_field_mut(object_mut(module)?, "sentences")?;
        for sentence in sentences {
            if provenance_digest(sentence, "lineageId")? == *lineage {
                return Ok(sentence);
            }
        }
    }
    Err(stale())
}

fn sentence_value(sentence: &SemanticJson) -> Result<&SemanticJson, PatchFailure> {
    object(sentence)?.get("value").ok_or_else(ill_formed)
}

fn sentence_value_mut(sentence: &mut SemanticJson) -> Result<&mut SemanticJson, PatchFailure> {
    object_mut(sentence)?
        .get_mut("value")
        .ok_or_else(ill_formed)
}

fn provenance(sentence: &SemanticJson) -> Result<&SemanticJson, PatchFailure> {
    object(sentence)?.get("provenance").ok_or_else(ill_formed)
}

fn provenance_digest(sentence: &SemanticJson, field: &str) -> Result<Digest, PatchFailure> {
    parse_digest_field(object(provenance(sentence)?)?, field)
}

fn term_sort(term: &SemanticJson) -> Result<&str, PatchFailure> {
    string_field(object(term)?, "sort")
}

fn term_node(term: &SemanticJson) -> Result<&BTreeMap<String, SemanticJson>, PatchFailure> {
    object(object(term)?.get("node").ok_or_else(malformed_path)?)
}

fn term_node_mut(
    term: &mut SemanticJson,
) -> Result<&mut BTreeMap<String, SemanticJson>, PatchFailure> {
    object_mut(
        object_mut(term)?
            .get_mut("node")
            .ok_or_else(malformed_path)?,
    )
}

fn object(value: &SemanticJson) -> Result<&BTreeMap<String, SemanticJson>, PatchFailure> {
    value.as_object().ok_or_else(ill_formed)
}

fn object_mut(
    value: &mut SemanticJson,
) -> Result<&mut BTreeMap<String, SemanticJson>, PatchFailure> {
    match value {
        SemanticJson::Object(fields) => Ok(fields),
        _ => Err(ill_formed()),
    }
}

fn array_field<'a>(
    fields: &'a BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<&'a [SemanticJson], PatchFailure> {
    fields
        .get(name)
        .and_then(SemanticJson::as_array)
        .ok_or_else(ill_formed)
}

fn array_field_mut<'a>(
    fields: &'a mut BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<&'a mut Vec<SemanticJson>, PatchFailure> {
    match fields.get_mut(name) {
        Some(SemanticJson::Array(values)) => Ok(values),
        _ => Err(ill_formed()),
    }
}

fn string_field<'a>(
    fields: &'a BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<&'a str, PatchFailure> {
    fields
        .get(name)
        .and_then(SemanticJson::as_str)
        .ok_or_else(ill_formed)
}

fn parse_digest_field(
    fields: &BTreeMap<String, SemanticJson>,
    name: &str,
) -> Result<Digest, PatchFailure> {
    Digest::parse(string_field(fields, name)?).map_err(|_| ill_formed())
}

fn exact_fields(
    fields: &BTreeMap<String, SemanticJson>,
    expected: &[&str],
) -> Result<(), PatchFailure> {
    let actual: BTreeSet<&str> = fields.keys().map(String::as_str).collect();
    let expected: BTreeSet<&str> = expected.iter().copied().collect();
    if actual == expected {
        Ok(())
    } else {
        Err(ill_formed())
    }
}

fn positive_i64(value: Option<&SemanticJson>) -> Result<i64, PatchFailure> {
    match value.and_then(SemanticJson::as_i64) {
        Some(value) if value > 0 => Ok(value),
        _ => Err(ill_formed()),
    }
}

fn to_i64(value: u64) -> i64 {
    i64::try_from(value).expect("validated v1 ordinal fits signed-64")
}

fn to_usize(value: u64) -> Result<usize, PatchFailure> {
    usize::try_from(value).map_err(|_| malformed_path())
}

fn stale() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::StalePrecondition,
        "immutable-baseline precondition does not hold",
    )
}

fn invalid_position() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::InvalidPosition,
        "insertion position does not agree with its destination",
    )
}

fn no_change() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::NoChange,
        "edit leaves its target unchanged",
    )
}

fn malformed_path() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::MalformedPath,
        "typed original-relative path does not resolve",
    )
}

fn duplicate_target() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::DuplicateTarget,
        "two edits name one target region or insertion slot",
    )
}

fn overlapping() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::OverlappingEdit,
        "edits overlap in original coordinates",
    )
}

fn ill_formed() -> PatchFailure {
    PatchFailure::new(
        PatchFailureKind::LocallyIllFormed,
        "portable local well-formedness failed",
    )
}
