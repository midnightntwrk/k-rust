//! Canonical campaign evidence for replay, without executing or classifying a mutant.
//!
//! Replay requires the same kink build and operator code, no fired time bound, and
//! k-rust provenance round-trip and compilation determinism. The normalized report
//! is its canonical JSON text; declared bounds are the only time values.

use crate::{
    Campaign, CampaignManifest, CampaignRun, FinalResult, OracleSide, OracleValue, PatternValue,
    SelectionPolicy, SideRun, TestEvidence, TestRun, tally,
};
use k_rust::{
    definition::{AttributeKey, Sentence},
    kast::Term,
    kore::{ast::Pattern, codec::to_value},
};
use kink_patch::{
    Baseline, CandidateDisposition, CandidateGeneration, Claim, Edit, SentenceFingerprint,
    SentenceOrigin, SentenceRef, apply, canonical_json, fingerprint_payload,
};
use serde_json::{Value, json};

pub const CAMPAIGN_REPORT_VERSION: u64 = 4;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignReport {
    value: Value,
}
impl CampaignReport {
    pub const fn value(&self) -> &Value {
        &self.value
    }
    pub fn text(&self) -> String {
        canonical_json(&self.value)
    }
    /// One baseline row of the report's `baseline` list, `{"test_id", "run"}`, exactly as
    /// [`campaign_report_multi`] encodes it (the report uses this function).
    pub fn baseline_row(evidence: &TestEvidence) -> Result<Value, ReportError> {
        Ok(json!({"test_id":evidence.test_id,"run":side_run(&evidence.run)?}))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReportError {
    MutantCountMismatch,
    ManifestMismatch,
    Encode(String),
}
impl std::fmt::Display for ReportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for ReportError {}
fn encode(e: impl std::fmt::Display) -> ReportError {
    ReportError::Encode(e.to_string())
}
fn enum_name(value: impl std::fmt::Debug) -> String {
    let mut name = String::new();
    for (i, c) in format!("{value:?}").chars().enumerate() {
        if i > 0 && c.is_uppercase() {
            name.push('-');
        }
        name.extend(c.to_lowercase());
    }
    name
}
fn reference(at: &SentenceRef) -> Value {
    json!({"module":at.module,"index":at.index})
}
fn term(term: &Term) -> Result<Value, ReportError> {
    serde_json::from_str(&k_rust::kast::json::to_string(term).map_err(encode)?).map_err(encode)
}
fn nsent(sentence: &Sentence) -> Result<Value, ReportError> {
    serde_json::from_str(&fingerprint_payload(sentence).map_err(encode)?).map_err(encode)
}
fn kore(pattern: &Pattern) -> Result<Value, ReportError> {
    to_value(pattern).map_err(encode)
}
fn oracle_value(value: &OracleValue) -> Result<Value, ReportError> {
    Ok(match value {
        OracleValue::ExitStop(stops) => {
            json!({"exit-stop":stops.iter().map(|stop| json!({"class":enum_name(stop.class),"code":stop.code})).collect::<Vec<_>>()})
        }
        OracleValue::FinalResult(FinalResult::WholeTerm(terms)) => {
            json!({"whole-term":terms.iter().map(kore).collect::<Result<Vec<_>, _>>()?})
        }
        OracleValue::FinalResult(FinalResult::TermPaths(terms)) => {
            json!({"term-paths":terms.iter().map(|paths| paths.iter().map(|(path, term)| Ok(json!({"path":path,"term":kore(term)?}))).collect::<Result<Vec<_>, ReportError>>()).collect::<Result<Vec<_>, _>>()?})
        }
        OracleValue::Pattern(PatternValue::NoMatch) => json!({"pattern":"no-match"}),
        OracleValue::Pattern(PatternValue::Match { bindings }) => {
            json!({"pattern":{"match":bindings.as_ref().map(|tuples| tuples.iter().map(|tuple| tuple.iter().map(|binding| Ok(json!({"name":binding.name,"term":kore(&binding.term)?}))).collect::<Result<Vec<_>, ReportError>>()).collect::<Result<Vec<_>, _>>()).transpose()?}})
        }
    })
}
fn side(side: &OracleSide) -> Result<Value, ReportError> {
    Ok(match side {
        OracleSide::Normal(value) => json!({"normal":oracle_value(value)?}),
        OracleSide::SemanticCrash(pattern) => json!({"semantic-crash":kore(pattern)?}),
        OracleSide::Timeout => json!("timeout"),
        OracleSide::Unknown => json!("unknown"),
        OracleSide::Error => json!("error"),
    })
}
fn side_run(run: &SideRun) -> Result<Value, ReportError> {
    Ok(match run {
        SideRun::Sides { sides } => {
            json!({"sides":sides.iter().map(side).collect::<Result<Vec<_>, _>>()?})
        }
        SideRun::Failed(failure) => json!({"failed":enum_name(failure)}),
    })
}
fn test_run(run: &TestRun) -> Value {
    match run {
        TestRun::Compared(outcomes) => {
            json!({"compared":outcomes.iter().map(enum_name).collect::<Vec<_>>()})
        }
        TestRun::Failed(failure) => json!({"failed":enum_name(failure)}),
        TestRun::SkippedAfterKill => json!("skipped-after-kill"),
    }
}
fn claim(claim: &Claim) -> Value {
    let origin = match &claim.origin {
        SentenceOrigin::Baseline(at) => json!({"baseline":reference(at)}),
        SentenceOrigin::Inserted { edit } => json!({"inserted":edit}),
    };
    json!({"origin":origin,"key":claim.key,"value":claim.value})
}
fn diff(baseline: &Baseline, edit: &Edit, canonical: &Value) -> Result<Value, ReportError> {
    let sentence = |at: &SentenceRef| {
        baseline
            .sentence(at)
            .ok_or_else(|| encode("missing baseline sentence"))
    };
    let (old, new) = match edit {
        Edit::ReplaceTerm {
            at, replacement, ..
        } => (
            term(
                baseline
                    .term(at)
                    .ok_or_else(|| encode("missing baseline term"))?,
            )?,
            term(replacement)?,
        ),
        Edit::ReplaceSentence { at, replacement } => (nsent(sentence(at)?)?, nsent(replacement)?),
        Edit::DeleteSentence { at } => (nsent(sentence(at)?)?, Value::Null),
        Edit::InsertSentence { sentence, .. } => (Value::Null, nsent(sentence)?),
        Edit::AddAttribute { value, .. } => (Value::Null, value.clone()),
        Edit::RemoveAttribute { at, key, .. } => (
            sentence(at)?
                .attributes()
                .get(key)
                .cloned()
                .unwrap_or(Value::Null),
            Value::Null,
        ),
        Edit::ReplaceAttribute {
            at,
            key,
            replacement,
            ..
        } => (
            sentence(at)?
                .attributes()
                .get(key)
                .cloned()
                .unwrap_or(Value::Null),
            replacement.clone(),
        ),
    };
    let at = if matches!(edit, Edit::InsertSentence { .. }) {
        Value::Null
    } else {
        canonical["sentence"].clone()
    };
    Ok(
        json!({"op":canonical["op"],"sentence":at,"path":canonical["path"],"position":canonical["position"],"key":canonical["key"],"old":old,"new":new}),
    )
}

pub fn campaign_report(
    manifest: &CampaignManifest,
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    run: &CampaignRun,
) -> Result<CampaignReport, ReportError> {
    campaign_report_multi(manifest, campaign, std::slice::from_ref(generation), run)
}

pub fn campaign_report_multi(
    manifest: &CampaignManifest,
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    run: &CampaignRun,
) -> Result<CampaignReport, ReportError> {
    if generations.is_empty()
        || generations
            .iter()
            .map(|g| g.candidates().len())
            .sum::<usize>()
            != run.mutants.len()
    {
        return Err(ReportError::MutantCountMismatch);
    }
    let operators = manifest.value()["operators"]
        .as_array()
        .ok_or(ReportError::ManifestMismatch)?;
    if operators.len() != generations.len() {
        return Err(ReportError::ManifestMismatch);
    }
    let mut counts = crate::Tally::default();
    let mut per_operator = Vec::new();
    let mut offset = 0;
    for (operator, generation) in generations.iter().enumerate() {
        let end = offset + generation.candidates().len();
        let statuses = run.mutants[offset..end]
            .iter()
            .map(|m| m.report.status)
            .collect::<Vec<_>>();
        let partial = CampaignRun {
            selection: run.selection,
            baseline: Vec::new(),
            baseline_coverage: Vec::new(),
            mutants: run.mutants[offset..end]
                .iter()
                .cloned()
                .map(|mut mutant| {
                    // Per-operator counts retain every candidate of that generation.
                    mutant.same_as = None;
                    mutant
                })
                .collect(),
            score: generation.scored().then(|| crate::score(&statuses)),
        };
        let count = tally(generation, &partial).ok_or(ReportError::MutantCountMismatch)?;
        counts.rejected_origins += count.rejected_origins;
        per_operator.push(json!({"operator":operator,"tally":tally_value(count),"score":score_value(partial.score)}));
        offset = end;
    }
    let mut distinct_statuses = Vec::new();
    for (index, mutant) in run.mutants.iter().enumerate() {
        if let Some(earlier) = mutant.same_as {
            if earlier.0 >= index || run.mutants[earlier.0].report.status != mutant.report.status {
                return Err(ReportError::ManifestMismatch);
            }
            continue;
        }
        distinct_statuses.push(mutant.report.status);
        match mutant.report.status {
            crate::MutantStatus::Killed => counts.killed += 1,
            crate::MutantStatus::Survived => counts.survived += 1,
            crate::MutantStatus::Equivalent => counts.equivalent += 1,
            crate::MutantStatus::Invalid => counts.invalid += 1,
            crate::MutantStatus::Timeout => counts.timeout += 1,
            crate::MutantStatus::Unknown => counts.unknown += 1,
            crate::MutantStatus::Error => counts.error += 1,
        }
    }
    let expected_score = generations
        .iter()
        .all(|g| g.scored())
        .then(|| crate::score(&distinct_statuses));
    if run.score != expected_score {
        return Err(ReportError::ManifestMismatch);
    }
    if manifest.value()["selection"] != run.selection.value() {
        return Err(ReportError::ManifestMismatch);
    }
    for mutant in &run.mutants {
        match &mutant.plan.selection {
            Some(selection)
                if selection.policy != run.selection || run.selection == SelectionPolicy::None =>
            {
                return Err(ReportError::ManifestMismatch);
            }
            None if run.selection != SelectionPolicy::None
                && mutant.plan.mutant_failure.is_none() =>
            {
                return Err(ReportError::ManifestMismatch);
            }
            _ => {}
        }
    }
    let entries = manifest.value()["mutants"]
        .as_array()
        .ok_or(ReportError::ManifestMismatch)?;
    if entries.len() != run.mutants.len() {
        return Err(ReportError::ManifestMismatch);
    }
    for (index, (entry, (operator, candidate))) in entries
        .iter()
        .zip(
            generations
                .iter()
                .enumerate()
                .flat_map(|(operator, g)| g.candidates().iter().map(move |c| (operator, c))),
        )
        .enumerate()
    {
        if entry["same_as"] != json!(run.mutants[index].same_as.map(|id| id.0)) {
            return Err(ReportError::ManifestMismatch);
        }
        if entry["operator"] != operator {
            return Err(ReportError::ManifestMismatch);
        }
        if entry["patch_sha256"] != candidate.patch.digest().map_err(encode)?.to_string() {
            return Err(ReportError::ManifestMismatch);
        }
    }
    let baseline = campaign.validator.baseline();
    let mut origins = Vec::new();
    let mut mutant_offset = 0;
    let mut origin_offset = 0;
    for (operator, generation) in generations.iter().enumerate() {
        let generated_origins = generation.selected_origins().iter().zip(generation.dispositions()).enumerate().map(|(ordinal, (origin, disposition))| {
        let disposition = match disposition { CandidateDisposition::Mutant(id) => json!({"mutant":id + mutant_offset}), CandidateDisposition::Rejected(f) => json!({"rejected":f.kind().as_str()}) };
        Ok(json!({"ordinal":ordinal + origin_offset,"operator":operator,"site_tuple":origin.site_tuple.iter().map(|at| json!({"module":at.sentence.module,"index":at.sentence.index,"path":at.path.0})).collect::<Vec<_>>(),
            "discovery_tuples":origin.discovery_tuples.iter().map(|tuple| Ok(json!({"sites":tuple.sites.iter().map(|site| json!({"role":site.role,"module":site.at.sentence.module,"index":site.at.sentence.index,"path":site.at.path.0})).collect::<Vec<_>>(),"bindings":tuple.bindings.as_slice().iter().map(|(name, bound)| Ok(json!({"name":name,"term":term(bound)?}))).collect::<Result<Vec<_>, ReportError>>()?}))).collect::<Result<Vec<_>, ReportError>>()?,"disposition":disposition}))
    }).collect::<Result<Vec<_>, ReportError>>()?;
        origin_offset += generated_origins.len();
        origins.extend(generated_origins);
        mutant_offset += generation.candidates().len();
    }
    let mut mutants = Vec::new();
    let mut offset = 0;
    let mut origin_offset = 0;
    for generation in generations {
        for (id, ((candidate, mutant_run), entry)) in generation
            .candidates()
            .iter()
            .zip(&run.mutants[offset..offset + generation.candidates().len()])
            .zip(&entries[offset..offset + generation.candidates().len()])
            .enumerate()
        {
            if mutant_run.report.mutant_id.0 != offset + id
                || mutant_run.operator != candidate.operator
            {
                return Err(ReportError::ManifestMismatch);
            }
            let output = apply(baseline, &candidate.patch).map_err(encode)?;
            let output_sentence = |at: &SentenceRef| {
                output
                    .definition()
                    .modules
                    .iter()
                    .find(|m| m.name == at.module)
                    .and_then(|m| m.local_sentences.get(at.index as usize))
                    .map(std::sync::Arc::as_ref)
                    .ok_or_else(|| encode("missing output sentence"))
            };
            let affected = mutant_run.written_sentences.iter().map(|at| {
            let sentence = baseline.sentence(at).ok_or_else(|| encode("missing baseline sentence"))?;
            let attrs = sentence.attributes();
            let new = output.origins().iter().find(|(_, origin)| **origin == SentenceOrigin::Baseline(at.clone())).map(|(out, _)| SentenceFingerprint::of(output_sentence(out)?).map(|f| f.to_string()).map_err(encode)).transpose()?;
            Ok(json!({"module":at.module,"index":at.index,"label":attrs.string(AttributeKey::Label),"source":attrs.source(),"location":attrs.location().map(|l| [l.start_line,l.start_column,l.end_line,l.end_column]),"old_fingerprint":baseline.fingerprint(at).map_err(encode)?.to_string(),"new_fingerprint":new}))
        }).collect::<Result<Vec<_>, ReportError>>()?;
            let inserted = output.origins().iter().filter(|(_, origin)| matches!(origin, SentenceOrigin::Inserted { .. })).map(|(at, _)| Ok(json!({"module":at.module,"index":at.index,"fingerprint":SentenceFingerprint::of(output_sentence(at)?).map_err(encode)?.to_string()}))).collect::<Result<Vec<_>, ReportError>>()?;
            let patch = candidate.patch.canonical_value().map_err(encode)?;
            let edits = patch["edits"]
                .as_array()
                .ok_or_else(|| encode("missing canonical edits"))?;
            let diffs = candidate
                .patch
                .edits()
                .iter()
                .zip(edits)
                .map(|(edit, canonical)| diff(baseline, edit, canonical))
                .collect::<Result<Vec<_>, _>>()?;
            let tests = mutant_run.plan.tests.iter().map(|test| Ok(json!({"test_id":test.test_id,"run":test_run(&test.run),"mutant":mutant_run.evidence.iter().find(|e| e.test_id == test.test_id).map(|e| side_run(&e.run)).transpose()?}))).collect::<Result<Vec<_>, ReportError>>()?;
            mutants.push(json!({"mutant_id":mutant_run.report.mutant_id.0,"operator":mutant_run.operator,"origins":generation.dispositions().iter().enumerate().filter_map(|(ordinal, d)| (*d == CandidateDisposition::Mutant(id)).then_some(ordinal + origin_offset)).collect::<Vec<_>>(),"patch_sha256":entry["patch_sha256"],"canonical_patch":patch,"affected_sentences":affected,"inserted_sentences":inserted,"diff":diffs,"status":enum_name(mutant_run.report.status),"mutant_failure":mutant_run.plan.mutant_failure.map(enum_name),"executed_test_ids":mutant_run.report.executed_test_ids,"killing_test_ids":mutant_run.report.killing_test_ids,"skipped_test_ids":mutant_run.report.skipped_test_ids,"tests":tests,"selection":mutant_run.plan.selection.as_ref().map(|selection| selection.value()),"claims":{"withdrawn":mutant_run.plan.claims.withdrawn.iter().map(claim).collect::<Vec<_>>(),"unsupported":mutant_run.plan.claims.unsupported.iter().map(claim).collect::<Vec<_>>()}}));
        }
        offset += generation.candidates().len();
        origin_offset += generation.selected_origins().len();
    }
    let baseline_runs = run
        .baseline
        .iter()
        .map(CampaignReport::baseline_row)
        .collect::<Result<Vec<_>, ReportError>>()?;
    let coverage = match run.selection {
        SelectionPolicy::None => Value::Null,
        SelectionPolicy::Prioritize(_) => Value::Array(
            run.baseline_coverage
                .iter()
                .map(|coverage| coverage.value())
                .collect(),
        ),
    };
    let score = run.score.map(|s| json!({"killed":s.killed,"survived":s.survived,"denominator":s.denominator,"ratio":s.ratio.map(|r| json!({"numerator":r.numerator,"denominator":r.denominator}))}));
    Ok(CampaignReport {
        value: json!({"schema":"kink-campaign-report","version":CAMPAIGN_REPORT_VERSION,"manifest_sha256":manifest.digest().to_string(),"manifest":manifest.value(),"baseline":baseline_runs,"coverage":coverage,"origins":origins,"mutants":mutants,"summary":{"tally":{"killed":counts.killed,"survived":counts.survived,"equivalent":counts.equivalent,"invalid":counts.invalid,"timeout":counts.timeout,"unknown":counts.unknown,"error":counts.error,"rejected_origins":counts.rejected_origins},"score":score,"per_operator":per_operator}}),
    })
}

fn tally_value(counts: crate::Tally) -> Value {
    json!({"killed":counts.killed,"survived":counts.survived,"equivalent":counts.equivalent,"invalid":counts.invalid,"timeout":counts.timeout,"unknown":counts.unknown,"error":counts.error,"rejected_origins":counts.rejected_origins})
}
fn score_value(score: Option<crate::Score>) -> Value {
    score.map(|s| json!({"killed":s.killed,"survived":s.survived,"denominator":s.denominator,"ratio":s.ratio.map(|r| json!({"numerator":r.numerator,"denominator":r.denominator}))})).unwrap_or(Value::Null)
}
