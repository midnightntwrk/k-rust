//! Project source definitions through a closed origin and sentence policy.

use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use k_rust::definition::{Attributes, FlatModule, ProductionItem, Sentence};

use super::{
    canonical_json,
    normalize::{Normalizer, Options},
    policy::{AttributePolicy, NamePolicy, metadata_attributes},
    reader::{self, DefinitionDocument},
};

type Counter = BTreeMap<String, u64>;
type SentenceCounter = BTreeMap<(String, String), u64>;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireProjectionPolicy {
    module_origins: BTreeMap<String, Option<String>>,
    #[serde(default)]
    sentence_origins: BTreeMap<String, String>,
    #[serde(default)]
    label_map: BTreeMap<String, String>,
    #[serde(default)]
    identity_labels: BTreeSet<String>,
    #[serde(default)]
    sort_map: BTreeMap<String, String>,
    #[serde(default)]
    identity_sorts: BTreeSet<String>,
    #[serde(default)]
    name_map: BTreeMap<String, String>,
    #[serde(default)]
    identity_names: BTreeSet<String>,
    #[serde(default)]
    attribute_value_map: BTreeMap<String, BTreeMap<String, String>>,
    #[serde(default = "metadata_attributes")]
    known_attributes: BTreeSet<String>,
    #[serde(default = "metadata_attributes")]
    metadata_attributes: BTreeSet<String>,
    #[serde(default)]
    imports_by_origin: BTreeMap<String, BTreeSet<String>>,
    #[serde(default)]
    supplemental_module_origins: BTreeMap<String, String>,
    #[serde(default)]
    supplemental_imports_by_origin: BTreeMap<String, BTreeSet<String>>,
    #[serde(default)]
    supplemental_sentence_sha256: Counter,
    #[serde(default)]
    closed_module_prefixes: BTreeSet<String>,
    #[serde(default)]
    redundant_sort_declarations: BTreeSet<String>,
    #[serde(default)]
    redundant_production_klabels: BTreeSet<String>,
    #[serde(default)]
    joined_terminal_productions: BTreeSet<String>,
    #[serde(default)]
    ignored_sentence_sha256: Counter,
}

pub(crate) struct ProjectionPolicy {
    pub(crate) names: NamePolicy,
    pub(crate) attributes: AttributePolicy,
    module_origins: BTreeMap<String, Option<String>>,
    sentence_origins: BTreeMap<String, String>,
    imports_by_origin: BTreeMap<String, BTreeSet<String>>,
    supplemental_module_origins: BTreeMap<String, String>,
    supplemental_imports_by_origin: BTreeMap<String, BTreeSet<String>>,
    supplemental_sentence_sha256: Counter,
    closed_module_prefixes: BTreeSet<String>,
    redundant_sort_declarations: BTreeSet<String>,
    redundant_production_klabels: BTreeSet<String>,
    joined_terminal_productions: BTreeSet<String>,
    ignored_sentence_sha256: Counter,
}

impl ProjectionPolicy {
    pub(crate) fn read(raw: &Value) -> Result<Self, String> {
        let wire: WireProjectionPolicy =
            serde_json::from_value(raw.clone()).map_err(|error| error.to_string())?;
        let policy = Self {
            names: NamePolicy {
                label_map: wire.label_map,
                identity_labels: wire.identity_labels,
                sort_map: wire.sort_map,
                identity_sorts: wire.identity_sorts,
                name_map: wire.name_map,
                identity_names: wire.identity_names,
            },
            attributes: AttributePolicy {
                known_attributes: wire.known_attributes,
                metadata_attributes: wire.metadata_attributes,
                attribute_value_map: wire.attribute_value_map,
            },
            module_origins: wire.module_origins,
            sentence_origins: wire.sentence_origins,
            imports_by_origin: wire.imports_by_origin,
            supplemental_module_origins: wire.supplemental_module_origins,
            supplemental_imports_by_origin: wire.supplemental_imports_by_origin,
            supplemental_sentence_sha256: wire.supplemental_sentence_sha256,
            closed_module_prefixes: wire.closed_module_prefixes,
            redundant_sort_declarations: wire.redundant_sort_declarations,
            redundant_production_klabels: wire.redundant_production_klabels,
            joined_terminal_productions: wire.joined_terminal_productions,
            ignored_sentence_sha256: wire.ignored_sentence_sha256,
        };
        if policy.module_origins.is_empty() {
            return Err("module_origins must not be empty".into());
        }
        if !policy
            .attributes
            .metadata_attributes
            .is_subset(&policy.attributes.known_attributes)
        {
            return Err("every removable metadata attribute must be known".into());
        }
        let origins: BTreeSet<_> = policy
            .module_origins
            .values()
            .flatten()
            .chain(policy.sentence_origins.values())
            .collect();
        let unknown: Vec<_> = policy
            .imports_by_origin
            .keys()
            .filter(|key| !origins.contains(key))
            .collect();
        if !unknown.is_empty() {
            return Err(format!("imports declared for unknown origins: {unknown:?}"));
        }
        let overlap: Vec<_> = policy
            .module_origins
            .keys()
            .filter(|key| policy.supplemental_module_origins.contains_key(*key))
            .collect();
        if !overlap.is_empty() {
            return Err(format!(
                "modules cannot be both compared and supplemental: {overlap:?}"
            ));
        }
        let supplemental_origins: BTreeSet<_> =
            policy.supplemental_module_origins.values().collect();
        let unknown: Vec<_> = policy
            .supplemental_imports_by_origin
            .keys()
            .filter(|key| !supplemental_origins.contains(key))
            .collect();
        if !unknown.is_empty() {
            return Err(format!(
                "supplemental imports declared for unknown origins: {unknown:?}"
            ));
        }
        if policy.closed_module_prefixes.contains("") {
            return Err("closed module prefixes must be nonempty".into());
        }
        Ok(policy)
    }

    fn closed(&self, name: &str) -> bool {
        self.closed_module_prefixes
            .iter()
            .any(|prefix| name.starts_with(prefix))
    }
}

fn digest(value: &Value) -> String {
    format!("{:x}", Sha256::digest(canonical_json(value).as_bytes()))
}

fn string<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value[field]
        .as_str()
        .ok_or_else(|| format!("{field} is not a string"))
}

fn array<'a>(value: &'a Value, field: &str) -> Result<&'a [Value], String> {
    value[field]
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| format!("{field} is not a list"))
}

fn increment(counter: &mut Counter, key: &str) {
    *counter.entry(key.to_owned()).or_default() += 1;
}

fn check_counter(actual: &Counter, expected: &Counter, what: &str) -> Result<(), String> {
    let nonzero = |counter: &Counter| {
        counter
            .iter()
            .filter(|(_, count)| **count != 0)
            .map(|(key, count)| (key.clone(), *count))
            .collect::<Counter>()
    };
    if nonzero(actual) == nonzero(expected) {
        Ok(())
    } else {
        Err(format!(
            "{what} differs: expected={expected:?}, actual={actual:?}"
        ))
    }
}

fn once(names: &BTreeSet<String>) -> Counter {
    names.iter().map(|name| (name.clone(), 1)).collect()
}

fn attributes_value(attributes: &Attributes) -> Value {
    Value::Object(
        attributes
            .wire_entries()
            .map(|(name, value)| (name.to_owned(), value.clone()))
            .collect(),
    )
}

fn normalized_attributes(
    attributes: &Attributes,
    policy: &ProjectionPolicy,
) -> Result<Value, String> {
    let mut attributes = attributes.clone();
    Normalizer::new(Options::source(), &policy.names, &policy.attributes)
        .attributes(&mut attributes)?;
    let mut value = attributes_value(&attributes);
    super::normalize::source_layout(&mut value);
    Ok(value)
}

fn sentence_identity(sentence: &Sentence) -> Result<String, String> {
    let kind = match sentence {
        Sentence::Rule { .. } => "KRule",
        Sentence::Claim { .. } => "KClaim",
        Sentence::Context { .. } => "KContext",
        Sentence::Production {
            label: Some(label), ..
        } => return Ok(format!("KProduction:klabel:{}", label.name)),
        Sentence::Production { sort, .. } => {
            return Ok(format!(
                "KProduction:sort:{}:{}",
                sort.name,
                &digest(&reader::sentence_value(sentence)?)[..16]
            ));
        }
        Sentence::SyntaxSort { sort, .. } => {
            return Ok(format!(
                "KSyntaxSort:sort:{}:{}",
                sort.name,
                &digest(&reader::sentence_value(sentence)?)[..16]
            ));
        }
        Sentence::SyntaxAssociativity { .. } => "KSyntaxAssociativity",
        Sentence::SyntaxPriority { .. } => "KSyntaxPriority",
        _ => return Err("unclassified source sentence".into()),
    };
    if matches!(
        sentence,
        Sentence::Rule { .. } | Sentence::Claim { .. } | Sentence::Context { .. }
    ) && let Some(label) = sentence
        .attributes()
        .get_str("label")
        .filter(|label| !label.is_empty())
    {
        return Ok(format!("{kind}:label:{label}"));
    }
    Ok(format!(
        "{kind}:sha256:{}",
        digest(&reader::sentence_value(sentence)?)
    ))
}

#[derive(Default)]
struct Projection {
    grouped: BTreeMap<String, Vec<Value>>,
    actual_imports: BTreeMap<String, BTreeSet<String>>,
    actual_attributes: BTreeMap<String, Vec<Value>>,
    redundant_sorts: Counter,
    redundant_klabels: Counter,
    joined_terminals: Counter,
    ignored_sentences: Counter,
    supplemental_sentences: Counter,
    supplemental_evidence: Vec<Value>,
}

impl Projection {
    fn origin<'a>(
        identity: &str,
        module_name: &str,
        default_origin: Option<&'a str>,
        policy: &'a ProjectionPolicy,
    ) -> Result<&'a str, String> {
        let qualified = format!("{module_name}::{identity}");
        policy
            .sentence_origins
            .get(&qualified)
            .or_else(|| policy.sentence_origins.get(identity))
            .map(String::as_str)
            .or(default_origin)
            .ok_or_else(|| format!("sentence {qualified} has no explicit semantic origin"))
    }

    fn retain(
        &mut self,
        normalized: &Value,
        supplemental: bool,
        policy: &ProjectionPolicy,
    ) -> bool {
        let hash = digest(normalized);
        if supplemental {
            increment(&mut self.supplemental_sentences, &hash);
            return false;
        }
        if self.ignored_sentences.get(&hash).copied().unwrap_or(0)
            < policy
                .ignored_sentence_sha256
                .get(&hash)
                .copied()
                .unwrap_or(0)
        {
            increment(&mut self.ignored_sentences, &hash);
            return false;
        }
        true
    }

    fn sentence(
        &mut self,
        sentence: &Sentence,
        module_name: &str,
        default_origin: Option<&str>,
        supplemental: bool,
        policy: &ProjectionPolicy,
    ) -> Result<(), String> {
        let identity = sentence_identity(sentence)?;
        let origin = Self::origin(&identity, module_name, default_origin, policy)?;
        let mut sentence = sentence.clone();
        if let Sentence::SyntaxSort { sort, .. } = &sentence
            && policy.redundant_sort_declarations.contains(&sort.name)
        {
            increment(&mut self.redundant_sorts, &sort.name);
            return Ok(());
        }
        if let Sentence::Production { label, items, .. } = &mut sentence
            && let Some(klabel) = label.as_ref().map(|label| label.name.clone())
        {
            if policy.joined_terminal_productions.contains(&klabel) {
                let expected = [
                    ProductionItem::Terminal("#".into()),
                    ProductionItem::Terminal(klabel.clone()),
                ];
                if !items.starts_with(&expected) {
                    return Err(format!(
                        "joined-terminal production shape differs: {klabel:?}"
                    ));
                }
                items.splice(..2, [ProductionItem::Terminal(format!("#{klabel}"))]);
                increment(&mut self.joined_terminals, &klabel);
            }
            if policy.redundant_production_klabels.contains(&klabel) {
                increment(&mut self.redundant_klabels, &klabel);
                *label = None;
            }
        }
        Normalizer::new(Options::source(), &policy.names, &policy.attributes)
            .sentence(&mut sentence)?;
        let mut normalized = reader::sentence_value(&sentence)?;
        super::normalize::source_layout(&mut normalized);
        if !self.retain(&normalized, supplemental, policy) {
            return Ok(());
        }
        if let Sentence::SyntaxPriority { attributes, .. } = &sentence {
            let attributes = json!({"node":"KAtt","att":attributes_value(attributes)});
            for edge in normalized["priorities"]
                .as_array()
                .expect("writer emits priority groups")
                .windows(2)
            {
                self.grouped.entry(origin.to_owned()).or_default().push(json!({"node":"KRS-IMP-SyntaxPriorityEdge","higher":edge[0],"lower":edge[1],"att":attributes}));
            }
        } else {
            self.grouped
                .entry(origin.to_owned())
                .or_default()
                .push(normalized);
        }
        Ok(())
    }

    fn bad_sentence(
        &mut self,
        sentence: &Value,
        module_name: &str,
        default_origin: Option<&str>,
        supplemental: bool,
        policy: &ProjectionPolicy,
    ) -> Result<(), String> {
        let identity = format!("badsentence:sha256:{}", digest(sentence));
        let origin = Self::origin(&identity, module_name, default_origin, policy)?;
        if self.retain(sentence, supplemental, policy) {
            self.grouped
                .entry(origin.to_owned())
                .or_default()
                .push(sentence.clone());
        }
        Ok(())
    }

    fn module(
        &mut self,
        module: &FlatModule,
        bad_sentences: Option<&BTreeMap<usize, Value>>,
        policy: &ProjectionPolicy,
    ) -> Result<(), String> {
        let module_name = &module.name;
        let supplemental_origin = policy.supplemental_module_origins.get(module_name);
        let supplemental = supplemental_origin.is_some();
        let default_origin = supplemental_origin.map(String::as_str).or_else(|| {
            policy
                .module_origins
                .get(module_name)
                .and_then(Option::as_deref)
        });
        let attributes = normalized_attributes(&module.attributes, policy)?;
        if attributes
            .as_object()
            .is_some_and(|attributes| !attributes.is_empty())
        {
            if supplemental {
                return Err(format!(
                    "supplemental module {module_name:?} has unpinned semantic attributes"
                ));
            }
            let origin = default_origin.ok_or_else(|| {
                format!("module {module_name:?} has semantic attributes but no module origin")
            })?;
            self.actual_attributes
                .entry(origin.to_owned())
                .or_default()
                .push(attributes);
        }
        let sentence_count = module.local_sentences.len() + bad_sentences.map_or(0, BTreeMap::len);
        let mut typed = module.local_sentences.iter();
        for index in 0..sentence_count {
            if let Some(bad_sentence) = bad_sentences.and_then(|sentences| sentences.get(&index)) {
                self.bad_sentence(
                    bad_sentence,
                    module_name,
                    default_origin,
                    supplemental,
                    policy,
                )?;
            } else {
                let sentence = typed
                    .next()
                    .ok_or("definition sentence positions are inconsistent")?;
                self.sentence(sentence, module_name, default_origin, supplemental, policy)?;
            }
        }
        let mut imports = BTreeSet::new();
        for imported in &module.imports {
            if policy.closed(&imported.name)
                && !policy.module_origins.contains_key(&imported.name)
                && !policy
                    .supplemental_module_origins
                    .contains_key(&imported.name)
            {
                return Err(format!(
                    "module {module_name:?} imports unclassified closed-namespace module {:?}",
                    imported.name
                ));
            }
            let visibility = if imported.public { "public" } else { "private" };
            imports.insert(format!(
                "{}:{visibility}",
                policy.names.name(&imported.name)?
            ));
        }
        if let Some(origin) = supplemental_origin {
            let expected = policy
                .supplemental_imports_by_origin
                .get(origin)
                .cloned()
                .unwrap_or_default();
            if imports != expected {
                return Err(format!(
                    "supplemental module {module_name:?} imports differ: expected={expected:?}, actual={imports:?}"
                ));
            }
            self.supplemental_evidence
                .push(json!({"module":module_name,"origin":origin,"imports":imports}));
        } else if let Some(origin) = default_origin {
            self.actual_imports
                .entry(origin.to_owned())
                .or_default()
                .extend(imports);
        } else if !imports.is_empty() && policy.imports_by_origin.is_empty() {
            return Err(format!(
                "module {module_name:?} has imports but no origin/import projection"
            ));
        }
        Ok(())
    }

    fn finish(
        mut self,
        policy: &ProjectionPolicy,
        definition_attributes: &Value,
    ) -> Result<Value, String> {
        check_counter(
            &self.redundant_sorts,
            &once(&policy.redundant_sort_declarations),
            "redundant sort declarations",
        )?;
        check_counter(
            &self.redundant_klabels,
            &once(&policy.redundant_production_klabels),
            "redundant production klabels",
        )?;
        check_counter(
            &self.joined_terminals,
            &once(&policy.joined_terminal_productions),
            "joined terminal productions",
        )?;
        check_counter(
            &self.ignored_sentences,
            &policy.ignored_sentence_sha256,
            "ignored sentence multiset",
        )?;
        check_counter(
            &self.supplemental_sentences,
            &policy.supplemental_sentence_sha256,
            "supplemental sentence multiset",
        )?;
        let origins: BTreeSet<_> = self
            .grouped
            .keys()
            .chain(policy.imports_by_origin.keys())
            .cloned()
            .collect();
        let mut projected = Vec::new();
        for origin in origins {
            let mut sentences = self.grouped.remove(&origin).unwrap_or_default();
            sentences.sort_by_cached_key(canonical_json);
            let mut attributes = self.actual_attributes.remove(&origin).unwrap_or_default();
            attributes.sort_by_cached_key(canonical_json);
            let imports = policy
                .imports_by_origin
                .get(&origin)
                .cloned()
                .unwrap_or_else(|| self.actual_imports.remove(&origin).unwrap_or_default());
            projected.push(json!({"origin":origin,"attributes":attributes,"imports":imports,"sentences":sentences}));
        }
        self.supplemental_evidence
            .sort_by_cached_key(canonical_json);
        Ok(
            json!({"format":"KRS-IMP-KAST-PROJECTION","version":1,"definitionAttributes":definition_attributes,
            "origins":projected,"supplementalModules":self.supplemental_evidence,"supplementalSentenceSha256":self.supplemental_sentences}),
        )
    }
}

pub(crate) fn project_definition(
    document: &DefinitionDocument,
    policy: &ProjectionPolicy,
) -> Result<Value, String> {
    let definition = &document.definition;
    let mut all_names = BTreeSet::new();
    let mut matches = Vec::new();
    for (index, module) in definition.modules.iter().enumerate() {
        let name = &module.name;
        if !all_names.insert(name) {
            return Err(format!("duplicate definition module {name:?}"));
        }
        if policy.module_origins.contains_key(name)
            || policy.supplemental_module_origins.contains_key(name)
        {
            matches.push((index, module));
        } else if policy.closed(name) {
            return Err(format!("unclassified closed-namespace module {name:?}"));
        }
    }
    let missing: Vec<_> = policy
        .module_origins
        .keys()
        .chain(policy.supplemental_module_origins.keys())
        .filter(|name| !all_names.contains(*name))
        .collect();
    if !missing.is_empty() {
        return Err(format!("selected modules are absent: {missing:?}"));
    }
    policy.names.name(&definition.main_module)?;
    let definition_attributes = normalized_attributes(&definition.attributes, policy)?;
    let mut projection = Projection::default();
    for (index, module) in matches {
        projection.module(module, document.bad_sentences.get(&index), policy)?;
    }
    projection.finish(policy, &definition_attributes)
}

fn sentences(projection: &Value) -> Result<SentenceCounter, String> {
    let mut counter = SentenceCounter::new();
    for origin in array(projection, "origins")? {
        for sentence in array(origin, "sentences")? {
            *counter
                .entry((
                    string(origin, "origin")?.to_owned(),
                    canonical_json(sentence),
                ))
                .or_default() += 1;
        }
    }
    Ok(counter)
}

fn layout(projection: &Value) -> Value {
    let mut layout = projection.clone();
    if let Some(object) = layout.as_object_mut() {
        object.remove("supplementalModules");
        object.remove("supplementalSentenceSha256");
    }
    if let Some(origins) = layout["origins"].as_array_mut() {
        for origin in origins {
            origin["sentences"] = json!([]);
        }
    }
    layout
}

fn exact_key(
    counter: &SentenceCounter,
    origin: &str,
    wanted: &str,
    count: u64,
    index: usize,
) -> Result<(String, String), String> {
    let matches: Vec<_> = counter
        .iter()
        .filter(|((key_origin, sentence), available)| {
            **available != 0
                && key_origin == origin
                && format!("{:x}", Sha256::digest(sentence.as_bytes())) == wanted
        })
        .collect();
    if matches.len() != 1 || *matches[0].1 < count {
        return Err(format!(
            "compatible sentence pair {index} has no exact count-{count} witness"
        ));
    }
    Ok(matches[0].0.clone())
}

fn multiset_difference(expected: &SentenceCounter, observed: &SentenceCounter) -> String {
    let difference = |left: &SentenceCounter, right: &SentenceCounter| {
        left.iter()
        .filter_map(|((origin, sentence), count)| {
            let extra = count.saturating_sub(right.get(&(origin.clone(), sentence.clone())).copied().unwrap_or_default());
            (extra != 0).then(|| json!({"origin":origin,"count":extra,"sentence":serde_json::from_str::<Value>(sentence).unwrap_or(Value::Null)}))
        }).take(3).collect::<Vec<_>>()
    };
    canonical_json(
        &json!({"missing":difference(expected,observed),"extra":difference(observed,expected)}),
    )
}

/// Compare projections with optional exact compatibility witnesses.
///
/// # Errors
/// Returns an error when layouts, witnessed counts, or remaining sentence multisets differ.
pub(crate) fn compare_definitions(
    baseline: &DefinitionDocument,
    actual: &DefinitionDocument,
    baseline_policy: &ProjectionPolicy,
    actual_policy: &ProjectionPolicy,
    compatible_sentence_pairs: &Value,
) -> Result<Value, String> {
    let expected = project_definition(baseline, baseline_policy)?;
    let observed = project_definition(actual, actual_policy)?;
    if layout(&expected) != layout(&observed) {
        return Err("source-definition non-sentence projection differs".into());
    }
    let mut expected_sentences = sentences(&expected)?;
    let mut observed_sentences = sentences(&observed)?;
    let empty = Vec::new();
    let pairs = if compatible_sentence_pairs.is_null() {
        &empty
    } else {
        compatible_sentence_pairs
            .as_array()
            .ok_or("compatible sentence pairs is not a list")?
    };
    for (index, pair) in pairs.iter().enumerate() {
        let fields = pair
            .as_object()
            .ok_or_else(|| format!("compatible sentence pair {index} is malformed"))?;
        if fields.len() != 4
            || !["origin", "reference_sha256", "actual_sha256", "count"]
                .iter()
                .all(|field| fields.contains_key(*field))
        {
            return Err(format!(
                "compatible sentence pair {index} has unknown fields"
            ));
        }
        let malformed = || format!("compatible sentence pair {index} is malformed");
        let origin = pair["origin"].as_str().ok_or_else(malformed)?;
        let reference = pair["reference_sha256"]
            .as_str()
            .filter(|hash| hash.len() == 64)
            .ok_or_else(malformed)?;
        let actual = pair["actual_sha256"]
            .as_str()
            .filter(|hash| hash.len() == 64)
            .ok_or_else(malformed)?;
        let count = pair["count"]
            .as_u64()
            .filter(|count| *count != 0)
            .ok_or_else(malformed)?;
        let expected_key = exact_key(&expected_sentences, origin, reference, count, index)?;
        *expected_sentences
            .get_mut(&expected_key)
            .ok_or_else(malformed)? -= count;
        let actual_key = exact_key(&observed_sentences, origin, actual, count, index)?;
        *observed_sentences
            .get_mut(&actual_key)
            .ok_or_else(malformed)? -= count;
    }
    expected_sentences.retain(|_, count| *count != 0);
    observed_sentences.retain(|_, count| *count != 0);
    if expected_sentences != observed_sentences {
        return Err(format!(
            "source-definition projection differs: {}",
            multiset_difference(&sentences(&expected)?, &sentences(&observed)?)
        ));
    }
    let sentence_count: usize = array(&expected, "origins")?
        .iter()
        .map(|origin| origin["sentences"].as_array().map_or(0, Vec::len))
        .sum();
    Ok(
        json!({"baseline_sha256":digest(&expected),"actual_sha256":digest(&observed),"sentence_count":sentence_count}),
    )
}

#[cfg(test)]
mod tests {
    use super::digest;

    fn project_definition(definition: &Value, policy: &Value) -> Result<Value, String> {
        let policy = super::ProjectionPolicy::read(policy)?;
        let document = super::reader::definition_document(definition)?;
        super::project_definition(&document, &policy)
    }

    fn compare_definitions(
        baseline: &Value,
        actual: &Value,
        baseline_policy: &Value,
        actual_policy: &Value,
        pairs: &Value,
    ) -> Result<Value, String> {
        let baseline_policy = super::ProjectionPolicy::read(baseline_policy)?;
        let actual_policy = super::ProjectionPolicy::read(actual_policy)?;
        let baseline = super::reader::definition_document(baseline)?;
        let actual = super::reader::definition_document(actual)?;
        super::compare_definitions(&baseline, &actual, &baseline_policy, &actual_policy, pairs)
    }

    fn sentence_identity(sentence: &Value) -> Result<String, String> {
        let definition = definition("REF", json!([sentence]));
        let document = super::reader::definition_document(&definition)?;
        super::sentence_identity(&document.definition.modules[0].local_sentences[0])
    }
    use serde_json::{Value, json};

    fn sort(name: &str) -> Value {
        json!({"node":"KSort","name":name,"params":[]})
    }

    fn apply(name: &str) -> Value {
        json!({"node":"KApply","label":{"node":"KLabel","name":name,"params":[]},"args":[],"arity":0})
    }

    fn rule(name: &str) -> Value {
        json!({"node":"KRule","body":apply(name),"requires":apply("#Top"),"ensures":apply("#Top"),"att":{"node":"KAtt","att":{}}})
    }

    fn priority(groups: Value) -> Value {
        let mut value =
            json!({"node":"KSyntaxPriority","priorities":[],"att":{"node":"KAtt","att":{}}});
        value["priorities"] = groups;
        value
    }

    fn syntax_sort(name: &str) -> Value {
        json!({"node":"KSyntaxSort","sort":sort(name),"params":[],"att":{"node":"KAtt","att":{}}})
    }

    fn definition(name: &str, sentences: Value) -> Value {
        let mut value = json!({"format":"KAST","version":4,"term":{"node":"KDefinition","mainModule":name,
            "modules":[{"node":"KFlatModule","name":name,"imports":[],"localSentences":[],"att":{"node":"KAtt","att":{}}}],
            "att":{"node":"KAtt","att":{}}}});
        value["term"]["modules"][0]["localSentences"] = sentences;
        value
    }

    fn policy(name: &str) -> Value {
        json!({"module_origins":{name:"imp"},"identity_names":[name],"identity_labels":["a","b","c","#Top"],"identity_sorts":["Expr"]})
    }

    fn assert_error(value: Result<Value, String>, expected: &str) {
        assert!(value.unwrap_err().contains(expected));
    }

    #[test]
    fn policy_validation_closes_origins_and_metadata() {
        let definition = definition("REF", json!([{"node":"badsentence"}]));
        let mut policy = policy("REF");
        policy["module_origins"] = json!({});
        assert_error(
            project_definition(&definition, &policy),
            "module_origins must not be empty",
        );
        policy = super::tests::policy("REF");
        policy["known_attributes"] = json!([]);
        assert_error(
            project_definition(&definition, &policy),
            "every removable metadata attribute must be known",
        );
        policy = super::tests::policy("REF");
        policy["imports_by_origin"] = json!({"missing":[]});
        assert_error(
            project_definition(&definition, &policy),
            "imports declared for unknown origins",
        );
        policy = super::tests::policy("REF");
        policy["supplemental_module_origins"] = json!({"REF":"support"});
        assert_error(
            project_definition(&definition, &policy),
            "both compared and supplemental",
        );
        policy = super::tests::policy("REF");
        policy["supplemental_imports_by_origin"] = json!({"missing":[]});
        assert_error(
            project_definition(&definition, &policy),
            "supplemental imports declared for unknown origins",
        );
        policy = super::tests::policy("REF");
        policy["closed_module_prefixes"] = json!([""]);
        assert_error(
            project_definition(&definition, &policy),
            "closed module prefixes must be nonempty",
        );
    }

    #[test]
    fn explicit_maps_close_and_unknown_names_fail() {
        let baseline = definition("REF", json!([rule("a")]));
        let actual = definition("ACT", json!([rule("renamed")]));
        let baseline_policy = policy("REF");
        let mut actual_policy = policy("ACT");
        actual_policy["label_map"] = json!({"renamed":"a"});
        actual_policy["name_map"] = json!({"ACT":"REF"});
        let result = compare_definitions(
            &baseline,
            &actual,
            &baseline_policy,
            &actual_policy,
            &Value::Null,
        )
        .unwrap();
        assert_eq!(result["baseline_sha256"], result["actual_sha256"]);
        assert_eq!(result["sentence_count"], 1);
        actual_policy["label_map"] = json!({});
        assert_error(project_definition(&actual, &actual_policy), "unknown label");
        actual_policy["name_map"] = json!({});
        actual_policy["identity_names"] = json!([]);
        assert_error(project_definition(&actual, &actual_policy), "unknown name");
    }

    #[test]
    fn sentence_fields_and_sort_vocabulary_fail_closed() {
        let mut malformed = definition("REF", json!([rule("a")]));
        malformed["term"]["modules"][0]["localSentences"][0]["mystery"] = json!(true);
        assert!(project_definition(&malformed, &policy("REF")).is_err());
        let unknown_sort = definition("REF", json!([syntax_sort("FutureSort")]));
        assert_error(
            project_definition(&unknown_sort, &policy("REF")),
            "unknown sort",
        );
    }

    #[test]
    fn ignored_context_requires_exact_digest_count_and_heat_cool_witnesses() {
        let context = json!({"node":"KContext","body":apply("a"),"requires":apply("#Top"),"att":{"node":"KAtt","att":{}}});
        let mut reference_policy = policy("REF");
        reference_policy["ignored_sentence_sha256"] = json!({digest(&context):1});
        let reference = definition("REF", json!([context, rule("a"), rule("b")]));
        let actual = definition("REF", json!([rule("a"), rule("b")]));
        let result = compare_definitions(
            &reference,
            &actual,
            &reference_policy,
            &policy("REF"),
            &Value::Null,
        )
        .unwrap();
        assert_eq!(result["sentence_count"], 2);
        let missing_cool = definition("REF", json!([rule("a")]));
        assert_error(
            compare_definitions(
                &reference,
                &missing_cool,
                &reference_policy,
                &policy("REF"),
                &Value::Null,
            ),
            "projection differs",
        );
        for expected in [json!({digest(&context):2}), json!({"wrong":1})] {
            reference_policy["ignored_sentence_sha256"] = expected;
            assert_error(
                project_definition(&reference, &reference_policy),
                "ignored sentence multiset differs",
            );
        }
    }

    #[test]
    fn flattened_module_requires_every_sentence_origin() {
        let definition = definition("REF", json!([rule("a")]));
        let mut policy = policy("REF");
        policy["module_origins"] = json!({"REF":null});
        assert_error(
            project_definition(&definition, &policy),
            "no explicit semantic origin",
        );
        let identity = sentence_identity(&rule("a")).unwrap();
        policy["sentence_origins"] = json!({format!("REF::{identity}"):"imp"});
        assert!(project_definition(&definition, &policy).is_ok());
    }

    #[test]
    fn duplicate_and_owned_modules_fail_closed() {
        let mut definition = definition("REF", json!([rule("a")]));
        let mut policy = policy("REF");
        policy["closed_module_prefixes"] = json!(["OWNED-"]);
        let mut owned = definition["term"]["modules"][0].clone();
        owned["name"] = json!("OWNED-SUPPORT");
        definition["term"]["modules"]
            .as_array_mut()
            .unwrap()
            .push(owned);
        assert_error(
            project_definition(&definition, &policy),
            "unclassified closed-namespace module",
        );
        definition["term"]["modules"][1]["name"] = json!("REF");
        assert!(project_definition(&definition, &policy).is_err());
    }

    #[test]
    fn supplemental_modules_require_exact_attestation() {
        let support_sentence = syntax_sort("Expr");
        let support_digest = digest(&support_sentence);
        let mut definition = definition("REF", json!([rule("a")]));
        let mut policy = policy("REF");
        policy["identity_names"] = json!(["REF", "OWNED-SUPPORT"]);
        policy["closed_module_prefixes"] = json!(["OWNED-"]);
        policy["supplemental_module_origins"] = json!({"OWNED-SUPPORT":"support"});
        policy["supplemental_sentence_sha256"] = json!({&support_digest:1});
        let mut support_module = definition["term"]["modules"][0].clone();
        support_module["name"] = json!("OWNED-SUPPORT");
        support_module["localSentences"] = json!([support_sentence]);
        definition["term"]["modules"]
            .as_array_mut()
            .unwrap()
            .push(support_module);
        let projection = project_definition(&definition, &policy).unwrap();
        assert_eq!(
            projection["supplementalSentenceSha256"],
            json!({support_digest:1})
        );
        definition["term"]["modules"][1]["localSentences"]
            .as_array_mut()
            .unwrap()
            .push(syntax_sort("Expr"));
        assert_error(
            project_definition(&definition, &policy),
            "supplemental sentence multiset differs",
        );
    }

    #[test]
    fn priority_edges_and_redundant_sorts_have_exact_counts() {
        let baseline = definition("REF", json!([priority(json!([["a"], ["b"], ["c"]]))]));
        let mut actual = definition(
            "ACT",
            json!([
                priority(json!([["a"], ["b"]])),
                priority(json!([["b"], ["c"]]))
            ]),
        );
        let mut actual_policy = policy("ACT");
        actual_policy["name_map"] = json!({"ACT":"REF"});
        let result = compare_definitions(
            &baseline,
            &actual,
            &policy("REF"),
            &actual_policy,
            &Value::Null,
        )
        .unwrap();
        assert_eq!(result["sentence_count"], 2);
        actual["term"]["modules"][0]["localSentences"]
            .as_array_mut()
            .unwrap()
            .pop();
        assert_error(
            compare_definitions(
                &baseline,
                &actual,
                &policy("REF"),
                &actual_policy,
                &Value::Null,
            ),
            "projection differs",
        );
        let baseline = definition("REF", json!([{"node":"badsentence"}]));
        let mut actual = definition("ACT", json!([{"node":"badsentence"},syntax_sort("Expr")]));
        actual_policy["redundant_sort_declarations"] = json!(["Expr"]);
        assert!(
            compare_definitions(
                &baseline,
                &actual,
                &policy("REF"),
                &actual_policy,
                &Value::Null
            )
            .is_ok()
        );
        actual["term"]["modules"][0]["localSentences"]
            .as_array_mut()
            .unwrap()
            .push(syntax_sort("Expr"));
        assert_error(
            project_definition(&actual, &actual_policy),
            "redundant sort declarations differ",
        );
    }

    #[test]
    fn ignored_sentences_and_compatible_pairs_require_witnesses() {
        let baseline = definition("REF", json!([rule("a")]));
        let actual = definition("REF", json!([rule("b")]));
        let policy = policy("REF");
        let pairs = json!([{"origin":"imp","reference_sha256":digest(&rule("a")),"actual_sha256":digest(&rule("b")),"count":1}]);
        let result = compare_definitions(&baseline, &actual, &policy, &policy, &pairs).unwrap();
        assert_eq!(result["sentence_count"], 1);
        assert_ne!(result["baseline_sha256"], result["actual_sha256"]);
        let mut invalid = pairs;
        invalid[0]["count"] = json!(2);
        assert_error(
            compare_definitions(&baseline, &actual, &policy, &policy, &invalid),
            "exact count-2 witness",
        );
        invalid[0]["count"] = json!(true);
        assert_error(
            compare_definitions(&baseline, &actual, &policy, &policy, &invalid),
            "malformed",
        );
        let mut ignored = policy;
        ignored["ignored_sentence_sha256"] = json!({"missing":1});
        assert_error(
            project_definition(&baseline, &ignored),
            "ignored sentence multiset differs",
        );
        ignored["ignored_sentence_sha256"] = json!({digest(&rule("a")):1});
        assert!(project_definition(&baseline, &ignored).is_ok());
    }

    #[test]
    fn joined_terminals_and_redundant_klabels_are_exact() {
        let production = json!({"node":"KProduction","sort":sort("Expr"),"params":[],
            "productionItems":[{"node":"KTerminal","value":"#"},{"node":"KTerminal","value":"a"}],
            "klabel":{"node":"KLabel","name":"a","params":[]},"att":{"node":"KAtt","att":{}}});
        let mut policy = policy("REF");
        policy["joined_terminal_productions"] = json!(["a"]);
        policy["redundant_production_klabels"] = json!(["a"]);
        let definition = definition("REF", json!([production]));
        let projection = project_definition(&definition, &policy).unwrap();
        let normalized = &projection["origins"][0]["sentences"][0];
        assert!(normalized.get("klabel").is_none());
        assert_eq!(
            normalized["productionItems"],
            json!([{"node":"KTerminal","value":"#a"}])
        );
        let mut repeated = definition.clone();
        let production = repeated["term"]["modules"][0]["localSentences"][0].clone();
        repeated["term"]["modules"][0]["localSentences"]
            .as_array_mut()
            .unwrap()
            .push(production);
        assert_error(
            project_definition(&repeated, &policy),
            "redundant production klabels differ",
        );
        let mut joined_policy = policy.clone();
        joined_policy["redundant_production_klabels"] = json!([]);
        assert_error(
            project_definition(&repeated, &joined_policy),
            "joined terminal productions differ",
        );
        let mut malformed = definition;
        malformed["term"]["modules"][0]["localSentences"][0]["productionItems"][0]["value"] =
            json!("!");
        assert_error(
            project_definition(&malformed, &policy),
            "joined-terminal production shape differs",
        );
    }

    #[test]
    fn attributes_are_retained_mapped_and_closed() {
        let mut definition = definition("REF", json!([rule("a")]));
        let mut policy = policy("REF");
        policy["known_attributes"] = json!(["label", "custom"]);
        policy["metadata_attributes"] = json!([]);
        policy["attribute_value_map"] = json!({"custom":{"raw":"canonical"}});
        definition["term"]["modules"][0]["localSentences"][0]["att"]["att"] =
            json!({"label":"a","custom":"raw"});
        let projection = project_definition(&definition, &policy).unwrap();
        assert_eq!(
            projection["origins"][0]["sentences"][0]["att"]["att"],
            json!({"label":"a","custom":"canonical"})
        );
        definition["term"]["modules"][0]["localSentences"][0]["att"]["att"]["unknown"] =
            json!(true);
        assert_error(
            project_definition(&definition, &policy),
            "unknown attributes",
        );
    }

    #[test]
    fn imports_and_semantic_module_attributes_are_checked() {
        let mut definition = definition("REF", json!([rule("a")]));
        let mut policy = policy("REF");
        policy["identity_names"] = json!(["REF", "OWNED-SUPPORT"]);
        policy["closed_module_prefixes"] = json!(["OWNED-"]);
        definition["term"]["modules"][0]["imports"] =
            json!([{"node":"KImport","name":"OWNED-SUPPORT","isPublic":true}]);
        assert_error(
            project_definition(&definition, &policy),
            "imports unclassified closed-namespace module",
        );
        definition["term"]["modules"][0]["imports"] = json!([]);
        policy["known_attributes"] = json!(["custom"]);
        policy["metadata_attributes"] = json!([]);
        policy["module_origins"] = json!({"REF":null});
        definition["term"]["modules"][0]["att"]["att"] = json!({"custom":"retained"});
        assert_error(
            project_definition(&definition, &policy),
            "semantic attributes but no module origin",
        );
    }

    #[test]
    fn priority_groups_without_edges_do_not_create_an_origin() {
        let definition = definition("REF", json!([priority(json!([["a"]]))]));
        let projection = project_definition(&definition, &policy("REF")).unwrap();
        assert_eq!(projection["origins"], json!([]));
    }
}
