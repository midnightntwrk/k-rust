//! Stable source identities and provenance shared by the semantic frontend.

use std::{
    collections::BTreeMap,
    ops::Range,
    path::{Path, PathBuf},
    sync::Arc,
};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    definition::{
        Definition, SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE, Sentence,
    },
    kast::{Term, TermMetadata, TermSpan},
};

pub const ORIGIN_ATTRIBUTE: &str = "org.krust.provenance.Origin";

/// Generated leaf categories whose derivation is represented by their nearest parent receipt.
pub const DECLARED_ORIGIN_FREE_NODE_KINDS: [&str; 3] =
    ["primitive-token", "structural-dot", "truth-value"];

/// Relocation-stable identity for one logical source and exact contents.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LogicalSourceId {
    pub logical: String,
    pub content_hash: [u8; 32],
}

impl LogicalSourceId {
    pub fn new(logical: impl Into<String>, contents: &[u8]) -> Self {
        Self {
            logical: logical.into(),
            content_hash: Sha256::digest(contents).into(),
        }
    }

    /// Resolve a project-relative logical name inside one concrete checkout.
    pub fn resolve_under(&self, project_root: impl AsRef<Path>) -> PathBuf {
        project_root.as_ref().join(&self.logical)
    }
}

/// Definition-local index into a [`SourceTable`].
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SourceId(pub usize);

/// One contiguous run of semantic-source bytes retained from a raw source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceOffsetSegment {
    pub semantic_start: usize,
    pub raw_start: usize,
    pub length: usize,
}

/// Relates byte ranges in parsed semantic text to their raw source ranges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceOffsetMap {
    semantic_length: usize,
    raw_length: usize,
    segments: Vec<SourceOffsetSegment>,
}

impl SourceOffsetMap {
    pub fn identity(length: usize) -> Self {
        let segments = (length != 0)
            .then_some(SourceOffsetSegment {
                semantic_start: 0,
                raw_start: 0,
                length,
            })
            .into_iter()
            .collect();
        Self {
            semantic_length: length,
            raw_length: length,
            segments,
        }
    }

    pub fn new(
        semantic_length: usize,
        raw_length: usize,
        segments: Vec<SourceOffsetSegment>,
    ) -> Result<Self, String> {
        let mut semantic_end = 0;
        let mut raw_end = 0;
        for segment in &segments {
            if segment.length == 0
                || segment.semantic_start != semantic_end
                || segment.raw_start < raw_end
            {
                return Err("source offset-map segments are not contiguous and ordered".into());
            }
            semantic_end = segment
                .semantic_start
                .checked_add(segment.length)
                .ok_or_else(|| "source offset-map semantic range overflows usize".to_owned())?;
            raw_end = segment
                .raw_start
                .checked_add(segment.length)
                .ok_or_else(|| "source offset-map raw range overflows usize".to_owned())?;
            if raw_end > raw_length {
                return Err("source offset-map segment exceeds the raw source".into());
            }
        }
        if semantic_end != semantic_length {
            return Err("source offset-map segments do not cover the semantic text".into());
        }
        Ok(Self {
            semantic_length,
            raw_length,
            segments,
        })
    }

    pub fn semantic_length(&self) -> usize {
        self.semantic_length
    }

    pub fn raw_length(&self) -> usize {
        self.raw_length
    }

    pub fn segments(&self) -> &[SourceOffsetSegment] {
        &self.segments
    }

    /// Map one semantic byte boundary to the next retained raw byte boundary.
    pub fn raw_offset(&self, semantic_offset: usize) -> Option<usize> {
        if semantic_offset > self.semantic_length {
            return None;
        }
        if semantic_offset == self.semantic_length {
            return self.segments.last().map_or(Some(0), |segment| {
                segment.raw_start.checked_add(segment.length)
            });
        }
        self.segments.iter().find_map(|segment| {
            let end = segment.semantic_start + segment.length;
            (semantic_offset >= segment.semantic_start && semantic_offset < end)
                .then(|| segment.raw_start + semantic_offset - segment.semantic_start)
        })
    }

    /// Map a half-open semantic range to the minimal half-open raw range containing it.
    pub fn raw_range(&self, semantic: Range<usize>) -> Option<Range<usize>> {
        if semantic.start > semantic.end || semantic.end > self.semantic_length {
            return None;
        }
        let raw_start = self.raw_offset(semantic.start)?;
        if semantic.is_empty() {
            return Some(raw_start..raw_start);
        }
        let final_byte = semantic.end.checked_sub(1)?;
        let segment = self.segments.iter().find(|segment| {
            final_byte >= segment.semantic_start
                && final_byte < segment.semantic_start + segment.length
        })?;
        let raw_end = segment.raw_start + semantic.end - segment.semantic_start;
        Some(raw_start..raw_end)
    }
}

/// Interned logical sources referenced by semantic metadata.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SourceTable {
    sources: Vec<LogicalSourceId>,
    offset_maps: BTreeMap<SourceId, SourceOffsetMap>,
}

impl SourceTable {
    pub fn intern(&mut self, source: LogicalSourceId) -> SourceId {
        if let Some(index) = self
            .sources
            .iter()
            .position(|candidate| candidate == &source)
        {
            return SourceId(index);
        }
        let id = SourceId(self.sources.len());
        self.sources.push(source);
        id
    }

    pub fn get(&self, id: SourceId) -> Option<&LogicalSourceId> {
        self.sources.get(id.0)
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &LogicalSourceId> {
        self.sources.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }

    pub fn set_offset_map(
        &mut self,
        source: SourceId,
        offset_map: SourceOffsetMap,
    ) -> Result<(), String> {
        if self.get(source).is_none() {
            return Err(format!("source id {} is not interned", source.0));
        }
        self.offset_maps.insert(source, offset_map);
        Ok(())
    }

    pub fn offset_map(&self, source: SourceId) -> Option<&SourceOffsetMap> {
        self.offset_maps.get(&source)
    }

    pub fn raw_range(&self, span: TermSpan) -> Option<Range<usize>> {
        self.get(span.source)?;
        if span.start > span.end {
            return None;
        }
        self.offset_map(span.source).map_or_else(
            || Some(span.start..span.end),
            |map| map.raw_range(span.start..span.end),
        )
    }
}

/// Frontend transformation responsible for a generated semantic node.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GeneratingPass {
    ConfigurationExpansion,
    ResolveComm,
    ResolveIo,
    ResolveFun,
    ResolveFunctionWithConfig,
    ResolveStrict,
    ResolveAnonymousVariables,
    ResolveContexts,
    ResolveHeatCool,
    SemanticCasts,
    SubsortKItem,
    ConstantFolding,
    GuardOrPatterns,
    ResolveFreshConfigConstants,
    GenerateSortPredicateSyntax,
    GenerateSortProjections,
    MacroExpansion,
    AddImplicitComputationCell,
    ResolveFreshConstants,
    ConcretizeCells,
    GenerateSortPredicateRules,
    AddSortInjections,
    RemoveUnit,
    MinimizeTermConstruction,
    ModuleToKoreMapCeil,
}

impl GeneratingPass {
    pub const ALL: [Self; 25] = [
        Self::ConfigurationExpansion,
        Self::ResolveComm,
        Self::ResolveIo,
        Self::ResolveFun,
        Self::ResolveFunctionWithConfig,
        Self::ResolveStrict,
        Self::ResolveAnonymousVariables,
        Self::ResolveContexts,
        Self::ResolveHeatCool,
        Self::SemanticCasts,
        Self::SubsortKItem,
        Self::ConstantFolding,
        Self::GuardOrPatterns,
        Self::ResolveFreshConfigConstants,
        Self::GenerateSortPredicateSyntax,
        Self::GenerateSortProjections,
        Self::MacroExpansion,
        Self::AddImplicitComputationCell,
        Self::ResolveFreshConstants,
        Self::ConcretizeCells,
        Self::GenerateSortPredicateRules,
        Self::AddSortInjections,
        Self::RemoveUnit,
        Self::MinimizeTermConstruction,
        Self::ModuleToKoreMapCeil,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ConfigurationExpansion => "configuration-expansion",
            Self::ResolveComm => "resolve-comm",
            Self::ResolveIo => "resolve-io",
            Self::ResolveFun => "resolve-fun",
            Self::ResolveFunctionWithConfig => "resolve-function-with-config",
            Self::ResolveStrict => "resolve-strict",
            Self::ResolveAnonymousVariables => "resolve-anonymous-variables",
            Self::ResolveContexts => "resolve-contexts",
            Self::ResolveHeatCool => "resolve-heat-cool",
            Self::SemanticCasts => "semantic-casts",
            Self::SubsortKItem => "subsort-kitem",
            Self::ConstantFolding => "constant-folding",
            Self::GuardOrPatterns => "guard-or-patterns",
            Self::ResolveFreshConfigConstants => "resolve-fresh-config-constants",
            Self::GenerateSortPredicateSyntax => "generate-sort-predicate-syntax",
            Self::GenerateSortProjections => "generate-sort-projections",
            Self::MacroExpansion => "macro-expansion",
            Self::AddImplicitComputationCell => "add-implicit-computation-cell",
            Self::ResolveFreshConstants => "resolve-fresh-constants",
            Self::ConcretizeCells => "concretize-cells",
            Self::GenerateSortPredicateRules => "generate-sort-predicate-rules",
            Self::AddSortInjections => "add-sort-injections",
            Self::RemoveUnit => "remove-unit",
            Self::MinimizeTermConstruction => "minimize-term-construction",
            Self::ModuleToKoreMapCeil => "module-to-kore-map-ceil",
        }
    }

    /// Resolve the stable wire name of a generating pass.
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|pass| pass.as_str() == name)
    }
}

/// Stable input edge for one generated node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProvenanceLink {
    Source { span: TermSpan },
    Sentence { unique_id: String },
}

/// Stable location of a generated value in its destination sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DestinationAnchor {
    pub module: String,
    pub sentence: String,
    pub sentence_index: u32,
    pub path: Vec<u32>,
}

/// Structured provenance attached to a generated term or sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct OriginRecord {
    pub pass: GeneratingPass,
    /// Immutable derivation links shared by generated descendants with the same origin set.
    pub origins: Arc<[ProvenanceLink]>,
    pub destination: Option<DestinationAnchor>,
}

impl OriginRecord {
    pub fn to_value(&self) -> Value {
        json!({
            "pass": self.pass.as_str(),
            "origins": self.origins.iter().map(link_value).collect::<Vec<_>>(),
            "destination": self.destination.as_ref().map(|destination| json!({
                "module": destination.module,
                "sentence": destination.sentence,
                "sentenceIndex": destination.sentence_index,
                "path": destination.path,
            })),
        })
    }
}

fn link_value(link: &ProvenanceLink) -> Value {
    match link {
        ProvenanceLink::Source { span } => json!({
            "kind": "source",
            "source": span.source.0,
            "start": span.start,
            "end": span.end,
        }),
        ProvenanceLink::Sentence { unique_id } => json!({
            "kind": "sentence",
            "uniqueId": unique_id,
        }),
    }
}

/// Attach one pass's receipts without changing semantic term equality or ordering.
pub fn record_generated_origins(
    before: &Definition,
    mut after: Definition,
    pass: GeneratingPass,
) -> Definition {
    for module in &mut after.modules {
        let before_sentences = before
            .modules
            .iter()
            .find(|candidate| candidate.name == module.name)
            .map(|candidate| candidate.local_sentences.as_slice())
            .unwrap_or_default();
        let module_origins = module_origin_links(before_sentences, pass);
        let counterparts = sentence_counterparts(before_sentences, &module.local_sentences);
        for (sentence_offset, sentence) in module.local_sentences.iter_mut().enumerate() {
            let sentence_index =
                u32::try_from(sentence_offset).expect("module sentence count fits u32");
            let before_sentence =
                counterparts[sentence_offset].map(|index| &before_sentences[index]);
            let generated = before_sentence.is_none_or(|candidate| candidate != sentence);
            let sentence_name = sentence_name(sentence, sentence_offset);
            let mut origins = before_sentence
                .map(sentence_origin_links)
                .unwrap_or_default();
            if origins.is_empty() {
                origins = stored_sentence_origin_links(sentence);
            }
            if origins.is_empty() {
                origins = sentence_source_links(sentence);
            }
            if origins.is_empty() {
                origins.clone_from(&module_origins);
            }
            let origins: Arc<[ProvenanceLink]> = origins.into();
            if generated {
                let record = OriginRecord {
                    pass,
                    origins: Arc::clone(&origins),
                    destination: Some(DestinationAnchor {
                        module: module.name.clone(),
                        sentence: sentence_name.clone(),
                        sentence_index,
                        path: Vec::new(),
                    }),
                };
                sentence
                    .attributes_mut()
                    .insert(ORIGIN_ATTRIBUTE, record.to_value());
            }
            annotate_sentence_terms(
                sentence,
                before_sentence,
                pass,
                &origins,
                &module.name,
                &sentence_name,
                sentence_index,
            );
        }
    }
    after
}

fn sentence_counterparts(before: &[Sentence], after: &[Sentence]) -> Vec<Option<usize>> {
    let mut counterparts = vec![None; after.len()];
    let mut used = vec![false; before.len()];
    for key in ["UNIQUE_ID", "label"] {
        for (after_index, sentence) in after.iter().enumerate() {
            if counterparts[after_index].is_some() {
                continue;
            }
            let Some(value) = sentence.attributes().get_str(key) else {
                continue;
            };
            if after
                .iter()
                .filter(|candidate| candidate.attributes().get_str(key) == Some(value))
                .count()
                != 1
            {
                continue;
            }
            let matching_before = before
                .iter()
                .enumerate()
                .filter(|(_, candidate)| candidate.attributes().get_str(key) == Some(value))
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            if let [before_index] = matching_before.as_slice()
                && !used[*before_index]
            {
                counterparts[after_index] = Some(*before_index);
                used[*before_index] = true;
            }
        }
    }
    for (index, sentence) in after.iter().enumerate() {
        if counterparts[index].is_none()
            && before.get(index).is_some_and(|candidate| {
                !used[index] && sentence_kind(candidate) == sentence_kind(sentence)
            })
        {
            counterparts[index] = Some(index);
            used[index] = true;
        }
    }
    counterparts
}

fn sentence_name(sentence: &Sentence, index: usize) -> String {
    sentence
        .attributes()
        .get_str("UNIQUE_ID")
        .or_else(|| sentence.attributes().get_str("label"))
        .map(str::to_owned)
        .unwrap_or_else(|| format!("{}:{index}", sentence_kind(sentence)))
}

fn sentence_kind(sentence: &Sentence) -> &'static str {
    match sentence {
        Sentence::SyntaxSort { .. } => "syntax-sort",
        Sentence::SortSynonym { .. } => "sort-synonym",
        Sentence::SyntaxLexical { .. } => "syntax-lexical",
        Sentence::Production { .. } => "production",
        Sentence::SyntaxAssociativity { .. } => "syntax-associativity",
        Sentence::SyntaxPriority { .. } => "syntax-priority",
        Sentence::ContextAlias { .. } => "context-alias",
        Sentence::Context { .. } => "context",
        Sentence::Rule { .. } => "rule",
        Sentence::Claim { .. } => "claim",
        Sentence::Configuration { .. } => "configuration",
        Sentence::Bubble { .. } => "bubble",
    }
}

pub(crate) fn sentence_source_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
    let mut links = Vec::new();
    for_each_term(sentence, &mut |term| collect_source_links(term, &mut links));
    links
}

pub(crate) fn sentence_origin_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
    let stored = stored_sentence_origin_links(sentence);
    if !stored.is_empty() {
        stored
    } else if let Some(unique_id) = sentence.attributes().get_str("UNIQUE_ID") {
        vec![ProvenanceLink::Sentence {
            unique_id: unique_id.into(),
        }]
    } else if sentence_is_termless(sentence)
        && let Some(span) = sentence_source_span(sentence)
    {
        vec![ProvenanceLink::Source { span }]
    } else {
        sentence_source_links(sentence)
    }
}

fn sentence_is_termless(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::Bubble { .. }
    )
}

fn sentence_source_span(sentence: &Sentence) -> Option<TermSpan> {
    let attributes = sentence.attributes();
    let start = attributes
        .get(SENTENCE_START_OFFSET_ATTRIBUTE)?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    let end = attributes
        .get(SENTENCE_END_OFFSET_ATTRIBUTE)?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    (start <= end).then_some(TermSpan {
        source: attributes.source_id()?,
        start,
        end,
    })
}

fn stored_sentence_origin_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
    sentence
        .attributes()
        .get(ORIGIN_ATTRIBUTE)
        .and_then(|record| record.get("origins"))
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|link| match link.get("kind").and_then(Value::as_str) {
            Some("source") => Some(ProvenanceLink::Source {
                span: TermSpan {
                    source: SourceId(usize::try_from(link.get("source")?.as_u64()?).ok()?),
                    start: usize::try_from(link.get("start")?.as_u64()?).ok()?,
                    end: usize::try_from(link.get("end")?.as_u64()?).ok()?,
                },
            }),
            Some("sentence") => Some(ProvenanceLink::Sentence {
                unique_id: link.get("uniqueId")?.as_str()?.into(),
            }),
            _ => None,
        })
        .collect()
}

pub(crate) fn seed_generated_sentence_origin(
    sentence: &mut Sentence,
    pass: GeneratingPass,
    origins: Vec<ProvenanceLink>,
) {
    sentence.attributes_mut().insert(
        ORIGIN_ATTRIBUTE,
        OriginRecord {
            pass,
            origins: origins.into(),
            destination: None,
        }
        .to_value(),
    );
}

fn module_origin_links(before_sentences: &[Sentence], pass: GeneratingPass) -> Vec<ProvenanceLink> {
    let configuration_sources = before_sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Configuration { .. }))
        .flat_map(sentence_origin_links)
        .fold(Vec::new(), |mut links, link| {
            push_unique(&mut links, link);
            links
        });
    if pass == GeneratingPass::ConfigurationExpansion && !configuration_sources.is_empty() {
        return configuration_sources;
    }
    before_sentences
        .iter()
        .flat_map(sentence_origin_links)
        .fold(Vec::new(), |mut links, link| {
            push_unique(&mut links, link);
            links
        })
}

fn collect_source_links(term: &Term, links: &mut Vec<ProvenanceLink>) {
    if let Some(span) = term.metadata().and_then(|metadata| metadata.span) {
        push_unique(links, ProvenanceLink::Source { span });
    }
    match term {
        Term::Annotated { term, .. } => collect_source_links(term, links),
        Term::Rewrite { left, right } => {
            collect_source_links(left, links);
            collect_source_links(right, links);
        }
        Term::As { pattern, alias } => {
            collect_source_links(pattern, links);
            collect_source_links(alias, links);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_source_links(item, links);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
    }
}

fn push_unique(links: &mut Vec<ProvenanceLink>, link: ProvenanceLink) {
    if !links.contains(&link) {
        links.push(link);
    }
}

fn for_each_term(sentence: &Sentence, visitor: &mut impl FnMut(&Term)) {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            visitor(body);
            visitor(requires);
            visitor(ensures);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            visitor(body);
            visitor(requires);
        }
        Sentence::Configuration { body, ensures, .. } => {
            visitor(body);
            visitor(ensures);
        }
        _ => {}
    }
}

#[derive(Clone, Copy)]
struct AnnotationContext<'a> {
    pass: GeneratingPass,
    module: &'a str,
    sentence: &'a str,
    sentence_index: u32,
}

fn annotate_sentence_terms(
    sentence: &mut Sentence,
    before: Option<&Sentence>,
    pass: GeneratingPass,
    origins: &Arc<[ProvenanceLink]>,
    module: &str,
    sentence_name: &str,
    sentence_index: u32,
) {
    let context = AnnotationContext {
        pass,
        module,
        sentence: sentence_name,
        sentence_index,
    };
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            annotate_term(body, sentence_term(before, 0), context, origins, vec![0]);
            annotate_term(
                requires,
                sentence_term(before, 1),
                context,
                origins,
                vec![1],
            );
            annotate_term(ensures, sentence_term(before, 2), context, origins, vec![2]);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            annotate_term(body, sentence_term(before, 0), context, origins, vec![0]);
            annotate_term(
                requires,
                sentence_term(before, 1),
                context,
                origins,
                vec![1],
            );
        }
        Sentence::Configuration { body, ensures, .. } => {
            annotate_term(body, sentence_term(before, 0), context, origins, vec![0]);
            annotate_term(ensures, sentence_term(before, 1), context, origins, vec![1]);
        }
        _ => {}
    }
}

fn sentence_term(sentence: Option<&Sentence>, field: u32) -> Option<&Term> {
    match (sentence?, field) {
        (
            Sentence::Rule { body, .. }
            | Sentence::Claim { body, .. }
            | Sentence::Context { body, .. }
            | Sentence::ContextAlias { body, .. }
            | Sentence::Configuration { body, .. },
            0,
        ) => Some(body),
        (
            Sentence::Rule { requires, .. }
            | Sentence::Claim { requires, .. }
            | Sentence::Context { requires, .. }
            | Sentence::ContextAlias { requires, .. },
            1,
        ) => Some(requires),
        (Sentence::Configuration { ensures, .. }, 1)
        | (Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. }, 2) => Some(ensures),
        _ => None,
    }
}

fn annotate_term(
    term: &mut Term,
    before: Option<&Term>,
    context: AnnotationContext<'_>,
    inherited_origins: &Arc<[ProvenanceLink]>,
    path: Vec<u32>,
) {
    if before.is_some_and(|candidate| term == candidate) {
        return;
    }
    let own_origins = term_origin_links(before, term, inherited_origins);
    if !declared_origin_free(term) {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = taken.with_metadata(TermMetadata {
            origin: Some(Arc::new(OriginRecord {
                pass: context.pass,
                origins: Arc::clone(&own_origins),
                destination: Some(DestinationAnchor {
                    module: context.module.into(),
                    sentence: context.sentence.into(),
                    sentence_index: context.sentence_index,
                    path: path.clone(),
                }),
            })),
            ..TermMetadata::default()
        });
    }

    if let Some(before) = before
        && let Some(child) = only_child_mut(term)
        && child == before
    {
        annotate_child(child, Some(before), 0, context, &own_origins, &path);
        return;
    }

    let before = before.map(Term::unannotated);
    match (unannotated_mut(term), before) {
        (
            Term::Rewrite { left, right },
            Some(Term::Rewrite {
                left: before_left,
                right: before_right,
            }),
        ) => {
            annotate_child(left, Some(before_left), 0, context, &own_origins, &path);
            annotate_child(right, Some(before_right), 1, context, &own_origins, &path);
        }
        (
            Term::As { pattern, alias },
            Some(Term::As {
                pattern: before_pattern,
                alias: before_alias,
            }),
        ) => {
            annotate_child(
                pattern,
                Some(before_pattern),
                0,
                context,
                &own_origins,
                &path,
            );
            annotate_child(alias, Some(before_alias), 1, context, &own_origins, &path);
        }
        (Term::Sequence(items), Some(Term::Sequence(before_items)))
        | (
            Term::Apply {
                arguments: items, ..
            },
            Some(Term::Apply {
                arguments: before_items,
                ..
            }),
        ) => {
            for (index, item) in items.iter_mut().enumerate() {
                annotate_child(
                    item,
                    before_items.get(index),
                    u32::try_from(index).expect("term arity fits u32"),
                    context,
                    &own_origins,
                    &path,
                );
            }
        }
        (Term::Rewrite { left, right }, _) => {
            annotate_child(left, None, 0, context, &own_origins, &path);
            annotate_child(right, None, 1, context, &own_origins, &path);
        }
        (Term::As { pattern, alias }, _) => {
            annotate_child(pattern, None, 0, context, &own_origins, &path);
            annotate_child(alias, None, 1, context, &own_origins, &path);
        }
        (
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            },
            _,
        ) => {
            for (index, item) in items.iter_mut().enumerate() {
                annotate_child(
                    item,
                    None,
                    u32::try_from(index).expect("term arity fits u32"),
                    context,
                    &own_origins,
                    &path,
                );
            }
        }
        (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }, _) => {}
        (Term::Annotated { .. }, _) => unreachable!(),
    }
}

fn term_origin_links(
    before: Option<&Term>,
    after: &Term,
    inherited: &Arc<[ProvenanceLink]>,
) -> Arc<[ProvenanceLink]> {
    let before_metadata = before.and_then(Term::metadata);
    let after_metadata = after.metadata();
    let mut links = Vec::new();
    for link in before_metadata
        .and_then(|metadata| metadata.origin.as_deref())
        .into_iter()
        .flat_map(|origin| origin.origins.iter())
        .chain(
            after_metadata
                .and_then(|metadata| metadata.origin.as_deref())
                .into_iter()
                .flat_map(|origin| origin.origins.iter()),
        )
        .cloned()
    {
        push_unique(&mut links, link);
    }
    for span in [
        before_metadata.and_then(|metadata| metadata.span),
        after_metadata.and_then(|metadata| metadata.span),
    ]
    .into_iter()
    .flatten()
    {
        push_unique(&mut links, ProvenanceLink::Source { span });
    }
    if links.is_empty() {
        return Arc::clone(inherited);
    }
    for link in inherited.iter() {
        push_unique(&mut links, link.clone());
    }
    if links == inherited.as_ref() {
        Arc::clone(inherited)
    } else {
        links.into()
    }
}

fn only_child_mut(term: &mut Term) -> Option<&mut Term> {
    match unannotated_mut(term) {
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } if items.len() == 1 => items.first_mut(),
        _ => None,
    }
}

fn unannotated_mut(mut term: &mut Term) -> &mut Term {
    loop {
        match term {
            Term::Annotated { term: inner, .. } => term = inner,
            term => return term,
        }
    }
}

fn annotate_child(
    term: &mut Term,
    before: Option<&Term>,
    child: u32,
    context: AnnotationContext<'_>,
    origins: &Arc<[ProvenanceLink]>,
    parent_path: &[u32],
) {
    let mut path = parent_path.to_vec();
    path.push(child);
    annotate_term(term, before, context, origins, path);
}

/// Primitive tokens and structural dots are deliberately origin-free.
pub fn declared_origin_free(term: &Term) -> bool {
    match term.unannotated() {
        Term::Token { .. } => true,
        Term::Apply { label, arguments }
            if arguments.is_empty() && matches!(label.name.as_str(), "#dots" | "#noDots") =>
        {
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        definition::{Attributes, FlatModule},
        kast::{Sort, TermMetadata},
    };

    fn rule(body: Term) -> Sentence {
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        Sentence::Rule {
            body,
            requires: truth.clone(),
            ensures: truth,
            attributes: Attributes::new([("label".into(), "MAIN.rule".into())].into()),
        }
    }

    fn definition(body: Term) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![rule(body)],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    fn definition_with_rules(rules: Vec<Sentence>) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: rules,
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn changed_node_with_inherited_span_records_the_generating_pass() {
        let span = TermSpan {
            source: SourceId(0),
            start: 10,
            end: 20,
        };
        let annotated = |label| {
            Term::apply(label, Vec::new()).with_metadata(TermMetadata {
                span: Some(span),
                ..TermMetadata::default()
            })
        };
        let before = definition(annotated("before"));
        let after = record_generated_origins(
            &before,
            definition(annotated("after")),
            GeneratingPass::MacroExpansion,
        );
        let Sentence::Rule { body, .. } = &after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };
        let metadata = body.metadata().unwrap();
        let origin = metadata
            .origin
            .as_deref()
            .expect("changed node has an origin");

        assert_eq!(metadata.span, Some(span));
        assert_eq!(origin.pass, GeneratingPass::MacroExpansion);
        assert_eq!(origin.origins.as_ref(), [ProvenanceLink::Source { span }]);
        assert_eq!(
            origin.destination,
            Some(DestinationAnchor {
                module: "MAIN".into(),
                sentence: "MAIN.rule".into(),
                sentence_index: 0,
                path: vec![0],
            }),
        );
    }

    #[test]
    fn generated_descendants_share_identical_origin_link_storage() {
        let span = TermSpan {
            source: SourceId(0),
            start: 10,
            end: 20,
        };
        let before = definition(
            Term::apply("before", Vec::new()).with_metadata(TermMetadata {
                span: Some(span),
                ..TermMetadata::default()
            }),
        );
        let after = record_generated_origins(
            &before,
            definition(Term::apply(
                "after",
                vec![Term::apply("generated-child", Vec::new())],
            )),
            GeneratingPass::MacroExpansion,
        );
        let Sentence::Rule { body, .. } = &after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };
        let parent = body
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("generated parent has an origin");
        let Term::Apply { arguments, .. } = body.unannotated() else {
            panic!("expected application");
        };
        let child = arguments[0]
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("generated child has an origin");

        assert_eq!(parent.origins.as_ref(), [ProvenanceLink::Source { span }]);
        assert_eq!(child.origins, parent.origins);
        assert_eq!(
            child.origins.as_ptr(),
            parent.origins.as_ptr(),
            "identical inherited origin sets must not be cloned into every generated term",
        );
    }

    #[test]
    fn unchanged_bare_node_is_not_claimed_by_a_later_pass() {
        let before = definition(Term::apply("unchanged", vec![Term::variable("X")]));
        let after =
            record_generated_origins(&before, before.clone(), GeneratingPass::AddSortInjections);
        let Sentence::Rule { body, .. } = &after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };

        assert_eq!(body.metadata(), None);
        let Term::Apply { arguments, .. } = body else {
            panic!("expected application");
        };
        assert_eq!(arguments[0].metadata(), None);
    }

    #[test]
    fn changed_node_retains_prior_origin_links_under_the_current_pass() {
        let source = ProvenanceLink::Sentence {
            unique_id: "upstream-rule".into(),
        };
        let prior = Arc::new(OriginRecord {
            pass: GeneratingPass::ConfigurationExpansion,
            origins: vec![source.clone()].into(),
            destination: Some(DestinationAnchor {
                module: "MAIN".into(),
                sentence: "MAIN.rule".into(),
                sentence_index: 0,
                path: vec![0],
            }),
        });
        let with_prior_origin = |label| {
            Term::apply(label, Vec::new()).with_metadata(TermMetadata {
                origin: Some(prior.clone()),
                ..TermMetadata::default()
            })
        };
        let before = definition(with_prior_origin("before"));
        let after = record_generated_origins(
            &before,
            definition(with_prior_origin("after")),
            GeneratingPass::MacroExpansion,
        );
        let Sentence::Rule { body, .. } = &after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };
        let origin = body
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("changed node has an origin");

        assert_eq!(origin.pass, GeneratingPass::MacroExpansion);
        assert_eq!(origin.origins.as_ref(), [source]);
        assert_eq!(
            origin.destination,
            Some(DestinationAnchor {
                module: "MAIN".into(),
                sentence: "MAIN.rule".into(),
                sentence_index: 0,
                path: vec![0],
            }),
        );
    }

    #[test]
    fn term_links_combine_prior_spans_and_inherited_origins_in_order() {
        let sentence = |unique_id: &str| ProvenanceLink::Sentence {
            unique_id: unique_id.into(),
        };
        let before_span = TermSpan {
            source: SourceId(0),
            start: 10,
            end: 20,
        };
        let after_span = TermSpan {
            source: SourceId(0),
            start: 30,
            end: 40,
        };
        let shared = sentence("shared");
        let origin = |links: Vec<ProvenanceLink>| {
            Arc::new(OriginRecord {
                pass: GeneratingPass::ConfigurationExpansion,
                origins: links.into(),
                destination: None,
            })
        };
        let before = Term::apply("before", Vec::new()).with_metadata(TermMetadata {
            span: Some(before_span),
            origin: Some(origin(vec![sentence("before"), shared.clone()])),
            ..TermMetadata::default()
        });
        let after = Term::apply("after", Vec::new()).with_metadata(TermMetadata {
            span: Some(after_span),
            origin: Some(origin(vec![sentence("after"), shared.clone()])),
            ..TermMetadata::default()
        });

        let inherited = vec![shared, sentence("inherited")].into();
        assert_eq!(
            term_origin_links(Some(&before), &after, &inherited).as_ref(),
            [
                sentence("before"),
                sentence("shared"),
                sentence("after"),
                ProvenanceLink::Source { span: before_span },
                ProvenanceLink::Source { span: after_span },
                sentence("inherited"),
            ],
        );
    }

    #[test]
    fn every_generating_pass_has_a_production_emission_site() {
        let emitter_sources = [
            include_str!("definition/configuration.rs"),
            include_str!("kompile/passes.rs"),
            include_str!("kompile/passes/resolve_io.rs"),
            include_str!("kompile/passes/resolve_fun.rs"),
            include_str!("kompile/passes/resolve_function_with_config.rs"),
            include_str!("kompile/passes/resolve_strict.rs"),
            include_str!("kompile/passes/resolve_anon_vars.rs"),
            include_str!("kompile/passes/resolve_contexts.rs"),
            include_str!("kompile/passes/resolve_heat_cool.rs"),
            include_str!("kompile/passes/resolve_semantic_casts.rs"),
            include_str!("kompile/passes/subsort_kitem.rs"),
            include_str!("kompile/passes/constant_folding.rs"),
            include_str!("kompile/passes/guard_or_patterns.rs"),
            include_str!("kompile/passes/resolve_fresh_config_constants.rs"),
            include_str!("kompile/passes/generate_sort_helpers.rs"),
            include_str!("kompile/passes/expand_macros.rs"),
            include_str!("kompile/passes/add_implicit_computation_cell.rs"),
            include_str!("kompile/passes/resolve_fresh_constants.rs"),
            include_str!("kompile/passes/concretize_cells.rs"),
            include_str!("kompile/passes/finalize.rs"),
            include_str!("kompile/sort_injections.rs"),
            include_str!("kompile/passes/remove_unit.rs"),
            include_str!("kompile/passes/minimize_term_construction.rs"),
            include_str!("kompile/module_to_kore.rs"),
        ]
        .map(|source| source.split("\n#[cfg(test)]").next().unwrap())
        .join("\n");

        for pass in GeneratingPass::ALL {
            let variant = format!("GeneratingPass::{pass:?}");
            assert!(
                emitter_sources.contains(&variant),
                "{pass:?} has no production emission site",
            );
        }
    }

    #[test]
    fn duplicate_sentence_keys_do_not_reuse_a_before_counterpart() {
        for key in ["label", "UNIQUE_ID"] {
            let duplicate_attributes = || {
                let mut attributes = Attributes::default();
                attributes.insert(key, Value::String("duplicate".into()));
                attributes
            };
            let make_rule = |body| {
                let mut sentence = rule(Term::apply(body, Vec::new()));
                *sentence.attributes_mut() = duplicate_attributes();
                sentence
            };
            let before = definition_with_rules(vec![make_rule("before"), make_rule("unchanged")]);
            let after = record_generated_origins(
                &before,
                definition_with_rules(vec![make_rule("after"), make_rule("unchanged")]),
                GeneratingPass::MacroExpansion,
            );
            let [
                Sentence::Rule {
                    body: changed_body, ..
                },
                Sentence::Rule {
                    body: unchanged_body,
                    ..
                },
            ] = after.main_module().unwrap().local_sentences.as_slice()
            else {
                panic!("expected two rules");
            };

            assert!(
                changed_body
                    .metadata()
                    .and_then(|metadata| metadata.origin.as_ref())
                    .is_some(),
                "changed node with duplicate {key} has an origin",
            );
            assert_eq!(
                unchanged_body.metadata(),
                None,
                "unchanged node with duplicate {key} is not claimed",
            );
        }
    }

    #[test]
    fn equal_generated_terms_in_duplicate_key_sentences_have_distinct_destinations() {
        for key in ["label", "UNIQUE_ID"] {
            let make_rule = || {
                let mut sentence = rule(Term::apply("generated", Vec::new()));
                sentence
                    .attributes_mut()
                    .insert(key, Value::String("duplicate".into()));
                sentence
            };
            let before = definition_with_rules(Vec::new());
            let after = record_generated_origins(
                &before,
                definition_with_rules(vec![make_rule(), make_rule()]),
                GeneratingPass::ConcretizeCells,
            );
            let destinations = after
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .filter_map(|sentence| match sentence {
                    Sentence::Rule { body, .. } => body
                        .metadata()
                        .and_then(|metadata| metadata.origin.as_deref())
                        .and_then(|origin| origin.destination.as_ref()),
                    _ => None,
                })
                .collect::<Vec<_>>();

            assert_eq!(destinations.len(), 2);
            assert_ne!(
                destinations[0], destinations[1],
                "duplicate {key} sentences have distinct destination occurrences",
            );
        }
    }

    #[test]
    fn duplicate_labels_across_modules_keep_distinct_source_and_destination_identities() {
        let make_rule = |body: Term| {
            let mut sentence = rule(body);
            sentence
                .attributes_mut()
                .insert("label", Value::String("duplicate".into()));
            sentence
        };
        let span = |source, start| TermSpan {
            source: SourceId(source),
            start,
            end: start + 4,
        };
        let module = |name: &str, body| FlatModule {
            name: name.into(),
            imports: Vec::new(),
            local_sentences: vec![make_rule(body)],
            attributes: Attributes::default(),
        };
        let before = Definition {
            main_module: "FIRST".into(),
            modules: vec![
                module(
                    "FIRST",
                    Term::apply("before", Vec::new()).with_metadata(TermMetadata {
                        span: Some(span(0, 10)),
                        ..TermMetadata::default()
                    }),
                ),
                module(
                    "SECOND",
                    Term::apply("before", Vec::new()).with_metadata(TermMetadata {
                        span: Some(span(1, 30)),
                        ..TermMetadata::default()
                    }),
                ),
            ],
            attributes: Attributes::default(),
        };
        let after = Definition {
            main_module: "FIRST".into(),
            modules: vec![
                module("FIRST", Term::apply("generated", Vec::new())),
                module("SECOND", Term::apply("generated", Vec::new())),
            ],
            attributes: Attributes::default(),
        };
        let after = record_generated_origins(&before, after, GeneratingPass::MacroExpansion);
        let receipts = after
            .modules
            .iter()
            .map(|module| {
                let Sentence::Rule { body, .. } = &module.local_sentences[0] else {
                    unreachable!()
                };
                assert_eq!(body, &Term::apply("generated", Vec::new()));
                body.metadata()
                    .and_then(|metadata| metadata.origin.as_deref())
                    .expect("generated term has a receipt")
            })
            .collect::<Vec<_>>();

        assert_eq!(
            receipts[0].origins.as_ref(),
            [ProvenanceLink::Source { span: span(0, 10) }]
        );
        assert_eq!(
            receipts[1].origins.as_ref(),
            [ProvenanceLink::Source { span: span(1, 30) }]
        );
        assert_ne!(receipts[0].origins, receipts[1].origins);
        assert_ne!(receipts[0].destination, receipts[1].destination);
        assert_eq!(receipts[0].destination.as_ref().unwrap().module, "FIRST");
        assert_eq!(receipts[1].destination.as_ref().unwrap().module, "SECOND");
        assert_eq!(receipts[0].destination.as_ref().unwrap().path, [0]);
        assert_eq!(receipts[1].destination.as_ref().unwrap().path, [0]);
    }
}
