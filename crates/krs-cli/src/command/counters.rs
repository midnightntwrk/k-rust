use krs_ir::measure::Counters;
use krs_ir::{DescriptorBundle, StableText};
use krs_ir_levels::DefinitionSentence;

pub(super) fn count_bundle(counters: &mut Counters, bundle: &DescriptorBundle, bytes: usize) {
    if !counters.is_enabled() {
        return;
    }
    counters.set("bundle.bytes", bytes);
    if let Some(provenance) = counters.get("bundle.provenance_bytes") {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        counters.set("bundle.other_bytes", bytes.saturating_sub(provenance));
    }
    counters.set("descriptors.total", bundle.descriptors().len());
    counters.set("declarations.total", bundle.declarations().len());
    let mut anchors = 0;
    let mut frames = 0;
    for descriptor in bundle.descriptors() {
        counters.add(
            format!(
                "descriptors.kind.{}",
                descriptor.id().item_kind().stable_text()
            ),
            1u64,
        );
        let origins = descriptor.provenance().origins();
        anchors += origins.len();
        frames += origins
            .iter()
            .map(|node| node.origin.frames().len())
            .sum::<usize>();
    }
    counters.set("provenance.anchors", anchors);
    counters.set("provenance.origin_frames", frames);
}

pub(super) fn count_definition(counters: &mut Counters, lowered: &krs_compiler::LoweredDefinition) {
    if !counters.is_enabled() {
        return;
    }
    let definition = lowered.definition();
    counters.set("definition.modules", definition.modules().len());
    let mut sentences = 0;
    for module in definition.modules() {
        sentences += module.sentences().len();
        for sentence in module.sentences() {
            let kind = match sentence {
                DefinitionSentence::SyntaxSort(_) => "syntax_sort",
                DefinitionSentence::Subsort(_) => "subsort",
                DefinitionSentence::Production(_) => "production",
                DefinitionSentence::Precedence(_) => "precedence",
                DefinitionSentence::Associativity(_) => "associativity",
                DefinitionSentence::Configuration(_) => "configuration",
                DefinitionSentence::ContextAlias(_) => "context_alias",
                DefinitionSentence::Rule(_) => "rule",
            };
            counters.add(format!("definition.sentences.{kind}"), 1u64);
        }
    }
    counters.set("definition.sentences", sentences);
    counters.set("definition.symbols", lowered.symbol_map().entries().len());
    counters.set(
        "definition.source_map_entries",
        lowered.source_map().entries().len(),
    );
}
