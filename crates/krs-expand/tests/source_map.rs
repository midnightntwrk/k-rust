//! Prints the whole-file expansion of tour-minimal with its source map and
//! checks the map against the authored anchors the expansion embeds.
//!
//! With `KRS_SOURCE_MAP_EVIDENCE` set to a directory, the test also writes the
//! generated file, its map, the per-surface measurement, and the anchor
//! coverage there; `KRS_WASM_PARSER_PROBE_OUTPUT` names the `observed-wasm-output.json`
//! of the ordinary-Wasm KRS parser probe, whose anchors are then covered too.

mod support;

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::ops::Range;

use krs_expand::sink::{
    AuthoredFile, GeneratedSource, InvocationId, Mapping, MappingClass, PrintReport, Splice,
    lookup, print_with_map, splice_tokens,
};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use sha2::{Digest, Sha256};
use support::{Expansion, TOUR_MINIMAL, TestEnvironment, expand_tour_minimal};

const GENERATED_FILE: &str = "/work/expanded/tour-minimal/src/lib.rs";

/// The printed whole file and, per invocation, its expansion and the report
/// of printing that expansion alone.
struct Printed {
    authored: AuthoredFile,
    source: GeneratedSource,
    surfaces: Vec<Surface>,
}

struct Surface {
    id: InvocationId,
    kind: &'static str,
    output: TokenStream,
    alone: PrintReport,
    none_groups: usize,
}

fn count_none_groups(stream: &TokenStream) -> usize {
    stream
        .clone()
        .into_iter()
        .map(|tree| match tree {
            TokenTree::Group(group) => {
                usize::from(group.delimiter() == Delimiter::None)
                    + count_none_groups(&group.stream())
            }
            _ => 0,
        })
        .sum()
}

/// Registers `nested` under `parent` and returns their splices.
fn splices(
    authored: &AuthoredFile,
    source: &mut GeneratedSource,
    surfaces: &mut Vec<Surface>,
    nested: &[(Vec<usize>, usize, Expansion)],
    parent: InvocationId,
) -> Vec<Splice> {
    nested
        .iter()
        .map(|(at, len, expansion)| {
            let id = register(authored, source, surfaces, expansion, Some(parent));
            Splice {
                at: at.clone(),
                len: *len,
                owner: id,
                tokens: expansion.output.clone(),
                splices: splices(authored, source, surfaces, &expansion.nested, id),
            }
        })
        .collect()
}

/// Records an invocation and checks that printing its expansion alone equals
/// the fallback `Display` and re-lexes to the same tokens.
fn register(
    authored: &AuthoredFile,
    source: &mut GeneratedSource,
    surfaces: &mut Vec<Surface>,
    expansion: &Expansion,
    parent: Option<InvocationId>,
) -> InvocationId {
    let call_site = authored
        .byte_range(expansion.call_site)
        .expect("the call site is authored");
    let replaced = authored
        .byte_range(expansion.replaced)
        .expect("the replaced tokens are authored");
    let id = source.begin_invocation(expansion.kind, call_site, replaced, parent);
    let mut alone = GeneratedSource::new(GENERATED_FILE, authored);
    let alone_id = alone.begin_invocation(expansion.kind, 0..0, 0..0, None);
    let report = print_with_map(&expansion.output, authored, alone_id, &[], &mut alone)
        .expect("the expansion prints");
    assert_eq!(
        alone.text,
        expansion.output.to_string(),
        "{}",
        expansion.kind
    );
    let relexed: TokenStream = alone.text.parse().expect("printed text lexes");
    assert_eq!(
        relexed.to_string(),
        alone.text,
        "{} re-lexes",
        expansion.kind
    );
    surfaces.push(Surface {
        id,
        kind: expansion.kind,
        output: expansion.output.clone(),
        alone: report,
        none_groups: count_none_groups(&expansion.output),
    });
    id
}

fn print_tour_minimal() -> Printed {
    let (authored, expansions) = expand_tour_minimal();
    let mut source = GeneratedSource::new(GENERATED_FILE, &authored);
    let mut surfaces = Vec::new();
    let mut cursor = 0;
    for expansion in &expansions {
        let replaced = authored
            .byte_range(expansion.replaced)
            .expect("the invocation is authored");
        source.copy_authored(&authored, cursor..replaced.start);
        let id = register(&authored, &mut source, &mut surfaces, expansion, None);
        let splices = splices(&authored, &mut source, &mut surfaces, &expansion.nested, id);
        let start = source.text.len();
        print_with_map(&expansion.output, &authored, id, &splices, &mut source)
            .expect("the expansion prints");
        assert_eq!(
            source.text[start..],
            splice_tokens(&expansion.output, &splices).to_string(),
            "{} with nested invocations",
            expansion.kind
        );
        cursor = replaced.end;
    }
    source.copy_authored(&authored, cursor..TOUR_MINIMAL.len());
    surfaces.sort_by_key(|surface| surface.id);
    Printed {
        authored,
        source,
        surfaces,
    }
}

/// Byte offset of a 1-based line and 1-based character column.
fn byte_offset(source: &str, line: u32, column: u32) -> usize {
    let start = source
        .split_inclusive('\n')
        .take(line as usize - 1)
        .map(str::len)
        .sum::<usize>();
    let rest = &source[start..];
    start
        + rest
            .char_indices()
            .nth(column as usize - 1)
            .map_or(rest.len(), |(offset, _)| offset)
}

/// One authored anchor embedded in an expansion's `HostProvenance`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Anchor {
    surface: String,
    role: String,
    ordinal: u32,
    authored: (usize, usize),
    exact: bool,
}

impl Anchor {
    fn range(&self) -> Range<usize> {
        self.authored.0..self.authored.1
    }
}

fn next_after<'a>(text: &'a str, marker: &str) -> Option<&'a str> {
    text.find(marker).map(|index| &text[index + marker.len()..])
}

fn number(text: &str) -> (u32, &str) {
    let digits = text
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(text.len());
    (text[..digits].parse().expect("a number"), &text[digits..])
}

/// Every `HostAuthoredAnchor` of `output`, converted to authored bytes.
fn provenance_anchors(surface: &str, output: &TokenStream) -> Vec<Anchor> {
    let text = output.to_string();
    let mut anchors = Vec::new();
    let mut rest = text.as_str();
    while let Some(after) = next_after(rest, "HostAuthoredAnchor :: new (") {
        let after = next_after(after, "ProvenanceKey :: new (\"").expect("a key");
        let role_end = after.find('"').expect("a role");
        let role = after[..role_end].to_owned();
        let (ordinal, after) = number(&after[role_end + 4..]);
        let after = next_after(after, "HostSourcePosition :: new (").expect("a start");
        let (start_line, after) = number(after);
        let (start_column, after) = number(&after[6..]);
        let after = next_after(after, "HostSourcePosition :: new (").expect("an end");
        let (end_line, after) = number(after);
        let (end_column, after) = number(&after[6..]);
        let after = next_after(after, "AnchorPrecision :: ").expect("a precision");
        anchors.push(Anchor {
            surface: surface.to_owned(),
            role,
            ordinal,
            authored: (
                byte_offset(TOUR_MINIMAL, start_line, start_column),
                byte_offset(TOUR_MINIMAL, end_line, end_column),
            ),
            exact: after.starts_with("Exact"),
        });
        rest = after;
    }
    anchors
}

/// Every generated range that `lookup` maps to exactly `authored`.
fn exact_generated_ranges(printed: &Printed, authored: &Range<usize>) -> Vec<Range<usize>> {
    let segments = printed
        .source
        .map
        .segments
        .iter()
        .filter(|segment| segment.class == MappingClass::ExactAuthored)
        .collect::<Vec<_>>();
    let generated_at = |position: usize, end: bool| {
        segments
            .iter()
            .filter_map(|segment| {
                let range = segment.authored.as_ref()?;
                let inside = if end {
                    range.start < position && position <= range.end
                } else {
                    range.start <= position && position < range.end
                };
                inside.then(|| segment.generated.start + (position - range.start))
            })
            .collect::<Vec<_>>()
    };
    let mut found = Vec::new();
    for start in generated_at(authored.start, false) {
        for end in generated_at(authored.end, true) {
            if start < end
                && matches!(
                    lookup(&printed.source, &printed.authored, start..end),
                    Mapping::ExactAuthored { authored: ref mapped, .. } if mapped == authored
                )
            {
                found.push(start..end);
            }
        }
    }
    found
}

/// Coverage of one anchor: the generated ranges mapping to it exactly, or the
/// class and reason a diagnostic at it would get.
struct Coverage {
    generated: Vec<Range<usize>>,
    class: MappingClass,
    reason: String,
}

/// Generated texts of segments matching `select`, as a readable list.
fn texts(printed: &Printed, select: impl Fn(&krs_expand::sink::Segment) -> bool) -> String {
    let texts = printed
        .source
        .map
        .segments
        .iter()
        .filter(|segment| select(segment))
        .map(|segment| format!("`{}`", &printed.source.text[segment.generated.clone()]))
        .collect::<BTreeSet<_>>();
    texts.into_iter().collect::<Vec<_>>().join(", ")
}

fn coverage(printed: &Printed, anchor: &Range<usize>) -> Coverage {
    let generated = exact_generated_ranges(printed, anchor);
    if !generated.is_empty() {
        return Coverage {
            generated,
            class: MappingClass::ExactAuthored,
            reason: String::new(),
        };
    }
    // A respanned token maps exact-authored to its span through lookup.
    let respanned = printed
        .source
        .map
        .segments
        .iter()
        .filter(|segment| segment.respanned.as_ref() == Some(anchor))
        .map(|segment| segment.generated.clone())
        .filter(|generated| {
            matches!(
                lookup(&printed.source, &printed.authored, generated.clone()),
                Mapping::ExactAuthored { authored: ref mapped, .. } if mapped == anchor
            )
        })
        .collect::<Vec<_>>();
    if !respanned.is_empty() {
        return Coverage {
            generated: respanned,
            class: MappingClass::ExactAuthored,
            reason: format!(
                "rustc-visible only as {}, spanned at this authored range with different text (respanned); lookup maps it exact-authored, where native rustc reports it",
                texts(printed, |segment| segment.respanned.as_ref()
                    == Some(anchor))
            ),
        };
    }
    let reason = if let Some(invocation) = printed
        .source
        .map
        .invocations
        .iter()
        .find(|invocation| invocation.parent.is_some() && invocation.replaced == *anchor)
    {
        format!(
            "call site of the nested `{}` invocation {}; the generated file holds its expansion, and a diagnostic inside it maps to this call site",
            invocation.kind, invocation.id.0
        )
    } else {
        let respanned = texts(printed, |segment| {
            segment.respanned.as_ref() == Some(anchor)
        });
        let overlapping = texts(printed, |segment| {
            segment.respanned.as_ref().is_some_and(|range| {
                range.start < anchor.end && anchor.start < range.end && range != anchor
            })
        });
        if !respanned.is_empty() {
            format!(
                "rustc-visible only as {respanned}, spanned at this authored range with different text (respanned); native rustc reports there"
            )
        } else if !overlapping.is_empty() {
            format!(
                "not emitted as tokens; only {overlapping} is spanned inside this range (respanned); the anchor reaches the collector through HostProvenance"
            )
        } else {
            "not emitted as tokens (no generated token is spanned in this range); the anchor reaches the collector through HostProvenance".to_owned()
        }
    };
    Coverage {
        generated,
        class: MappingClass::InvocationLevel,
        reason,
    }
}

fn check_map(printed: &Printed) {
    let text = &printed.source.text;
    let mut position = 0;
    for segment in &printed.source.map.segments {
        assert_eq!(segment.generated.start, position, "segments are contiguous");
        assert!(
            segment.generated.end > segment.generated.start,
            "segments are nonempty"
        );
        assert_eq!(
            segment.authored.is_some(),
            segment.class == MappingClass::ExactAuthored,
            "only exact-authored segments carry an authored range"
        );
        if let Some(authored) = &segment.authored {
            assert_eq!(
                text[segment.generated.clone()],
                TOUR_MINIMAL[authored.clone()]
            );
        }
        assert_ne!(segment.class, MappingClass::Unmappable);
        position = segment.generated.end;
    }
    assert_eq!(position, text.len(), "segments cover the generated text");
    syn::parse_file(text).expect("the generated file parses");
}

/// Authored ranges that lie outside every invocation map to themselves.
fn check_identity(printed: &Printed, authored: Range<usize>) {
    let segment = printed
        .source
        .map
        .segments
        .iter()
        .find(|segment| {
            segment.owner.is_none()
                && segment
                    .authored
                    .as_ref()
                    .is_some_and(|range| range.start <= authored.start && authored.end <= range.end)
        })
        .unwrap_or_else(|| panic!("{authored:?} is copied unchanged"));
    let offset = segment.generated.start - segment.authored.as_ref().unwrap().start;
    let generated = authored.start + offset..authored.end + offset;
    assert_eq!(
        printed.source.text[generated.clone()],
        TOUR_MINIMAL[authored.clone()]
    );
    assert_eq!(
        lookup(&printed.source, &printed.authored, generated),
        Mapping::ExactAuthored {
            authored,
            owner: None
        }
    );
}

fn line_range(first: usize, last: usize) -> Range<usize> {
    let start = byte_offset(TOUR_MINIMAL, u32::try_from(first).unwrap(), 1);
    let end = byte_offset(TOUR_MINIMAL, u32::try_from(last + 1).unwrap(), 1);
    start..end
}

#[test]
fn tour_minimal_source_map_is_exact_where_tokens_are_authored() {
    let printed = print_tour_minimal();
    check_map(&printed);
    assert!(
        printed
            .surfaces
            .iter()
            .all(|surface| surface.none_groups == 0)
    );
    // Lines 42-44 are comments inside `k::rules!`, whose expansion drops them.
    for (first, last) in [(1, 6), (46, 46), (7, 8), (29, 29)] {
        check_identity(&printed, line_range(first, last));
    }
    let mut anchors = BTreeSet::new();
    for surface in &printed.surfaces {
        anchors.extend(provenance_anchors(surface.kind, &surface.output));
    }
    assert!(!anchors.is_empty());
    for anchor in anchors.iter().filter(|anchor| anchor.exact) {
        let coverage = coverage(&printed, &anchor.range());
        assert!(
            coverage.class == MappingClass::ExactAuthored || !coverage.reason.is_empty(),
            "{anchor:?}"
        );
    }
    if let Ok(directory) = std::env::var("KRS_SOURCE_MAP_EVIDENCE") {
        write_evidence(&printed, &anchors, std::path::Path::new(&directory));
    }
    // Representative authored anchors that rustc sees as authored
    // tokens map exactly.
    for (text, authored) in [
        ("M2Obj", 303..308),
        ("KResult", 310..317),
        ("Foo", 448..451),
        ("k", 557..558),
        ("Object::Foo", 668..679),
    ] {
        assert_eq!(TOUR_MINIMAL[authored.clone()], *text);
        assert!(
            !exact_generated_ranges(&printed, &authored).is_empty(),
            "{text} at {authored:?} maps exactly"
        );
    }
    // The rule's pattern and result are not emitted as tokens; the rule reaches
    // rustc only through variant witnesses spanned at the authored heads.
    for (text, authored, head, witness) in [
        ("Foo()", 800..805, 800..803, "__krs_variant_type_id_Foo"),
        ("Bar()", 809..814, 809..812, "__krs_variant_type_id_Bar"),
    ] {
        assert_eq!(TOUR_MINIMAL[authored.clone()], *text);
        assert!(exact_generated_ranges(&printed, &authored).is_empty());
        assert!(printed.source.map.segments.iter().any(|segment| {
            segment.respanned.as_ref() == Some(&head)
                && printed.source.text[segment.generated.clone()] == *witness
        }));
    }
    // The initializer body contains the nested `k::k!`; rustc spans it as
    // authored code, and so does the map.
    assert!(!exact_generated_ranges(&printed, &(640..693)).is_empty());
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::new(), |mut hex, byte| {
            write!(hex, "{byte:02x}").unwrap();
            hex
        })
}

fn map_json(printed: &Printed) -> serde_json::Value {
    let map = &printed.source.map;
    let range = |range: &Range<usize>| serde_json::json!([range.start, range.end]);
    serde_json::json!({
        "version": map.version,
        "generated_file": map.generated_file,
        "authored_file": map.authored_file,
        "authored_sha256": sha256(TOUR_MINIMAL.as_bytes()),
        "invocations": map.invocations.iter().map(|invocation| serde_json::json!({
            "id": invocation.id.0,
            "kind": invocation.kind,
            "call_site": range(&invocation.call_site),
            "replaced": range(&invocation.replaced),
            "parent": invocation.parent.map(|parent| parent.0),
        })).collect::<Vec<_>>(),
        "segments": map.segments.iter().map(|segment| {
            let mut value = serde_json::json!({
                "generated": range(&segment.generated),
                "class": segment.class.name(),
                "authored": segment.authored.as_ref().map(range),
                "owner": segment.owner.map(|owner| owner.0),
            });
            if let Some(respanned) = &segment.respanned {
                value["respanned"] = range(respanned);
            }
            value
        }).collect::<Vec<_>>(),
    })
}

/// One anchor of the parser probe's `observed-wasm-output.json`.
struct WasmParserProbeAnchor {
    surface: String,
    role: String,
    ordinal: u64,
    authored: Range<usize>,
}

fn wasm_parser_probe_anchors() -> Option<Vec<WasmParserProbeAnchor>> {
    let path = std::env::var("KRS_WASM_PARSER_PROBE_OUTPUT").ok()?;
    let output: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).expect("probe output is readable"))
            .expect("probe output is JSON");
    let mut anchors = Vec::new();
    for invocation in output["invocations"].as_array().expect("invocations") {
        for anchor in invocation["authored_anchors"].as_array().expect("anchors") {
            let at =
                |key: &str| usize::try_from(anchor["authored"][key].as_u64().unwrap()).unwrap();
            anchors.push(WasmParserProbeAnchor {
                surface: invocation["id"].as_str().unwrap().to_owned(),
                role: anchor["role"].as_str().unwrap().to_owned(),
                ordinal: anchor["ordinal"].as_u64().unwrap(),
                authored: at("start")..at("end"),
            });
        }
    }
    Some(anchors)
}

fn toml_string(text: &str) -> String {
    serde_json::to_string(text).unwrap()
}

fn write_evidence(printed: &Printed, anchors: &BTreeSet<Anchor>, directory: &std::path::Path) {
    std::fs::create_dir_all(directory).unwrap();
    let text = &printed.source.text;
    let map = serde_json::to_string_pretty(&map_json(printed)).unwrap() + "\n";
    std::fs::write(directory.join("tour-minimal.expanded.rs"), text).unwrap();
    std::fs::write(directory.join("tour-minimal.map.json"), &map).unwrap();

    std::fs::write(
        directory.join("measurement.generated.toml"),
        measurement(printed, text, &map),
    )
    .unwrap();
    std::fs::write(
        directory.join("anchor-coverage.toml"),
        anchor_coverage(printed, anchors),
    )
    .unwrap();
}

fn measurement(printed: &Printed, text: &str, map: &str) -> String {
    let mut measurement = String::new();
    writeln!(
        measurement,
        "# Generated by crates/krs-expand/tests/source_map.rs (KRS_SOURCE_MAP_EVIDENCE)."
    )
    .unwrap();
    writeln!(measurement, "expanded_rs_bytes = {}", text.len()).unwrap();
    writeln!(
        measurement,
        "expanded_rs_sha256 = {}",
        toml_string(&sha256(text.as_bytes()))
    )
    .unwrap();
    writeln!(
        measurement,
        "map_json_sha256 = {}",
        toml_string(&sha256(map.as_bytes()))
    )
    .unwrap();
    writeln!(
        measurement,
        "segments = {}",
        printed.source.map.segments.len()
    )
    .unwrap();
    let outside = printed
        .source
        .map
        .segments
        .iter()
        .filter(|segment| segment.owner.is_none());
    writeln!(
        measurement,
        "identity_bytes = {}",
        outside
            .map(|segment| segment.generated.len())
            .sum::<usize>()
    )
    .unwrap();
    for surface in &printed.surfaces {
        surface_measurement(printed, surface, &mut measurement);
    }
    measurement
}

fn surface_measurement(printed: &Printed, surface: &Surface, measurement: &mut String) {
    let invocation = &printed.source.map.invocations[surface.id.0];
    let bytes = |class: MappingClass| {
        printed
            .source
            .map
            .segments
            .iter()
            .filter(|segment| segment.owner == Some(surface.id) && segment.class == class)
            .map(|segment| segment.generated.len())
            .sum::<usize>()
    };
    let report = surface.alone;
    writeln!(measurement, "\n[[surface]]").unwrap();
    writeln!(measurement, "invocation = {}", surface.id.0).unwrap();
    writeln!(measurement, "kind = {}", toml_string(surface.kind)).unwrap();
    writeln!(
        measurement,
        "call_site = [{}, {}]",
        invocation.call_site.start, invocation.call_site.end
    )
    .unwrap();
    if let Some(parent) = invocation.parent {
        writeln!(measurement, "parent = {}", parent.0).unwrap();
    }
    writeln!(
        measurement,
        "generated_bytes_exact_authored = {}",
        bytes(MappingClass::ExactAuthored)
    )
    .unwrap();
    writeln!(
        measurement,
        "generated_bytes_invocation_level = {}",
        bytes(MappingClass::InvocationLevel)
    )
    .unwrap();
    writeln!(
        measurement,
        "generated_bytes_generated_only = {}",
        bytes(MappingClass::GeneratedOnly)
    )
    .unwrap();
    writeln!(measurement, "tokens = {}", report.tokens).unwrap();
    writeln!(
        measurement,
        "tokens_exact_authored = {}",
        report.exact_authored
    )
    .unwrap();
    writeln!(
        measurement,
        "tokens_invocation_level = {}",
        report.call_site + report.reparsed + report.respanned
    )
    .unwrap();
    writeln!(
        measurement,
        "tokens_invocation_level_call_site = {}",
        report.call_site
    )
    .unwrap();
    writeln!(
        measurement,
        "tokens_invocation_level_reparsed = {}",
        report.reparsed
    )
    .unwrap();
    writeln!(
        measurement,
        "tokens_invocation_level_respanned = {}",
        report.respanned
    )
    .unwrap();
    writeln!(
        measurement,
        "delimiter_none_groups = {}",
        surface.none_groups
    )
    .unwrap();
}

fn anchor_coverage(printed: &Printed, anchors: &BTreeSet<Anchor>) -> String {
    let mut rows = String::new();
    writeln!(
        rows,
        "# Generated by crates/krs-expand/tests/source_map.rs (KRS_SOURCE_MAP_EVIDENCE)."
    )
    .unwrap();
    let mut write_row = |source: &str,
                         surface: &str,
                         role: &str,
                         ordinal: u64,
                         authored: &Range<usize>,
                         extra: &str| {
        let coverage = coverage(printed, authored);
        writeln!(rows, "\n[[anchor]]").unwrap();
        writeln!(rows, "source = {}", toml_string(source)).unwrap();
        writeln!(rows, "surface = {}", toml_string(surface)).unwrap();
        writeln!(rows, "role = {}", toml_string(role)).unwrap();
        writeln!(rows, "ordinal = {ordinal}").unwrap();
        writeln!(rows, "authored = [{}, {}]", authored.start, authored.end).unwrap();
        writeln!(
            rows,
            "authored_text = {}",
            toml_string(&TOUR_MINIMAL[authored.clone()])
        )
        .unwrap();
        rows.push_str(extra);
        writeln!(rows, "class = {}", toml_string(coverage.class.name())).unwrap();
        match coverage.generated.first() {
            Some(first) => {
                writeln!(rows, "generated = [{}, {}]", first.start, first.end).unwrap();
                writeln!(rows, "generated_occurrences = {}", coverage.generated.len()).unwrap();
                if !coverage.reason.is_empty() {
                    writeln!(rows, "reason = {}", toml_string(&coverage.reason)).unwrap();
                }
            }
            None => writeln!(rows, "reason = {}", toml_string(&coverage.reason)).unwrap(),
        }
    };
    if let Some(probe_anchors) = wasm_parser_probe_anchors() {
        for probe in &probe_anchors {
            let embedded = anchors.iter().any(|anchor| {
                anchor.role == probe.role
                    && u64::from(anchor.ordinal) == probe.ordinal
                    && anchor.range() == probe.authored
            });
            write_row(
                "WasmParserProbe",
                &probe.surface,
                &probe.role,
                probe.ordinal,
                &probe.authored,
                &format!("in_host_provenance = {embedded}\n"),
            );
        }
    }
    for anchor in anchors {
        write_row(
            "HostProvenance",
            &anchor.surface,
            &anchor.role,
            u64::from(anchor.ordinal),
            &anchor.range(),
            &format!(
                "precision = {}\n",
                toml_string(if anchor.exact {
                    "Exact"
                } else {
                    "InvocationFallback"
                })
            ),
        );
    }
    rows
}

/// Diagnostic case D002 (`browser/worker/test/fixtures/diagnostics/unresolved_constructor.rs`,
/// sha256 705c28f3...ebeaa): native rustc reports E0433 at the authored
/// `missing` (bytes 207..214, exact-authored) and D004 at the invocation
/// (183..241, invocation-level). The expansion carries `missing` verbatim, so
/// the map reproduces both classes.
#[test]
fn unresolved_constructor_sort_path_maps_like_native() {
    const SOURCE: &str = "#[k::sort]\npub trait Expr {}\n\n// The first diagnostic selects `missing`; a generated reference check also\n// reports the complete macro invocation through rustc's expansion metadata.\n#[k::constructor(sort = missing::Expr, syntax = \"broken\")]\npub struct Broken;\n\nfn main() {}\n";
    assert_eq!(
        sha256(SOURCE.as_bytes()),
        "705c28f35e9f95938b7b95262ea6da8e9532fc1bf05eceb9b99a5aeceffebeaa"
    );
    let (authored, tokens) =
        AuthoredFile::lex("src/bin/unresolved_constructor.rs", SOURCE).unwrap();
    let file: syn::File = syn::parse2(tokens).unwrap();
    let env = TestEnvironment::new(Some(&authored));
    let mut source = GeneratedSource::new(GENERATED_FILE, &authored);
    let mut cursor = 0;
    for item in &file.items {
        let (mut attrs, entry) = match item {
            syn::Item::Trait(item) => (item.attrs.clone(), krs_expand::AttributeMacro::Sort),
            syn::Item::Struct(item) => {
                (item.attrs.clone(), krs_expand::AttributeMacro::Constructor)
            }
            _ => continue,
        };
        let replaced = authored
            .byte_range(syn::spanned::Spanned::span(item))
            .unwrap();
        let attribute = attrs.remove(0);
        let call_site = syn::spanned::Spanned::span(&attribute);
        let arguments = match &attribute.meta {
            syn::Meta::List(list) => list.tokens.clone(),
            _ => TokenStream::new(),
        };
        let mut stripped = item.clone();
        match &mut stripped {
            syn::Item::Trait(item) => item.attrs = attrs,
            syn::Item::Struct(item) => item.attrs = attrs,
            _ => unreachable!(),
        }
        env.set_call_site(call_site);
        let output = krs_expand::expand_attribute(
            entry,
            &env,
            arguments,
            quote::ToTokens::to_token_stream(&stripped),
        )
        .unwrap();
        source.copy_authored(&authored, cursor..replaced.start);
        let id = source.begin_invocation(
            entry.name(),
            authored.byte_range(call_site).unwrap(),
            replaced.clone(),
            None,
        );
        print_with_map(&output, &authored, id, &[], &mut source).unwrap();
        cursor = replaced.end;
    }
    source.copy_authored(&authored, cursor..SOURCE.len());
    let missing = source
        .map
        .segments
        .iter()
        .filter(|segment| segment.authored == Some(207..214))
        .collect::<Vec<_>>();
    assert!(!missing.is_empty(), "`missing` is copied verbatim");
    for segment in missing {
        assert_eq!(
            lookup(&source, &authored, segment.generated.clone()),
            Mapping::ExactAuthored {
                authored: 207..214,
                owner: Some(InvocationId(1))
            }
        );
    }
    assert_eq!(source.map.invocations[1].call_site, 183..241);
}

/// Prints every expansion of a native per-invocation capture
/// (`KRS_NATIVE_CAPTURE`) through the recording printer. The
/// native text is re-lexed through `proc_macro2`, so this checks the printer's
/// `Display` emulation over the corpus's token shapes, not the map.
#[test]
#[ignore = "needs a native capture; set KRS_NATIVE_CAPTURE"]
fn native_capture_outputs_print_identically() {
    let path = std::env::var("KRS_NATIVE_CAPTURE").expect("KRS_NATIVE_CAPTURE names a capture");
    let capture = std::fs::read_to_string(&path).expect("the native capture is readable");
    let (authored, _) = AuthoredFile::lex("src/lib.rs", "").unwrap();
    let mut rows = 0;
    for line in capture.lines() {
        let row: serde_json::Value = serde_json::from_str(line).expect("a JSON capture row");
        let output: TokenStream = row["output"]
            .as_str()
            .expect("a captured output")
            .parse()
            .expect("native output lexes");
        let mut source = GeneratedSource::new(GENERATED_FILE, &authored);
        let id = source.begin_invocation("captured", 0..0, 0..0, None);
        print_with_map(&output, &authored, id, &[], &mut source).expect("the output prints");
        assert_eq!(source.text, output.to_string(), "{row}");
        rows += 1;
    }
    assert!(rows > 0);
    eprintln!("printed {rows} captured expansions identically");
}
