//! Deterministic construction and rendering of the workspace algorithm graph.
//!
//! Known limits (review of ce7bb649, not fixed by AG-20):
//!
//! - Finding 5: a card fence that is never closed is dropped without a failure or a report line.
//! - Finding 6: only line doc comments hold cards; `/** */`, `/*! */`, and `#[doc = include_str!(..)]` cards are ignored silently.
//! - Finding 7: an `impl Name` or `Name::method` site counts trait impls too, so it is ambiguous when `Name` also has trait impls.
//! - Finding 8: a type path resolves by crate and last segment only; the module path is ignored and function-local types are indexed.
//! - Finding 13: the raw-span rule matches only `info_span!("algo", ..)`; `info_span!(target: .., "algo", ..)` and `span!(Level::INFO, "algo", ..)` pass the gate.
//! - Finding 17: a stage `call` matches the last `::` segment of any site in any crate, so an unrelated `Foo::call` site gets a `contains` edge.
//! - Finding 19: drift aborts on one invalid card or unparsable changed file, never checks `algorithm-contract` cards, and compares only the first item of a repeated site name.

mod atlas;
mod cards;
mod coverage;
mod diff;
mod drift;
mod html;
mod join;
mod map;
mod model;
pub mod query;
mod render;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs, io,
    path::{Path, PathBuf},
};

pub use atlas::{
    AMDAHL_RULE, ATLAS_SCHEMA_VERSION, Atlas, AtlasIndex, CUT_RULE, CounterFit, Fit,
    INDEX_SCHEMA_VERSION, IndexReceipt, Ladder, LadderRow, LoadedReceipt, MatrixRow, MovedCounter,
    NESTING_RULE, NestLine, Nesting, Rules, SHARE_RULE, SLOPE_RULE, STALENESS_RULE, ShareRow,
    StaleAlgorithm, Staleness, WorkloadCost, amdahl_ceiling, atlas, check_staleness, fit_power_law,
    read_atlas_index, receipt_graph,
};
use cards::{Card, CardKind, Representation, SourceIndex};
pub use coverage::{
    COVERAGE_SCHEMA_VERSION, Coverage, CoveredFile, CoveredFunction, canonical_coverage_toml,
    normalize_export, read_coverage,
};
pub use diff::{
    AlgorithmDelta, ChangedCount, CountDelta, DIFF_RULE, DiffAnswer, Side, Spread, TimeClass,
    TimeDelta, VerdictChange, diff, read_join_file,
};
pub use drift::{DriftFinding, DriftReport, drift, render_drift};
pub use html::{HTML_DATA_ELEMENT_ID, render_html};
pub use join::{
    AGGREGATION_RULE, AlgorithmCounter, AlgorithmRun, EdgeRun, JOIN_SCHEMA_VERSION, Join, NodeRun,
    ObservedContain, ObservedEdge, PhaseRun, Receipt, ReceiptCounter, Revision, Summary,
    ToolVersion, VERDICT_RULE, Verdict, canonical_join_toml, edge_verdict_rule, join_files,
    render_run_overlay,
};
use k_rust::kompile::pipeline::{
    EMISSION_PHASES, LOAD_PHASES, StageDescription, prologue_descriptions, stage_descriptions,
};
use k_rust_kore::measure::{Algorithm, Counter};
pub use map::{MAP_COMMAND, MAP_PATH, render_map};
pub use model::{Anchor, Cost, Edge, Graph, Node};
pub use render::{
    Filters, render_composition, render_composition_focus, render_module_map, render_pipeline,
};

/// A graph and the non-fatal resolution findings collected while building it.
#[derive(Clone, Debug, Default)]
pub struct Build {
    pub graph: Graph,
    /// Violations of the source-card contract. The workspace freshness test rejects these.
    pub failures: Vec<String>,
    /// Advisory coverage findings. These are deliberately printed but never asserted.
    pub report: Vec<String>,
}

/// An error that prevents the input tree from being read or the graph from being serialized.
#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Toml(toml::ser::Error),
    TomlDeserialize(toml::de::Error),
    Json(serde_json::Error),
    Invalid(String),
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => error.fmt(formatter),
            Self::Toml(error) => error.fmt(formatter),
            Self::TomlDeserialize(error) => error.fmt(formatter),
            Self::Json(error) => error.fmt(formatter),
            Self::Invalid(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Toml(error) => Some(error),
            Self::TomlDeserialize(error) => Some(error),
            Self::Json(error) => Some(error),
            Self::Invalid(_) => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}

impl From<toml::ser::Error> for Error {
    fn from(value: toml::ser::Error) -> Self {
        Self::Toml(value)
    }
}

impl From<toml::de::Error> for Error {
    fn from(value: toml::de::Error) -> Self {
        Self::TomlDeserialize(value)
    }
}

impl From<serde_json::Error> for Error {
    fn from(value: serde_json::Error) -> Self {
        Self::Json(value)
    }
}

/// Return the workspace root: the nearest ancestor of the current directory whose `Cargo.toml`
/// declares `[workspace]`, or else the workspace that built this binary.
pub fn workspace_root() -> PathBuf {
    std::env::current_dir()
        .ok()
        .and_then(|directory| find_workspace_root(&directory))
        .or_else(|| find_workspace_root(Path::new(env!("CARGO_MANIFEST_DIR"))))
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(Path::parent)
                .expect("algo-graph is under crates/algo-graph")
                .to_owned()
        })
}

fn find_workspace_root(start: &Path) -> Option<PathBuf> {
    start.ancestors().find_map(|directory| {
        let manifest = fs::read_to_string(directory.join("Cargo.toml")).ok()?;
        let manifest = toml::from_str::<toml::Table>(&manifest).ok()?;
        manifest
            .contains_key("workspace")
            .then(|| directory.to_owned())
    })
}

/// Build the static graph from source cards and linked registries.
///
pub fn build_graph(root: &Path) -> Result<Build, Error> {
    let mut failures = Vec::new();
    let mut report = Vec::new();
    let (cards, index) = cards::read_cards(root, &mut failures)?;
    let algorithm_registry = Algorithm::ALL
        .iter()
        .map(|algorithm| (algorithm.as_str().to_owned(), format!("{algorithm:?}")))
        .collect::<BTreeMap<_, _>>();
    let counter_registry = Counter::ALL
        .iter()
        .map(|counter| (format!("{counter:?}"), counter.name().to_owned()))
        .collect::<BTreeMap<_, _>>();

    let mut nodes = BTreeMap::<(String, String), Node>::new();
    let mut edges = Vec::new();
    for (id, variant) in &algorithm_registry {
        insert_node(
            &mut nodes,
            Node {
                kind: "algorithm".to_owned(),
                id: id.clone(),
                provenance: "table".to_owned(),
                anchor: Anchor {
                    crate_name: "k-rust-kore".to_owned(),
                    file: "crates/k-rust-kore/src/measure.rs".to_owned(),
                    symbol: format!("Algorithm::{variant}"),
                },
                area: area(id),
                name: None,
                sites: Vec::new(),
                cost: Vec::new(),
                variable: None,
                invariant: None,
                no_counter: None,
                span: None,
                table: Some("Algorithm::ALL".to_owned()),
                call: None,
                behavior: None,
                generating_passes: Vec::new(),
                type_path: None,
                role: None,
                registry_name: Some(variant.clone()),
                sequence: None,
            },
        );
    }
    for (variant, name) in &counter_registry {
        insert_node(
            &mut nodes,
            Node {
                kind: "observation".to_owned(),
                id: counter_id(variant),
                provenance: "table".to_owned(),
                anchor: Anchor {
                    crate_name: "k-rust-kore".to_owned(),
                    file: "crates/k-rust-kore/src/measure.rs".to_owned(),
                    symbol: format!("Counter::{variant}"),
                },
                area: name.split('.').next().map(ToOwned::to_owned),
                name: Some(variant.clone()),
                sites: Vec::new(),
                cost: Vec::new(),
                variable: None,
                invariant: None,
                no_counter: None,
                span: None,
                table: Some("Counter::ALL".to_owned()),
                call: None,
                behavior: None,
                generating_passes: Vec::new(),
                type_path: None,
                role: None,
                registry_name: Some(name.clone()),
                sequence: None,
            },
        );
    }
    insert_node(
        &mut nodes,
        Node {
            kind: "registry".to_owned(),
            id: "Counter::ALL".to_owned(),
            provenance: "table".to_owned(),
            anchor: Anchor {
                crate_name: "k-rust-kore".to_owned(),
                file: "crates/k-rust-kore/src/measure.rs".to_owned(),
                symbol: "Counter::ALL".to_owned(),
            },
            area: None,
            name: Some("counter declaration order".to_owned()),
            sites: Vec::new(),
            cost: Vec::new(),
            variable: None,
            invariant: None,
            no_counter: None,
            span: None,
            table: Some("Counter::ALL".to_owned()),
            call: None,
            behavior: None,
            generating_passes: Vec::new(),
            type_path: None,
            role: None,
            registry_name: None,
            sequence: None,
        },
    );
    let constraint_producers = algorithm_registry
        .keys()
        .cloned()
        .chain(["Counter::ALL".to_owned()])
        .collect::<BTreeSet<_>>();

    let mut primary_cards = BTreeMap::<String, Vec<&Card>>::new();
    let mut contract_cards = BTreeMap::<String, Vec<&Card>>::new();
    let mut claimed_counters = BTreeSet::new();
    for card in &cards {
        validate_card(
            card,
            root,
            &index,
            &algorithm_registry,
            &counter_registry,
            &constraint_producers,
            &mut failures,
        );
        match card.kind {
            CardKind::Primary => {
                primary_cards
                    .entry(card.body.id.clone())
                    .or_default()
                    .push(card);
                apply_primary_card(&mut nodes, card);
            }
            CardKind::Site => apply_site_card(&mut nodes, card, &mut failures),
            CardKind::Contract => {
                contract_cards
                    .entry(card.body.id.clone())
                    .or_default()
                    .push(card);
                apply_contract_card(&mut nodes, card);
            }
        }
        add_card_edges(
            &mut nodes,
            &mut edges,
            card,
            &index,
            &counter_registry,
            &mut claimed_counters,
        );
    }

    for (id, variant) in &algorithm_registry {
        match primary_cards.get(id).map(Vec::as_slice).unwrap_or(&[]) {
            [] => failures.push(format!(
                "crates/k-rust-kore/src/measure.rs: Algorithm::{variant}: {id} has no primary card"
            )),
            [_] => {}
            duplicates => failures.push(format!(
                "{}: {id} has {} primary cards: {}",
                card_location(duplicates[0]),
                duplicates.len(),
                duplicates
                    .iter()
                    .map(|card| card_location(card))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        }
    }
    for (id, declarations) in contract_cards {
        if declarations.len() != 1 {
            failures.push(format!(
                "{}: contract {id} has {} declarations: {}",
                card_location(declarations[0]),
                declarations.len(),
                declarations
                    .iter()
                    .map(|card| card_location(card))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }
    for variant in counter_registry.keys() {
        if !claimed_counters.contains(variant) {
            report.push(format!("unclaimed counter {variant}"));
        }
    }

    add_phases(&mut nodes, &mut edges);
    add_contains_edges(&nodes, &mut edges, &mut report);
    validate_source_contract(
        &cards,
        &index,
        &algorithm_registry,
        &mut failures,
        &mut report,
    );
    report_undeclared_representation_uses(&cards, &index, &mut report);

    let mut graph = Graph {
        nodes: nodes.into_values().collect(),
        edges,
    };
    graph.sort();
    failures.sort();
    failures.dedup();
    report.sort();
    report.dedup();
    Ok(Build {
        graph,
        failures,
        report,
    })
}

/// Serialize a graph in its canonical TOML form.
pub fn canonical_toml(graph: &Graph) -> Result<String, Error> {
    let mut graph = graph.clone();
    graph.sort();
    let mut output = toml::to_string_pretty(&graph)?;
    if !output.ends_with('\n') {
        output.push('\n');
    }
    Ok(output)
}

/// Workspace-relative path of the gate's advisory report.
pub const REPORT_PATH: &str = "target/algo/report.txt";

/// Write the build's advisory report lines to [`REPORT_PATH`] below `root` and return the line
/// that names the file and its line count.
pub fn write_report(root: &Path, build: &Build) -> Result<String, Error> {
    let path = root.join(REPORT_PATH);
    let mut contents = build.report.join("\n");
    if !contents.is_empty() {
        contents.push('\n');
    }
    write_output(&path, &contents)?;
    Ok(format!(
        "algo-graph report: {} lines written to {}",
        build.report.len(),
        path.display()
    ))
}

/// Write text after creating its parent directory.
pub fn write_output(path: &Path, contents: &str) -> Result<(), Error> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, contents)?;
    Ok(())
}

fn validate_card(
    card: &Card,
    root: &Path,
    index: &SourceIndex,
    algorithms: &BTreeMap<String, String>,
    counters: &BTreeMap<String, String>,
    constraint_producers: &BTreeSet<String>,
    failures: &mut Vec<String>,
) {
    if card.kind != CardKind::Contract && !algorithms.contains_key(&card.body.id) {
        failures.push(format!(
            "{}: card id {} is absent from Algorithm::ALL",
            card_location(card),
            card.body.id
        ));
    }
    if card.body.id.is_empty() {
        failures.push(format!("{}: card has no id", card_location(card)));
    }
    if card.kind == CardKind::Contract {
        if !card.body.id.starts_with("contract.") {
            failures.push(format!(
                "{}: anchored contract id {} must start with contract.",
                card_location(card),
                card.body.id
            ));
        }
        if card.body.name.is_none() || card.body.sites.len() != 1 || card.body.constrains.len() != 1
        {
            failures.push(format!(
                "{}: anchored contract {} must have a name, one site, and one constrains entry",
                card_location(card),
                card.body.id
            ));
        }
    }
    if card.kind == CardKind::Site
        && !matches!(
            card.body.role.as_deref(),
            Some("part" | "variant" | "fallback")
        )
    {
        failures.push(format!(
            "{}: site-card role for {} must be part, variant, or fallback",
            card_location(card),
            card.body.id
        ));
    }
    if let Some(policy) = &card.body.span
        && !matches!(policy.as_str(), "per problem" | "per call" | "none")
    {
        failures.push(format!(
            "{}: span policy {policy:?} for {} must be per problem, per call, or none",
            card_location(card),
            card.body.id
        ));
    }
    for row_id in legacy_row_ids(&card.source) {
        failures.push(format!(
            "{}: legacy row id {row_id} remains inside the card for {}",
            card_location(card),
            card.body.id
        ));
    }
    for site in &card.body.sites {
        match index.symbol_count(&card.crate_name, &card.file, site) {
            0 => failures.push(format!(
                "{}: site {site} does not resolve for {}",
                card.file, card.body.id
            )),
            1 => {}
            count => failures.push(format!(
                "{}: site {site} resolves to {count} items for {}",
                card.file, card.body.id
            )),
        }
    }
    for counter in &card.body.counters {
        if !counters.contains_key(counter) {
            failures.push(format!(
                "{}: Counter::{counter} does not resolve for {}",
                card_location(card),
                card.body.id
            ));
        }
    }
    if card.kind == CardKind::Primary {
        validate_primary_contract(card, failures);
    }
    for test in &card.body.tests {
        if !is_workspace_file(root, test) {
            failures.push(format!(
                "{}: test path {test} is not a file under the workspace root for {}",
                card_location(card),
                card.body.id
            ));
        }
    }
    for representation in card.body.consumes.iter().chain(&card.body.produces) {
        let Some((crate_name, symbol)) = representation_parts(representation.type_path()) else {
            failures.push(format!(
                "{}: representation type {} does not resolve for {}: expected a workspace type path",
                card_location(card),
                representation.type_path(),
                card.body.id
            ));
            continue;
        };
        match index.resolve_type(&crate_name, &symbol).len() {
            0 => failures.push(format!(
                "{}: representation type {} does not resolve for {}",
                card_location(card),
                representation.type_path(),
                card.body.id
            )),
            1 => {}
            count => failures.push(format!(
                "{}: representation type {} resolves to {count} items in {crate_name} for {}",
                card_location(card),
                representation.type_path(),
                card.body.id
            )),
        }
    }
    for target in card.body.variant_of.iter().chain(&card.body.falls_back_to) {
        if *target == card.body.id {
            failures.push(format!(
                "{}: {} names itself as a variant or fallback target",
                card_location(card),
                card.body.id
            ));
        } else if !algorithms.contains_key(target) {
            failures.push(format!(
                "{}: algorithm reference {target} does not resolve for {}",
                card_location(card),
                card.body.id
            ));
        }
    }
    for constraint in &card.body.constrains {
        if !constraint_producers.contains(&constraint.id) {
            failures.push(format!(
                "{}: constraint producer {} does not resolve for {}",
                card_location(card),
                constraint.id,
                card.body.id
            ));
        }
        if !card.body.sites.contains(&constraint.site) {
            failures.push(format!(
                "{}: constraint consumer site {} is absent from sites for {}",
                card_location(card),
                constraint.site,
                card.body.id
            ));
        }
    }
}

/// Enforce the minimum primary-card contract of design section 3.2.
fn validate_primary_contract(card: &Card, failures: &mut Vec<String>) {
    let location = card_location(card);
    let id = &card.body.id;
    if card.body.name.as_deref().is_none_or(str::is_empty) {
        failures.push(format!("{location}: primary card {id} has no name"));
    }
    if card.body.sites.is_empty() {
        failures.push(format!("{location}: primary card {id} has no sites"));
    }
    if card.body.cost.is_empty() {
        failures.push(format!("{location}: primary card {id} has no [[cost]]"));
    }
    if card.body.variable.as_deref().is_none_or(str::is_empty)
        && let Some(cost) = card
            .body
            .cost
            .iter()
            .find(|cost| bound_names_variable(&cost.bound))
    {
        failures.push(format!(
            "{location}: primary card {id} has no variable although cost bound {:?} names one",
            cost.bound
        ));
    }
    if card.body.counters.is_empty() && card.body.no_counter.as_deref().is_none_or(str::is_empty) {
        failures.push(format!(
            "{location}: primary card {id} has no counters and no no_counter reason"
        ));
    }
}

/// A bound names a variable when one of its words is a single letter other than `O` (the
/// asymptotic operator) and `x` (the multiplication sign cards write).
fn bound_names_variable(bound: &str) -> bool {
    bound
        .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .any(|word| {
            let mut characters = word.chars();
            matches!(
                (characters.next(), characters.next()),
                (Some(letter), None) if letter.is_ascii_alphabetic() && letter != 'O' && letter != 'x'
            ) || word.split_once('_').is_some_and(|(head, _)| {
                head.len() == 1 && head.chars().all(|letter| letter.is_ascii_alphabetic())
            })
        })
}

/// A `tests` entry must be a relative path, without `..`, to a file under the workspace root.
fn is_workspace_file(root: &Path, test: &str) -> bool {
    let path = Path::new(test);
    path.components()
        .all(|component| matches!(component, std::path::Component::Normal(_)))
        && root.join(path).is_file()
}

fn apply_primary_card(nodes: &mut BTreeMap<(String, String), Node>, card: &Card) {
    let key = (card.body.id.clone(), "algorithm".to_owned());
    let anchors = card.site_anchors();
    let anchor = anchors.first().cloned().unwrap_or_else(|| Anchor {
        crate_name: card.crate_name.clone(),
        file: card.file.clone(),
        symbol: card.body.id.clone(),
    });
    let node = nodes
        .entry(key)
        .or_insert_with(|| empty_algorithm(card, anchor.clone()));
    if node.provenance != "declared" {
        node.provenance = "declared".to_owned();
        node.anchor = anchor;
        node.name = card.body.name.clone();
        node.cost = card.body.cost.iter().map(Cost::from).collect();
        node.variable = card.body.variable.clone();
        node.invariant = card.body.invariant.clone();
        node.no_counter = card.body.no_counter.clone();
        node.span = card.body.span.clone();
    }
    extend_unique(&mut node.sites, anchors);
}

fn apply_site_card(
    nodes: &mut BTreeMap<(String, String), Node>,
    card: &Card,
    failures: &mut Vec<String>,
) {
    let key = (card.body.id.clone(), "algorithm".to_owned());
    let Some(node) = nodes.get_mut(&key) else {
        failures.push(format!(
            "{}: site card refers to absent algorithm {}",
            card_location(card),
            card.body.id
        ));
        return;
    };
    extend_unique(&mut node.sites, card.site_anchors());
}

fn apply_contract_card(nodes: &mut BTreeMap<(String, String), Node>, card: &Card) {
    let anchors = card.site_anchors();
    let anchor = anchors.first().cloned().unwrap_or_else(|| Anchor {
        crate_name: card.crate_name.clone(),
        file: card.file.clone(),
        symbol: card.body.id.clone(),
    });
    insert_node(
        nodes,
        Node {
            kind: "contract".to_owned(),
            id: card.body.id.clone(),
            provenance: "declared".to_owned(),
            anchor,
            area: area(&card.body.id).and_then(|area| (area != "contract").then_some(area)),
            name: card.body.name.clone(),
            sites: anchors,
            cost: Vec::new(),
            variable: None,
            invariant: None,
            no_counter: None,
            span: None,
            table: None,
            call: None,
            behavior: None,
            generating_passes: Vec::new(),
            type_path: None,
            role: None,
            registry_name: None,
            sequence: None,
        },
    );
}

fn empty_algorithm(card: &Card, anchor: Anchor) -> Node {
    Node {
        kind: "algorithm".to_owned(),
        id: card.body.id.clone(),
        provenance: "declared".to_owned(),
        anchor,
        area: area(&card.body.id),
        name: card.body.name.clone(),
        sites: Vec::new(),
        cost: card.body.cost.iter().map(Cost::from).collect(),
        variable: card.body.variable.clone(),
        invariant: card.body.invariant.clone(),
        no_counter: card.body.no_counter.clone(),
        span: card.body.span.clone(),
        table: None,
        call: None,
        behavior: None,
        generating_passes: Vec::new(),
        type_path: None,
        role: None,
        registry_name: None,
        sequence: None,
    }
}

fn add_card_edges(
    nodes: &mut BTreeMap<(String, String), Node>,
    edges: &mut Vec<Edge>,
    card: &Card,
    index: &SourceIndex,
    counters: &BTreeMap<String, String>,
    claimed_counters: &mut BTreeSet<String>,
) {
    for counter in &card.body.counters {
        claimed_counters.insert(counter.clone());
        if counters.contains_key(counter) {
            edges.push(edge(
                "measured-by",
                &card.body.id,
                &counter_id(counter),
                "declared",
            ));
        }
    }
    for test in &card.body.tests {
        let test_id = test.clone();
        let crate_name = test
            .strip_prefix("crates/")
            .and_then(|rest| rest.split('/').next())
            .unwrap_or("workspace")
            .to_owned();
        insert_node(
            nodes,
            Node {
                kind: "observation".to_owned(),
                id: test_id.clone(),
                provenance: "declared".to_owned(),
                anchor: Anchor {
                    crate_name,
                    file: test.clone(),
                    symbol: test.clone(),
                },
                area: area(&card.body.id),
                name: Some(test.clone()),
                sites: Vec::new(),
                cost: Vec::new(),
                variable: None,
                invariant: None,
                no_counter: None,
                span: None,
                table: None,
                call: None,
                behavior: None,
                generating_passes: Vec::new(),
                type_path: None,
                role: None,
                registry_name: None,
                sequence: None,
            },
        );
        edges.push(edge("measured-by", &card.body.id, &test_id, "declared"));
    }
    for representation in &card.body.consumes {
        add_representation(nodes, edges, card, representation, "consumes", index);
    }
    for representation in &card.body.produces {
        add_representation(nodes, edges, card, representation, "produces", index);
    }
    if let Some(target) = &card.body.variant_of {
        edges.push(edge("variant-of", &card.body.id, target, "declared"));
    }
    for (order, target) in card.body.falls_back_to.iter().enumerate() {
        let mut relation = edge("falls-back-to", &card.body.id, target, "declared");
        relation.order = Some(order);
        edges.push(relation);
    }
    for constraint in &card.body.constrains {
        let mut relation = edge("constrains", &constraint.id, &card.body.id, "declared");
        relation.detail = Some(constraint.via.clone());
        relation.consumer_site = Some(Anchor {
            crate_name: card.crate_name.clone(),
            file: card.file.clone(),
            symbol: constraint.site.clone(),
        });
        edges.push(relation);
    }
}

fn add_representation(
    nodes: &mut BTreeMap<(String, String), Node>,
    edges: &mut Vec<Edge>,
    card: &Card,
    representation: &Representation,
    edge_kind: &str,
    index: &SourceIndex,
) {
    let id = representation.id();
    let resolved =
        representation_parts(representation.type_path()).and_then(|(crate_name, symbol)| {
            let anchors = index.resolve_type(&crate_name, &symbol);
            (anchors.len() == 1).then(|| anchors[0].clone())
        });
    let anchor = resolved.unwrap_or_else(|| Anchor {
        crate_name: card.crate_name.clone(),
        file: card.file.clone(),
        symbol: representation.type_path().to_owned(),
    });
    insert_node(
        nodes,
        Node {
            kind: "representation".to_owned(),
            id: id.clone(),
            provenance: "declared".to_owned(),
            anchor,
            area: representation_parts(representation.type_path())
                .and_then(|(crate_name, _)| crate_area(&crate_name)),
            name: Some(representation.type_path().to_owned()),
            sites: Vec::new(),
            cost: Vec::new(),
            variable: None,
            invariant: None,
            no_counter: None,
            span: None,
            table: None,
            call: None,
            behavior: None,
            generating_passes: Vec::new(),
            type_path: Some(representation.type_path().to_owned()),
            role: representation.role().map(ToOwned::to_owned),
            registry_name: None,
            sequence: None,
        },
    );
    edges.push(edge(edge_kind, &card.body.id, &id, "declared"));
}

fn add_phases(nodes: &mut BTreeMap<(String, String), Node>, edges: &mut Vec<Edge>) {
    let mut phases = Vec::<Node>::new();
    for name in LOAD_PHASES {
        phases.push(simple_phase(name, "LOAD_PHASES", phases.len()));
    }
    let prologue_start = phases.len();
    for description in prologue_descriptions() {
        phases.push(described_phase(description, phases.len()));
    }
    let stages_start = phases.len();
    for description in stage_descriptions() {
        phases.push(described_phase(description, phases.len()));
    }
    let stages_end = phases.len();
    for name in EMISSION_PHASES {
        phases.push(simple_phase(name, "EMISSION_PHASES", phases.len()));
    }

    // LOAD_PHASES contains two mutually exclusive entry phases and nested child timings;
    // EMISSION_PHASES contains an optional Bison phase. Their table order is not an assertion
    // that every adjacent pair executes. Only the two unconditional stage runs contribute
    // follows edges until those tables expose branch metadata.
    for range in [prologue_start..stages_start, stages_start..stages_end] {
        for pair in phases[range].windows(2) {
            let mut relation = edge("follows", &pair[0].id, &pair[1].id, "table");
            relation.order = pair[0].sequence;
            edges.push(relation);
        }
    }
    for phase in phases {
        insert_node(nodes, phase);
    }
}

fn simple_phase(name: &str, table: &str, sequence: usize) -> Node {
    Node {
        kind: "phase".to_owned(),
        id: name.to_owned(),
        provenance: "table".to_owned(),
        anchor: Anchor {
            crate_name: "k-rust".to_owned(),
            file: "crates/k-rust/src/kompile/pipeline.rs".to_owned(),
            symbol: table.to_owned(),
        },
        area: Some("kompile".to_owned()),
        name: Some(name.to_owned()),
        sites: Vec::new(),
        cost: Vec::new(),
        variable: None,
        invariant: None,
        no_counter: None,
        span: None,
        table: Some(table.to_owned()),
        call: None,
        behavior: None,
        generating_passes: Vec::new(),
        type_path: None,
        role: None,
        registry_name: None,
        sequence: Some(sequence),
    }
}

fn described_phase(description: StageDescription, sequence: usize) -> Node {
    Node {
        kind: "phase".to_owned(),
        id: description.name.to_owned(),
        provenance: "table".to_owned(),
        anchor: Anchor {
            crate_name: "k-rust".to_owned(),
            file: "crates/k-rust/src/kompile/pipeline.rs".to_owned(),
            symbol: description.call.to_owned(),
        },
        area: Some("kompile".to_owned()),
        name: Some(description.name.to_owned()),
        sites: Vec::new(),
        cost: Vec::new(),
        variable: None,
        invariant: None,
        no_counter: None,
        span: None,
        table: Some(description.table.to_owned()),
        call: Some(description.call.to_owned()),
        behavior: Some(description.behavior.to_owned()),
        generating_passes: description
            .generating_passes
            .into_iter()
            .map(ToOwned::to_owned)
            .collect(),
        type_path: None,
        role: None,
        registry_name: None,
        sequence: Some(sequence),
    }
}

fn add_contains_edges(
    nodes: &BTreeMap<(String, String), Node>,
    edges: &mut Vec<Edge>,
    report: &mut Vec<String>,
) {
    let algorithms = nodes
        .values()
        .filter(|node| node.kind == "algorithm")
        .collect::<Vec<_>>();
    for phase in nodes.values().filter(|node| node.kind == "phase") {
        let Some(call) = &phase.call else {
            continue;
        };
        let matched = algorithms
            .iter()
            .filter(|algorithm| {
                algorithm.sites.iter().any(|site| {
                    site.symbol == *call
                        || site
                            .symbol
                            .rsplit("::")
                            .next()
                            .is_some_and(|symbol| symbol == call)
                })
            })
            .collect::<Vec<_>>();
        if matched.is_empty() {
            report.push(format!(
                "uncovered phase {}: call {call} names no algorithm site",
                phase.id
            ));
        }
        for algorithm in matched {
            edges.push(edge("contains", &phase.id, &algorithm.id, "derived"));
        }
    }
}

fn validate_source_contract(
    cards: &[Card],
    index: &SourceIndex,
    algorithms: &BTreeMap<String, String>,
    failures: &mut Vec<String>,
    report: &mut Vec<String>,
) {
    const MEASURE_FILE: &str = "crates/k-rust-kore/src/measure.rs";

    let card_files = cards
        .iter()
        .map(|card| card.file.as_str())
        .collect::<BTreeSet<_>>();
    for (file, facts) in &index.files {
        if facts.raw_algo_spans > 0 && file != MEASURE_FILE {
            failures.push(format!(
                "{file}: info_span!(\"algo\", ...) is a raw algorithm span; only {MEASURE_FILE}:algorithm_span may contain that literal"
            ));
        }
        if facts.has_invariant_loop && !card_files.contains(file.as_str()) {
            report.push(format!(
                "worklist without card {file}: contains a while/loop expression and an Invariant: comment"
            ));
        }
    }
    let measure_raw_spans = index
        .files
        .get(MEASURE_FILE)
        .map(|facts| facts.raw_algo_spans)
        .unwrap_or(0);
    if measure_raw_spans != 1 {
        failures.push(format!(
            "{MEASURE_FILE}: algorithm_span must contain the sole raw info_span!(\"algo\", ...) literal; found {measure_raw_spans}"
        ));
    }

    for card in cards.iter().filter(|card| card.kind == CardKind::Primary) {
        let has_counter = cards
            .iter()
            .filter(|candidate| candidate.body.id == card.body.id)
            .any(|candidate| !candidate.body.counters.is_empty());
        let span_policy = card.body.span.as_deref();
        if !has_counter && !matches!(span_policy, Some("per problem" | "per call")) {
            report.push(format!(
                "runtime-invisible algorithm {} at {}: neither a counter nor a span",
                card.body.id,
                card_location(card)
            ));
        }

        let Some(policy @ ("per problem" | "per call")) = span_policy else {
            continue;
        };
        let Some(variant) = algorithms.get(&card.body.id) else {
            continue;
        };
        let site_files = cards
            .iter()
            .filter(|candidate| candidate.body.id == card.body.id)
            .map(|candidate| candidate.file.as_str())
            .collect::<BTreeSet<_>>();
        let instrumented = site_files.iter().any(|file| {
            index
                .files
                .get(*file)
                .is_some_and(|facts| facts.algorithm_spans.contains(variant))
        });
        if !instrumented {
            failures.push(format!(
                "{}: span policy {policy:?} for {} has no algorithm_span(Algorithm::{variant}) in any site file ({})",
                card_location(card),
                card.body.id,
                site_files.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }
    }
}

/// Report each algorithm that branches on a declared representation returned by a site of its
/// producer, while no card of the algorithm consumes or produces that representation.
///
/// This is a syntactic heuristic, not type resolution. A representation is identified by its
/// simple name: the last path segment of a declared type, without generic arguments. Its producers
/// are the algorithms with a card that produces a type of that simple name, and a producer site
/// name is the last `::` segment of a `sites` entry of any card of a producer. A use is an
/// [`cards::OutcomePattern`] that names the representation and whose callee is a producer site
/// name, as `MatchResult::Failed(_)` in `match match_terms_in_definition(..) { .. }`. The pattern
/// path is first resolved through the file's `use` declarations by
/// [`cards::SourceIndex::resolve_path`]; a resolved path names the representation when it equals
/// the declared type path without generic arguments, so an alias such as `KoreSentence` matches
/// `k_rust_kore::kore::ast::Sentence` and a same-name type at another path does not match. When
/// the path cannot be resolved, the pattern names the representation whose simple name equals
/// the identifier, and two types with one simple name are not distinguished. A use belongs to
/// the algorithms with a card in the same file that names the enclosing item as a site (directly,
/// or through `impl Type` for a `Type::method` item); a use in an item that no card in the file
/// names belongs to every algorithm whose primary card is in that file. An algorithm declares a
/// simple name when any of its cards consumes or produces a type of that simple name, whatever
/// the role or crate.
fn report_undeclared_representation_uses(
    cards: &[Card],
    index: &SourceIndex,
    report: &mut Vec<String>,
) {
    let simple_name = |representation: &Representation| {
        representation_parts(representation.type_path()).map(|(_, symbol)| symbol)
    };
    let mut type_paths = BTreeMap::<String, BTreeSet<&str>>::new();
    let mut plain_paths = BTreeMap::<String, BTreeSet<String>>::new();
    let mut producer_sites = BTreeMap::<String, BTreeSet<&str>>::new();
    let mut declared = BTreeMap::<&str, BTreeSet<String>>::new();
    for card in cards {
        for representation in &card.body.produces {
            let Some(name) = simple_name(representation) else {
                continue;
            };
            let sites = cards
                .iter()
                .filter(|candidate| candidate.body.id == card.body.id)
                .flat_map(|candidate| &candidate.body.sites)
                .filter(|site| !site.starts_with("impl "))
                .filter_map(|site| site.rsplit("::").next());
            producer_sites.entry(name).or_default().extend(sites);
        }
        for representation in card.body.consumes.iter().chain(&card.body.produces) {
            let Some(name) = simple_name(representation) else {
                continue;
            };
            type_paths
                .entry(name.clone())
                .or_default()
                .insert(representation.type_path());
            plain_paths
                .entry(name.clone())
                .or_default()
                .extend(plain_type_path(representation.type_path()));
            declared.entry(&card.body.id).or_default().insert(name);
        }
    }

    let mut findings = BTreeMap::<(&str, &str), BTreeSet<String>>::new();
    for (file, facts) in &index.files {
        let file_cards = cards
            .iter()
            .filter(|card| card.file == *file)
            .collect::<Vec<_>>();
        for pattern in &facts.outcome_patterns {
            let resolved = index.resolve_path(file, &pattern.path);
            let resolved_name = match &resolved {
                Some(path) => path.last().unwrap_or(&pattern.identifier),
                None => &pattern.identifier,
            };
            let Some((name, _)) = producer_sites.get_key_value(resolved_name) else {
                continue;
            };
            if resolved.is_some_and(|path| !plain_paths[name].contains(&path.join("::"))) {
                continue;
            }
            if !producer_sites[name].contains(pattern.callee.as_str()) {
                continue;
            }
            let names_item = |card: &&&Card| {
                pattern.item.as_deref().is_some_and(|item| {
                    card.body.sites.iter().any(|site| {
                        site == item
                            || site.strip_prefix("impl ").is_some_and(|type_name| {
                                item.strip_prefix(type_name)
                                    .is_some_and(|method| method.starts_with("::"))
                            })
                    })
                })
            };
            let mut owners = file_cards
                .iter()
                .filter(names_item)
                .map(|card| card.body.id.as_str())
                .collect::<BTreeSet<_>>();
            if owners.is_empty() {
                owners = file_cards
                    .iter()
                    .filter(|card| card.kind == CardKind::Primary)
                    .map(|card| card.body.id.as_str())
                    .collect();
            }
            for owner in owners {
                if declared
                    .get(owner)
                    .is_some_and(|names| names.contains(name))
                {
                    continue;
                }
                findings.entry((owner, name)).or_default().insert(format!(
                    "{file}::{} (from {})",
                    pattern.item.as_deref().unwrap_or("<item>"),
                    pattern.callee
                ));
            }
        }
    }
    for ((owner, name), uses) in findings {
        report.push(format!(
            "undeclared representation use {owner}: matches {name} ({}) without consumes or produces at {}",
            type_paths[name].iter().copied().collect::<Vec<_>>().join(", "),
            uses.into_iter().collect::<Vec<_>>().join(", ")
        ));
    }
}

fn card_location(card: &Card) -> String {
    format!(
        "{}:{}",
        card.file,
        card.body
            .sites
            .first()
            .map(String::as_str)
            .unwrap_or("<card>")
    )
}

fn legacy_row_ids(source: &str) -> BTreeSet<String> {
    source
        .split(|character: char| !character.is_ascii_alphanumeric())
        .filter(|token| {
            let mut characters = token.chars();
            let Some(prefix @ ('B' | 'P' | 'D')) = characters.next() else {
                return false;
            };
            let remainder = characters.as_str();
            !remainder.is_empty()
                && (remainder
                    .chars()
                    .all(|character| character.is_ascii_digit())
                    || (prefix == 'B'
                        && remainder.ends_with('b')
                        && !remainder[..remainder.len() - 1].is_empty()
                        && remainder[..remainder.len() - 1]
                            .chars()
                            .all(|character| character.is_ascii_digit())))
        })
        .map(ToOwned::to_owned)
        .collect()
}

fn insert_node(nodes: &mut BTreeMap<(String, String), Node>, node: Node) {
    nodes
        .entry((node.id.clone(), node.kind.clone()))
        .or_insert(node);
}

fn edge(kind: &str, from: &str, to: &str, provenance: &str) -> Edge {
    Edge {
        kind: kind.to_owned(),
        from: from.to_owned(),
        to: to.to_owned(),
        provenance: provenance.to_owned(),
        detail: None,
        order: None,
        consumer_site: None,
    }
}

fn counter_id(variant: &str) -> String {
    variant.to_owned()
}

fn extend_unique<T: Eq>(values: &mut Vec<T>, additions: impl IntoIterator<Item = T>) {
    for addition in additions {
        if !values.contains(&addition) {
            values.push(addition);
        }
    }
}

fn area(id: &str) -> Option<String> {
    id.split_once('.').map(|(area, _)| area.to_owned())
}

fn crate_area(crate_name: &str) -> Option<String> {
    match crate_name {
        "k-rust-backend" => Some("backend".to_owned()),
        "k-rust-kore" => Some("kore".to_owned()),
        "k-rust" => Some("kompile".to_owned()),
        _ => None,
    }
}

/// A type path without generic arguments, as `k_rust::definition::PartialOrder` for
/// `k_rust::definition::PartialOrder<k_rust::kast::Sort>`.
fn plain_type_path(type_path: &str) -> Option<String> {
    let syn::Type::Path(path) = syn::parse_str::<syn::Type>(type_path).ok()? else {
        return None;
    };
    Some(
        path.path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::"),
    )
}

fn representation_parts(type_path: &str) -> Option<(String, String)> {
    let parsed = syn::parse_str::<syn::Type>(type_path).ok()?;
    let syn::Type::Path(path) = parsed else {
        return None;
    };
    let mut segments = path.path.segments.iter();
    let crate_name = segments.next()?.ident.to_string().replace('_', "-");
    let symbol = path.path.segments.last()?.ident.to_string();
    Some((crate_name, symbol))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generic_type_paths_resolve_to_crate_and_item() {
        assert_eq!(
            representation_parts("k_rust::definition::ProductionCatalog<'a>"),
            Some(("k-rust".to_owned(), "ProductionCatalog".to_owned()))
        );
    }

    fn primary_card(source: &str) -> Card {
        Card {
            kind: CardKind::Primary,
            body: toml::from_str(source).unwrap(),
            crate_name: "k-rust-backend".to_owned(),
            file: "crates/k-rust-backend/src/example.rs".to_owned(),
            source: source.to_owned(),
        }
    }

    #[test]
    fn primary_cards_must_meet_the_minimum_contract() {
        let mut failures = Vec::new();
        validate_primary_contract(&primary_card("id = \"backend.x\"\n"), &mut failures);
        assert_eq!(failures.len(), 4, "{failures:?}");
        for (failure, missing) in failures.iter().zip([
            "has no name",
            "has no sites",
            "has no [[cost]]",
            "has no counters and no no_counter reason",
        ]) {
            assert!(
                failure.starts_with(
                    "crates/k-rust-backend/src/example.rs:<card>: primary card backend.x "
                ) && failure.ends_with(missing),
                "{failure}"
            );
        }

        let mut failures = Vec::new();
        validate_primary_contract(
            &primary_card(
                "id = \"backend.x\"\nname = \"x\"\nsites = [\"run\"]\ncounters = [\"MatchingPairs\"]\n[[cost]]\nmode = \"m\"\nbound = \"O(p x a)\"\n",
            ),
            &mut failures,
        );
        assert_eq!(
            failures,
            [
                "crates/k-rust-backend/src/example.rs:run: primary card backend.x has no variable although cost bound \"O(p x a)\" names one"
            ]
        );

        let mut failures = Vec::new();
        validate_primary_contract(
            &primary_card(
                "id = \"backend.x\"\nname = \"x\"\nsites = [\"run\"]\ncounters = []\nno_counter = \"once\"\n[[cost]]\nmode = \"m\"\nbound = \"O(1) per call\"\n",
            ),
            &mut failures,
        );
        assert!(failures.is_empty(), "{failures:?}");
    }

    #[test]
    fn bound_variables_are_single_letters_other_than_the_operators() {
        assert!(bound_names_variable("O(p x a)"));
        assert!(bound_names_variable("O(sum n_m^2 x eq)"));
        assert!(bound_names_variable("at most h rounds"));
        assert!(!bound_names_variable("O(1)"));
        assert!(!bound_names_variable(
            "one matching problem and up to three SMT calls"
        ));
    }

    #[test]
    fn tests_entries_must_be_files_under_the_root() {
        let root = workspace_root();
        assert!(is_workspace_file(
            &root,
            "crates/algo-graph/tests/freshness.rs"
        ));
        assert!(!is_workspace_file(&root, "crates/algo-graph/tests"));
        assert!(!is_workspace_file(&root, "/etc/hosts"));
        assert!(!is_workspace_file(
            &root,
            "crates/../crates/algo-graph/tests/freshness.rs"
        ));
    }

    #[test]
    fn legacy_row_ids_are_recognized_only_as_tokens() {
        assert_eq!(
            legacy_row_ids("B2, B6b, P19 and D35; not Btree or parser.p19"),
            BTreeSet::from([
                "B2".to_owned(),
                "B6b".to_owned(),
                "D35".to_owned(),
                "P19".to_owned(),
            ])
        );
    }

    #[test]
    fn current_tree_is_canonical() {
        let build = build_graph(&workspace_root()).unwrap();
        let first = canonical_toml(&build.graph).unwrap();
        let second = canonical_toml(&build.graph).unwrap();
        assert_eq!(first, second);
        assert!(!first.contains(&workspace_root().display().to_string()));
        let decoded: Graph = toml::from_str(&first).unwrap();
        assert_eq!(decoded, build.graph);
    }

    #[test]
    fn hard_case_constraints_have_exact_anchored_coverage() {
        let graph = build_graph(&workspace_root()).unwrap().graph;
        let constraints = graph
            .edges
            .iter()
            .filter(|edge| edge.kind == "constrains")
            .map(|edge| {
                (
                    edge.from.as_str(),
                    edge.to.as_str(),
                    edge.consumer_site
                        .as_ref()
                        .map(|anchor| anchor.symbol.as_str()),
                )
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            constraints,
            BTreeSet::from([
                (
                    "Counter::ALL",
                    "contract.counters.krust_writer_order",
                    Some("write_counters_if_requested"),
                ),
                (
                    "definition.catalog.production",
                    "contract.definition.production_catalog_cache",
                    Some("DefinitionViews::production_catalog"),
                ),
                (
                    "definition.catalog.production",
                    "parser.bubble.rules",
                    Some("resolve_rule_bubbles_with_resolved"),
                ),
                (
                    "definition.catalog.production",
                    "parser.programs.parse",
                    Some("ProgramParser::parse"),
                ),
                (
                    "definition.provenance.record",
                    "definition.json.encode",
                    Some("serialize_provenance"),
                ),
                (
                    "definition.resolve.imports",
                    "contract.kompile.resolved_cache",
                    Some("PassInput::resolved_raw"),
                ),
                (
                    "kompile.kore.declarations",
                    "definition.outer.requires",
                    Some("load_definition_against_prepared"),
                ),
                (
                    "kompile.sentences.number",
                    "backend.definition.internalize",
                    Some("BackendDefinition::internalize_for_source_execution"),
                ),
                (
                    "kompile.sentences.number",
                    "kompile.modules.rewrite_order",
                    Some("collect_execution_rewrite_order"),
                ),
            ])
        );
        assert!(
            graph
                .edges
                .iter()
                .filter(|edge| edge.kind == "constrains")
                .all(|edge| edge.provenance == "declared" && edge.detail.is_some())
        );
        let carriers = graph
            .edges
            .iter()
            .filter(|edge| edge.kind == "constrains")
            .map(|edge| {
                (
                    (edge.from.as_str(), edge.to.as_str()),
                    edge.detail.as_deref(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            carriers,
            BTreeMap::from([
                (
                    ("Counter::ALL", "contract.counters.krust_writer_order"),
                    Some(
                        "Snapshot::iter preserves Counter::ALL declaration order for the hand-written JSON object",
                    ),
                ),
                (
                    (
                        "definition.catalog.production",
                        "contract.definition.production_catalog_cache",
                    ),
                    Some(
                        "ResolvedDefinition keeps one ProductionCatalog per module in a OnceLock that ResolvedDefinition::update carries forward while the module's visible syntax is unchanged; DefinitionViews caches an Arc to it",
                    ),
                ),
                (
                    ("definition.catalog.production", "parser.bubble.rules"),
                    Some(
                        "the per-module ProductionCatalog that rule_grammar reads from ResolvedDefinition::production_catalog",
                    ),
                ),
                (
                    ("definition.catalog.production", "parser.programs.parse"),
                    Some(
                        "the per-module ProductionCatalog that ProgramParser::from_resolved reads from ResolvedDefinition::production_catalog",
                    ),
                ),
                (
                    ("definition.provenance.record", "definition.json.encode"),
                    Some(
                        "AttributeKey::Origin records generated origins and is excluded from semantic comparison before provenance serialization",
                    ),
                ),
                (
                    (
                        "definition.resolve.imports",
                        "contract.kompile.resolved_cache",
                    ),
                    Some(
                        "Current.resolved is forced once and ResolvedDefinition::update propagates the cached resolution between stages",
                    ),
                ),
                (
                    ("kompile.kore.declarations", "definition.outer.requires"),
                    Some(
                        "the SyntaxModule attribute and PreparedDefinitionManifest module digests cross the process boundary in parsed.json and krust.json",
                    ),
                ),
                (
                    ("kompile.sentences.number", "backend.definition.internalize"),
                    Some(
                        "the UNIQUE_ID attribute survives KORE emission and determines source rewrite order",
                    ),
                ),
                (
                    ("kompile.sentences.number", "kompile.modules.rewrite_order"),
                    Some("the UNIQUE_ID attribute set by number_sentences"),
                ),
            ])
        );

        let kinds = graph
            .nodes
            .iter()
            .map(|node| (node.id.as_str(), node.kind.as_str()))
            .collect::<BTreeMap<_, _>>();
        let follows = graph
            .edges
            .iter()
            .filter(|edge| edge.kind == "follows")
            .map(|edge| (edge.from.as_str(), edge.to.as_str()))
            .collect::<BTreeSet<_>>();
        let descriptions = stage_descriptions();
        let stage_order = descriptions
            .windows(2)
            .map(|pair| (pair[0].name, pair[1].name))
            .collect::<BTreeSet<_>>();
        assert!(stage_order.is_subset(&follows));
        assert!(
            graph
                .edges
                .iter()
                .filter(|edge| edge.kind == "follows")
                .all(|edge| {
                    edge.provenance == "table"
                        && kinds.get(edge.from.as_str()) == Some(&"phase")
                        && kinds.get(edge.to.as_str()) == Some(&"phase")
                })
        );
        assert!(
            graph
                .edges
                .iter()
                .filter(|edge| edge.kind == "constrains")
                .all(|edge| {
                    kinds.get(edge.from.as_str()) != Some(&"phase")
                        && kinds.get(edge.to.as_str()) != Some(&"phase")
                })
        );
    }
}
