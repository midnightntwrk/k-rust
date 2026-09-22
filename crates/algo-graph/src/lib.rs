//! Deterministic construction and rendering of the workspace algorithm graph.

mod cards;
mod drift;
mod join;
mod model;
mod render;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs, io,
    path::{Path, PathBuf},
};

use cards::{Card, CardKind, Representation, SourceIndex};
pub use drift::{DriftFinding, DriftReport, drift, render_drift};
pub use join::{
    AGGREGATION_RULE, AlgorithmCounter, AlgorithmRun, EdgeRun, JOIN_SCHEMA_VERSION, Join, NodeRun,
    ObservedContain, ObservedEdge, PhaseRun, Receipt, ReceiptCounter, Revision, Summary,
    ToolVersion, canonical_join_toml, join_files, render_run_overlay,
};
use k_rust::kompile::pipeline::{
    EMISSION_PHASES, LOAD_PHASES, StageDescription, prologue_descriptions, stage_descriptions,
};
use k_rust_kore::measure::{Algorithm, Counter};
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

/// Return the repository root encoded by this workspace build.
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("algo-graph is under crates/algo-graph")
        .to_owned()
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
    for test in &card.body.tests {
        if !root.join(test).exists() {
            failures.push(format!(
                "{}: test path {test} does not resolve for {}",
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
        if !algorithms.contains_key(target) {
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
                        "the per-module OnceLock retains the first ProductionCatalog forced by disambiguation, sort injection, or KORE emission",
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
