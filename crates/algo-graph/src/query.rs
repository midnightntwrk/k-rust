//! Questions a coding agent asks of the algorithm graph and of one run joined to it.
//!
//! Every answer is a serializable struct with a compact plain-text rendering.
//! Text is one header line followed by one item per line or a small indented block,
//! and every item ends with a `file::symbol` anchor.
//! The TOML rendering carries the same content.
//!
//! The graph only knows what cards declare and what the registries tabulate.
//! An absent relation is therefore never evidence of independence (design section 2),
//! and every answer that lists relations says so.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt, fs,
    path::{Component, Path},
};

use serde::Serialize;

use crate::{
    AlgorithmRun, Anchor, Cost, Edge, Error, Graph, JOIN_SCHEMA_VERSION, Join, Node, Verdict,
    build_graph, edge_verdict_rule,
};

/// The caveat every relation-listing answer repeats.
pub const ABSENT_RELATION_CAVEAT: &str = "an absent relation proves nothing: relations are declared by hand on cards or read from the stage table, and there is no call graph";

const COUNTER_TABLE: &str = "Counter::ALL";

/// An id, path, or area that names nothing in the graph or join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NotFound {
    /// What was looked up, such as `algorithm id` or `path`.
    pub what: String,
    /// The text as given.
    pub query: String,
    /// The three nearest known values.
    pub candidates: Vec<String>,
    /// An optional sentence on how to recover.
    pub hint: Option<String>,
}

impl fmt::Display for NotFound {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "unknown {} `{}`", self.what, self.query)?;
        if !self.candidates.is_empty() {
            write!(formatter, "; nearest: {}", self.candidates.join(", "))?;
        }
        if let Some(hint) = &self.hint {
            write!(formatter, "\n{hint}")?;
        }
        Ok(())
    }
}

impl std::error::Error for NotFound {}

/// An answer that has a plain-text rendering besides its TOML serialization.
pub trait Answer: Serialize {
    /// The compact plain-text rendering, ending with a newline.
    fn text(&self) -> String;

    /// The TOML rendering of the same content.
    fn toml(&self) -> Result<String, Error> {
        let mut output = toml::to_string_pretty(self)?;
        if !output.ends_with('\n') {
            output.push('\n');
        }
        Ok(output)
    }
}

/// Read a saved graph, or build the graph from the checkout at `root`.
///
/// The second value holds the freshness failures of a build; a saved graph has none.
pub fn load_graph(root: &Path, saved: Option<&Path>) -> Result<(Graph, Vec<String>), Error> {
    match saved {
        Some(path) => {
            let mut graph: Graph = toml::from_str(&fs::read_to_string(path)?)?;
            graph.sort();
            Ok((graph, Vec::new()))
        }
        None => {
            let build = build_graph(root)?;
            Ok((build.graph, build.failures))
        }
    }
}

/// Read a canonical join file as written by `algo-graph join`.
pub fn read_join(path: &Path) -> Result<Join, Error> {
    let source = fs::read_to_string(path)?;
    let schema = toml::from_str::<toml::Table>(&source)?
        .get("schema_version")
        .and_then(toml::Value::as_integer);
    if schema != Some(i64::from(JOIN_SCHEMA_VERSION)) {
        return Err(Error::Invalid(format!(
            "{}: join schema {}, but this tool reads schema {JOIN_SCHEMA_VERSION}; rerun `algo-graph join`",
            path.display(),
            schema.map_or_else(|| "absent".to_owned(), |schema| schema.to_string())
        )));
    }
    Ok(toml::from_str(&source)?)
}

/// A counter named by its `Counter` variant and its dotted registry name.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize)]
pub struct CounterRef {
    pub variant: String,
    pub name: String,
}

// ---------------------------------------------------------------------------------------------
// owner

/// The algorithms, contracts, and representations anchored in a file or at a symbol.
#[derive(Clone, Debug, Serialize)]
pub struct OwnerAnswer {
    pub query: String,
    /// Repository-relative file or directory, absent for a symbol-only query.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    /// False when a symbol was given but no card names it as a site; the answer then lists
    /// the owners of the whole file.
    pub symbol_is_site: bool,
    /// Sites in the file nearest to an unmatched symbol.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub nearest_sites: Vec<String>,
    /// Files with cards nearest to a path that has none.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub nearest_files: Vec<String>,
    #[serde(rename = "owner")]
    pub owners: Vec<Owner>,
    #[serde(rename = "representation")]
    pub representations: Vec<OwnedRepresentation>,
}

/// One algorithm or anchored contract with a site in the queried place.
#[derive(Clone, Debug, Serialize)]
pub struct Owner {
    pub id: String,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// True when the primary card itself is in the queried file or directory.
    pub primary_card_here: bool,
    /// The primary card lives in the `//!` head of this anchor's file; the symbol is the first
    /// site.
    pub card: Anchor,
    /// The sites that matched the query.
    pub matched: Vec<Anchor>,
    /// The algorithm's sites outside the queried file or directory.
    pub other_sites: Vec<Anchor>,
    pub counters: Vec<CounterRef>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub no_counter: Option<String>,
    pub tests: Vec<String>,
    /// `per problem`, `per call`, `none`, or `absent` when the card has no `span` key.
    pub span: String,
    /// For a contract: each producer it depends on, with the carrier of the dependency.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub constrained_by: Vec<String>,
}

/// A representation type defined in the queried place, with the algorithms on each side.
#[derive(Clone, Debug, Serialize)]
pub struct OwnedRepresentation {
    pub id: String,
    pub anchor: Anchor,
    pub produced_by: Vec<String>,
    pub consumed_by: Vec<String>,
}

/// Answer `owner <path>[::<symbol>]` or `owner <symbol>`.
///
/// A target containing `/`, ending in `.rs`, or naming a top directory of an anchored file is a
/// path, absolute or relative to `root`, and may be a directory; `::` after the path starts a
/// symbol. Any other target is a symbol looked up in every file.
pub fn owner(graph: &Graph, root: &Path, target: &str) -> Result<OwnerAnswer, NotFound> {
    let index = Index::new(graph);
    let files = index.anchored_files();
    let names_directory = files
        .iter()
        .any(|file| file.starts_with(&format!("{target}/")));
    let (raw_path, symbol) = if target.contains('/') || target.ends_with(".rs") || names_directory {
        match target.split_once("::") {
            Some((path, symbol)) => (Some(path), Some(symbol.to_owned())),
            None => (Some(target), None),
        }
    } else {
        (None, Some(target.to_owned()))
    };
    let path = raw_path.map(|raw| relative_path(root, raw, &files));

    let in_path = |anchor: &Anchor| {
        path.as_deref()
            .is_none_or(|path| anchor.file == path || anchor.file.starts_with(&format!("{path}/")))
    };
    let owners_in_path = graph
        .nodes
        .iter()
        .filter(|node| matches!(node.kind.as_str(), "algorithm" | "contract"))
        .filter(|node| node_anchors(node).any(&in_path))
        .collect::<Vec<_>>();
    let representations_in_path = graph
        .nodes
        .iter()
        .filter(|node| node.kind == "representation" && in_path(&node.anchor))
        .collect::<Vec<_>>();

    if let Some(path) = &path
        && owners_in_path.is_empty()
        && representations_in_path.is_empty()
        && !root.join(path).exists()
    {
        return Err(NotFound {
            what: "path".to_owned(),
            query: raw_path.unwrap_or(target).to_owned(),
            candidates: nearest(path, files.iter().map(String::as_str)),
            hint: Some(
                "paths are relative to the repository root or absolute; try `algo-graph query search <file name>`"
                    .to_owned(),
            ),
        });
    }

    let symbol_hits = |node: &Node| {
        node_anchors(node)
            .filter(|anchor| in_path(anchor))
            .filter(|anchor| {
                symbol
                    .as_deref()
                    .is_some_and(|symbol| symbol_matches(&anchor.symbol, symbol))
            })
            .cloned()
            .collect::<Vec<_>>()
    };
    let symbol_owners = owners_in_path
        .iter()
        .filter(|node| !symbol_hits(node).is_empty())
        .copied()
        .collect::<Vec<_>>();
    let symbol_representations = representations_in_path
        .iter()
        .filter(|node| {
            symbol
                .as_deref()
                .is_some_and(|symbol| symbol_matches(&node.anchor.symbol, symbol))
        })
        .copied()
        .collect::<Vec<_>>();
    let symbol_is_site =
        symbol.is_none() || !symbol_owners.is_empty() || !symbol_representations.is_empty();

    if symbol.is_some() && path.is_none() && symbol_owners.is_empty() {
        let sites = graph
            .nodes
            .iter()
            .filter(|node| matches!(node.kind.as_str(), "algorithm" | "contract"))
            .flat_map(node_anchors)
            .map(|anchor| anchor.symbol.as_str())
            .collect::<BTreeSet<_>>();
        return Err(NotFound {
            what: "site symbol".to_owned(),
            query: target.to_owned(),
            candidates: nearest(target, sites),
            hint: Some(
                "only card sites are indexed; a helper called by a site is not; give `<file>::<symbol>` to list the owners of the file"
                    .to_owned(),
            ),
        });
    }

    let (selected, representations) = if symbol_is_site && symbol.is_some() {
        (symbol_owners, symbol_representations)
    } else {
        (owners_in_path, representations_in_path)
    };
    let owners = selected
        .iter()
        .map(|node| {
            let matched = if symbol_is_site && symbol.is_some() {
                symbol_hits(node)
            } else {
                node_anchors(node)
                    .filter(|anchor| in_path(anchor))
                    .cloned()
                    .collect()
            };
            Owner {
                id: node.id.clone(),
                kind: node.kind.clone(),
                name: node.name.clone(),
                primary_card_here: path.is_some() && in_path(&node.anchor),
                card: node.anchor.clone(),
                matched: dedup(matched),
                other_sites: dedup(
                    node_anchors(node)
                        .filter(|anchor| !in_path(anchor))
                        .cloned()
                        .collect(),
                ),
                counters: index.counters(&node.id),
                no_counter: node.no_counter.clone(),
                tests: index.tests(&node.id),
                span: span_policy(node),
                constrained_by: graph
                    .edges
                    .iter()
                    .filter(|edge| edge.kind == "constrains" && edge.to == node.id)
                    .map(|edge| {
                        format!(
                            "{} via: {}",
                            edge.from,
                            edge.detail.as_deref().unwrap_or("no carrier recorded")
                        )
                    })
                    .collect(),
            }
        })
        .collect::<Vec<_>>();

    let nearest_sites = if symbol_is_site {
        Vec::new()
    } else {
        let sites = selected
            .iter()
            .flat_map(|node| node_anchors(node))
            .filter(|anchor| in_path(anchor))
            .map(|anchor| anchor.symbol.as_str())
            .collect::<BTreeSet<_>>();
        nearest(symbol.as_deref().unwrap_or_default(), sites)
    };
    let nearest_files = match &path {
        Some(path) if owners.is_empty() && representations.is_empty() => {
            nearest(path, files.iter().map(String::as_str))
        }
        _ => Vec::new(),
    };

    Ok(OwnerAnswer {
        query: target.to_owned(),
        path,
        symbol,
        symbol_is_site,
        nearest_sites,
        nearest_files,
        owners,
        representations: representations
            .into_iter()
            .map(|node| OwnedRepresentation {
                id: node.id.clone(),
                anchor: node.anchor.clone(),
                produced_by: index.incoming(&node.id, "produces"),
                consumed_by: index.incoming(&node.id, "consumes"),
            })
            .collect(),
    })
}

impl Answer for OwnerAnswer {
    fn text(&self) -> String {
        let mut out = String::new();
        let place = match (&self.path, &self.symbol) {
            (Some(path), Some(symbol)) => format!("{path}::{symbol}"),
            (Some(path), None) => path.clone(),
            (None, Some(symbol)) => format!("symbol {symbol} in any file"),
            (None, None) => self.query.clone(),
        };
        line(
            &mut out,
            format!(
                "owner {place}: {} owner(s), {} representation(s). Owners are cards whose sites are here; a helper that no card lists as a site is not attributed.",
                self.owners.len(),
                self.representations.len()
            ),
        );
        if !self.symbol_is_site {
            line(
                &mut out,
                format!(
                    "note: no card names `{}` as a site in this file, so these are the owners of the whole file; nearest sites: {}",
                    self.symbol.as_deref().unwrap_or_default(),
                    list_or_none(&self.nearest_sites)
                ),
            );
        }
        if self.owners.is_empty() && self.representations.is_empty() {
            line(
                &mut out,
                format!(
                    "no card names a site here; docs/algorithm-cards.md lists card-less modules; nearest files with cards: {}",
                    list_or_none(&self.nearest_files)
                ),
            );
        }
        for owner in &self.owners {
            line(
                &mut out,
                format!(
                    "{} ({}{})  {}  {}",
                    owner.id,
                    owner.kind,
                    if owner.primary_card_here {
                        ", card here"
                    } else {
                        ""
                    },
                    owner.name.as_deref().unwrap_or("-"),
                    anchor_text(&owner.card)
                ),
            );
            line(
                &mut out,
                if owner.kind == "contract" {
                    format!("  card: the /// doc of {}", anchor_text(&owner.card))
                } else {
                    format!("  card: //! head of {}", owner.card.file)
                },
            );
            line(
                &mut out,
                format!("  matched sites: {}", sites_text(&owner.matched)),
            );
            if !owner.other_sites.is_empty() {
                line(
                    &mut out,
                    format!("  sites elsewhere: {}", sites_text(&owner.other_sites)),
                );
            }
            if owner.kind == "contract" {
                for constraint in &owner.constrained_by {
                    line(&mut out, format!("  constrained by: {constraint}"));
                }
                continue;
            }
            line(
                &mut out,
                format!(
                    "  counters: {}",
                    counters_text(&owner.counters, owner.no_counter.as_deref())
                ),
            );
            line(&mut out, format!("  tests: {}", tests_text(&owner.tests)));
            line(&mut out, format!("  span: {}", owner.span));
        }
        for representation in &self.representations {
            line(
                &mut out,
                format!(
                    "representation {}  produced by: {}; consumed by: {}  {}",
                    representation.id,
                    list_or_none(&representation.produced_by),
                    list_or_none(&representation.consumed_by),
                    anchor_text(&representation.anchor)
                ),
            );
        }
        out
    }
}

// ---------------------------------------------------------------------------------------------
// show

/// One node as a block: its card fields and every relation with its provenance.
#[derive(Clone, Debug, Serialize)]
pub struct ShowAnswer {
    pub node: Node,
    pub counters: Vec<CounterRef>,
    pub tests: Vec<String>,
    #[serde(rename = "relation")]
    pub relations: Vec<Relation>,
    pub caveat: String,
}

/// One relation of a shown node, stated from the node's side.
#[derive(Clone, Debug, Serialize)]
pub struct Relation {
    /// The stored edge kind, or `feeds` for the derived producer-to-consumer relation.
    pub kind: String,
    /// `out` when the shown node is the stored `from`, `in` when it is the stored `to`.
    pub direction: String,
    pub provenance: String,
    pub other: String,
    pub other_kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub order: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub consumer_site: Option<Anchor>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub anchor: Option<Anchor>,
}

/// Answer `show <id>` for any node id, a dotted counter name, or an `Algorithm` variant name.
pub fn show(graph: &Graph, id: &str) -> Result<ShowAnswer, NotFound> {
    let index = Index::new(graph);
    let node = index.resolve(id, "id")?;
    let mut relations = Vec::new();
    for edge in &graph.edges {
        let direction = if edge.from == node.id {
            "out"
        } else if edge.to == node.id {
            "in"
        } else {
            continue;
        };
        let other = if direction == "out" {
            &edge.to
        } else {
            &edge.from
        };
        if node.kind == "algorithm" && edge.kind == "measured-by" && direction == "out" {
            continue;
        }
        relations.push(Relation {
            kind: edge.kind.clone(),
            direction: direction.to_owned(),
            provenance: edge.provenance.clone(),
            other: other.clone(),
            other_kind: index.kind(other),
            detail: edge.detail.clone(),
            order: edge.order,
            consumer_site: edge.consumer_site.clone(),
            anchor: index.anchor(other),
        });
    }
    for (representation, consumer) in index.feeds_from(&node.id) {
        relations.push(Relation {
            kind: "feeds".to_owned(),
            direction: "out".to_owned(),
            provenance: "derived".to_owned(),
            other_kind: index.kind(&consumer),
            anchor: index.anchor(&consumer),
            other: consumer,
            detail: Some(representation),
            order: None,
            consumer_site: None,
        });
    }
    for (representation, producer) in index.feeds_into(&node.id) {
        relations.push(Relation {
            kind: "feeds".to_owned(),
            direction: "in".to_owned(),
            provenance: "derived".to_owned(),
            other_kind: index.kind(&producer),
            anchor: index.anchor(&producer),
            other: producer,
            detail: Some(representation),
            order: None,
            consumer_site: None,
        });
    }
    Ok(ShowAnswer {
        counters: index.counters(&node.id),
        tests: index.tests(&node.id),
        node: node.clone(),
        relations,
        caveat: ABSENT_RELATION_CAVEAT.to_owned(),
    })
}

impl Answer for ShowAnswer {
    fn text(&self) -> String {
        let node = &self.node;
        let mut out = String::new();
        line(
            &mut out,
            format!(
                "show {} ({}, provenance {})  {}",
                node.id,
                display_kind(node),
                node.provenance,
                anchor_text(&node.anchor)
            ),
        );
        let field = |out: &mut String, key: &str, value: Option<&str>| {
            if let Some(value) = value {
                line(out, format!("{key}: {value}"));
            }
        };
        field(
            &mut out,
            "name",
            node.name.as_deref().filter(|name| *name != node.id),
        );
        field(&mut out, "area", node.area.as_deref());
        if node.kind == "algorithm" && node.provenance == "declared" {
            field(
                &mut out,
                "card",
                Some(&format!("//! head of {}", node.anchor.file)),
            );
        }
        field(&mut out, "type", node.type_path.as_deref());
        field(&mut out, "role", node.role.as_deref());
        match (node.kind.as_str(), node.registry_name.as_deref()) {
            ("algorithm", Some(variant)) => {
                line(&mut out, format!("enum variant: Algorithm::{variant}"));
            }
            (_, name) => field(&mut out, "dotted name", name),
        }
        field(
            &mut out,
            "table",
            node.table.as_deref().filter(|_| node.kind != "algorithm"),
        );
        field(&mut out, "call", node.call.as_deref());
        field(&mut out, "behavior", node.behavior.as_deref());
        field(
            &mut out,
            "sequence",
            node.sequence
                .map(|sequence| sequence.to_string())
                .as_deref(),
        );
        if !node.generating_passes.is_empty() {
            field(
                &mut out,
                "generating passes",
                Some(&node.generating_passes.join(", ")),
            );
        }
        for cost in &node.cost {
            line(&mut out, format!("cost [{}]: {}", cost.mode, cost.bound));
        }
        field(&mut out, "variable", node.variable.as_deref());
        field(&mut out, "invariant", node.invariant.as_deref());
        if !node.lean.is_empty() {
            field(&mut out, "lean", Some(&node.lean.join(", ")));
        }
        if node.kind == "algorithm" {
            line(
                &mut out,
                format!(
                    "counters: {}",
                    counters_text(&self.counters, node.no_counter.as_deref())
                ),
            );
            line(&mut out, format!("tests: {}", tests_text(&self.tests)));
            line(&mut out, format!("span: {}", span_policy(node)));
        }
        if !node.sites.is_empty() {
            line(&mut out, "sites:".to_owned());
            for site in &node.sites {
                line(&mut out, format!("  {}", anchor_text(site)));
            }
        }
        line(
            &mut out,
            format!("relations [provenance] ({}):", self.caveat),
        );
        if self.relations.is_empty() {
            line(&mut out, "  none declared".to_owned());
        }
        for relation in &self.relations {
            let verb = relation_verb(&relation.kind, &relation.direction);
            let mut text = format!("  {verb} {} [{}]", relation.other, relation.provenance);
            if relation.kind == "feeds" {
                text.push_str(&format!(
                    " via {}",
                    relation.detail.as_deref().unwrap_or("?")
                ));
            } else if let Some(detail) = &relation.detail {
                text.push_str(&format!(" via: {detail}"));
            }
            if let Some(order) = relation.order
                && relation.kind == "falls-back-to"
            {
                text.push_str(&format!(" (ladder position {order})"));
            }
            if let Some(site) = &relation.consumer_site {
                text.push_str(&format!("  consumer site {}", anchor_text(site)));
            } else if let Some(anchor) = &relation.anchor {
                text.push_str(&format!("  {}", anchor_text(anchor)));
            }
            line(&mut out, text);
        }
        out
    }
}

fn relation_verb(kind: &str, direction: &str) -> String {
    match (kind, direction) {
        ("produces", "out") => "produces".to_owned(),
        ("produces", "in") => "produced by".to_owned(),
        ("consumes", "out") => "consumes".to_owned(),
        ("consumes", "in") => "consumed by".to_owned(),
        ("feeds", "out") => "feeds".to_owned(),
        ("feeds", "in") => "fed by".to_owned(),
        ("constrains", "out") => "constrains".to_owned(),
        ("constrains", "in") => "constrained by".to_owned(),
        ("variant-of", "out") => "variant of".to_owned(),
        ("variant-of", "in") => "has variant".to_owned(),
        ("falls-back-to", "out") => "falls back to".to_owned(),
        ("falls-back-to", "in") => "is the fallback of".to_owned(),
        ("contains", "out") => "contains".to_owned(),
        ("contains", "in") => "runs in phase".to_owned(),
        ("follows", "out") => "precedes phase".to_owned(),
        ("follows", "in") => "comes after phase".to_owned(),
        ("measured-by", "out") => "measured by".to_owned(),
        ("measured-by", "in") => "measures".to_owned(),
        (kind, "out") => kind.to_owned(),
        (kind, _) => format!("{kind} (incoming)"),
    }
}

// ---------------------------------------------------------------------------------------------
// impact

/// The downstream closure of one node.
#[derive(Clone, Debug, Serialize)]
pub struct ImpactAnswer {
    pub origin: String,
    pub origin_kind: String,
    pub origin_anchor: Anchor,
    pub caveat: String,
    /// Algorithms and contracts reached, in breadth-first order.
    pub reached: Vec<Reached>,
    /// Counters of the origin and of every reached algorithm.
    pub counters: Vec<CounterImpact>,
    /// Tests declared by the origin or a reached algorithm.
    pub tests: Vec<TestImpact>,
    /// Relations of the origin that the closure does not follow.
    pub not_followed: Vec<NotFollowed>,
}

/// One reached algorithm or contract.
#[derive(Clone, Debug, Serialize)]
pub struct Reached {
    pub id: String,
    pub kind: String,
    /// `declared` when reached through card relations alone; `stage-order` when every path
    /// needs the phase order of the stage table.
    pub class: String,
    pub anchor: Anchor,
    pub path: Vec<Hop>,
}

/// One step of an impact path, stated in the direction of traversal.
#[derive(Clone, Debug, Serialize)]
pub struct Hop {
    pub from: String,
    /// `produces`, `consumed-by`, `constrains`, `is-fallback-of`, `has-variant`, `runs-in`,
    /// `precedes`, or `contains`.
    pub step: String,
    pub to: String,
    /// The stored edge kind the step reads.
    pub edge: String,
    pub provenance: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// For a `constrains` step: the consumer site that relies on the producer.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub consumer_site: Option<Anchor>,
}

/// A counter to re-measure and the algorithms that declare it.
#[derive(Clone, Debug, Serialize)]
pub struct CounterImpact {
    pub variant: String,
    pub name: String,
    /// `declared` when the origin or a card-relation reached algorithm declares it.
    pub class: String,
    pub algorithms: Vec<String>,
}

/// A declared test path and the algorithms that name it.
#[derive(Clone, Debug, Serialize)]
pub struct TestImpact {
    pub path: String,
    pub algorithms: Vec<String>,
}

/// A relation of the origin that is not a dependency in the traversal direction.
#[derive(Clone, Debug, Serialize)]
pub struct NotFollowed {
    pub edge: String,
    pub other: String,
    pub reason: String,
}

/// How the traversal reached a node; it limits the phase steps taken from it.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Reach {
    /// The origin, or reached through a card relation: an algorithm continues into the phases
    /// after every phase that contains it, and a phase affects every algorithm it contains.
    Full,
    /// A phase entered from an algorithm it contains: only the phases after it are affected,
    /// not the other algorithms of the same phase.
    Container,
    /// An algorithm reached because a phase that contains it runs after a changed phase. The
    /// change reaches it in that phase only, whose successors the phase order already covers,
    /// so it does not continue into its other phases, some of which may run earlier.
    InPhase,
}

/// Answer `impact <id>`.
///
/// The closure follows, from the origin:
/// `produces` then `consumes` through a shared representation id (type and role);
/// declared `constrains` from producer to consumer;
/// `falls-back-to` and `variant-of` read backwards, since a change to the fallback or to the
/// general algorithm changes the caller or the specialised copy;
/// and, in a second class, derived `contains` and table `follows` phase order.
/// `measured-by` is never followed: counters and tests are listed, not traversed.
pub fn impact(graph: &Graph, id: &str) -> Result<ImpactAnswer, NotFound> {
    let index = Index::new(graph);
    let origin = index.resolve(id, "id")?;
    if origin.kind == "observation" {
        return Err(NotFound {
            what: "dependency source".to_owned(),
            query: id.to_owned(),
            candidates: index.incoming(&origin.id, "measured-by"),
            hint: Some(format!(
                "{} is a {}, which measures algorithms and is not a dependency; the candidates are the algorithms it measures",
                origin.id,
                display_kind(origin)
            )),
        });
    }
    let declared = closure(&index, &origin.id, false);
    let full = closure(&index, &origin.id, true);

    let reportable = |id: &str| matches!(index.kind(id).as_str(), "algorithm" | "contract");
    let mut reached = Vec::new();
    for (class, paths) in [("declared", &declared), ("stage-order", &full)] {
        for (id, path) in paths {
            if id == &origin.id || !reportable(id) {
                continue;
            }
            if class == "stage-order" && declared.iter().any(|(known, _)| known == id) {
                continue;
            }
            reached.push(Reached {
                id: id.clone(),
                kind: index.kind(id),
                class: class.to_owned(),
                anchor: index.anchor(id).unwrap_or_else(|| origin.anchor.clone()),
                path: path.clone(),
            });
        }
    }

    let declared_ids = std::iter::once(origin.id.as_str())
        .chain(
            reached
                .iter()
                .filter(|reached| reached.class == "declared")
                .map(|reached| reached.id.as_str()),
        )
        .collect::<BTreeSet<_>>();
    let mut counters = BTreeMap::<CounterRef, BTreeSet<String>>::new();
    let mut tests = BTreeMap::<String, BTreeSet<String>>::new();
    for id in std::iter::once(origin.id.as_str()).chain(reached.iter().map(|r| r.id.as_str())) {
        for counter in index.counters(id) {
            counters.entry(counter).or_default().insert(id.to_owned());
        }
        for test in index.tests(id) {
            tests.entry(test).or_default().insert(id.to_owned());
        }
    }
    let mut counters = counters
        .into_iter()
        .map(|(counter, algorithms)| CounterImpact {
            class: if algorithms
                .iter()
                .any(|id| declared_ids.contains(id.as_str()))
            {
                "declared".to_owned()
            } else {
                "stage-order".to_owned()
            },
            variant: counter.variant,
            name: counter.name,
            algorithms: algorithms.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    counters.sort_by(|left, right| (&left.class, &left.name).cmp(&(&right.class, &right.name)));

    let mut not_followed = Vec::new();
    for edge in graph.edges.iter().filter(|edge| edge.from == origin.id) {
        let reason = match edge.kind.as_str() {
            "falls-back-to" => {
                "the origin falls back to it: a change to the origin changes which inputs reach it, not what it computes"
            }
            "variant-of" if edge.to != origin.id => {
                "the origin is a specialised copy of it: a change to the copy does not change the general algorithm"
            }
            _ => continue,
        };
        not_followed.push(NotFollowed {
            edge: edge.kind.clone(),
            other: edge.to.clone(),
            reason: reason.to_owned(),
        });
    }

    Ok(ImpactAnswer {
        origin: origin.id.clone(),
        origin_kind: origin.kind.clone(),
        origin_anchor: origin.anchor.clone(),
        caveat: ABSENT_RELATION_CAVEAT.to_owned(),
        reached,
        counters,
        tests: tests
            .into_iter()
            .map(|(path, algorithms)| TestImpact {
                path,
                algorithms: algorithms.into_iter().collect(),
            })
            .collect(),
        not_followed,
    })
}

/// Breadth-first closure from `origin`; the path of each node is its first-found shortest path.
fn closure(index: &Index<'_>, origin: &str, stage_order: bool) -> Vec<(String, Vec<Hop>)> {
    let start = (origin.to_owned(), Reach::Full);
    let mut seen = BTreeSet::from([start.clone()]);
    let mut first_path = BTreeMap::<String, usize>::new();
    let mut order = vec![(origin.to_owned(), Vec::<Hop>::new())];
    first_path.insert(origin.to_owned(), 0);
    let mut queue = VecDeque::from([(start, Vec::<Hop>::new())]);
    while let Some(((current, entry), path)) = queue.pop_front() {
        for (hop, next_entry) in steps(index, origin, &current, entry, stage_order) {
            let state = (hop.to.clone(), next_entry);
            if hop.to == current || !seen.insert(state.clone()) {
                continue;
            }
            let mut next_path = path.clone();
            next_path.push(hop);
            if !first_path.contains_key(&state.0) {
                first_path.insert(state.0.clone(), order.len());
                order.push((state.0.clone(), next_path.clone()));
            }
            queue.push_back((state, next_path));
        }
    }
    order
}

/// The steps from `current`. Phase steps are taken only when `stage_order` is set, except that
/// a phase origin always reaches the algorithms it contains.
fn steps(
    index: &Index<'_>,
    origin: &str,
    current: &str,
    entry: Reach,
    stage_order: bool,
) -> Vec<(Hop, Reach)> {
    let mut steps = Vec::new();
    let hop = |edge: &Edge, step: &str, reversed: bool| Hop {
        from: current.to_owned(),
        step: step.to_owned(),
        to: if reversed {
            edge.from.clone()
        } else {
            edge.to.clone()
        },
        edge: edge.kind.clone(),
        provenance: edge.provenance.clone(),
        detail: edge.detail.clone(),
        consumer_site: edge.consumer_site.clone(),
    };
    let is_phase = index.kind(current) == "phase";
    for edge in &index.graph.edges {
        if edge.from == current {
            match edge.kind.as_str() {
                "produces" => steps.push((hop(edge, "produces", false), Reach::Full)),
                "constrains" => steps.push((hop(edge, "constrains", false), Reach::Full)),
                "follows" if stage_order => steps.push((hop(edge, "precedes", false), Reach::Full)),
                "contains"
                    if (stage_order || current == origin) && is_phase && entry == Reach::Full =>
                {
                    steps.push((hop(edge, "contains", false), Reach::InPhase))
                }
                _ => {}
            }
        }
        if edge.to == current {
            match edge.kind.as_str() {
                "consumes" => steps.push((hop(edge, "consumed-by", true), Reach::Full)),
                "falls-back-to" => steps.push((hop(edge, "is-fallback-of", true), Reach::Full)),
                "variant-of" => steps.push((hop(edge, "has-variant", true), Reach::Full)),
                "contains" if stage_order && !is_phase && entry == Reach::Full => {
                    steps.push((hop(edge, "runs-in", true), Reach::Container))
                }
                _ => {}
            }
        }
    }
    steps
}

impl Answer for ImpactAnswer {
    fn text(&self) -> String {
        let mut out = String::new();
        let (declared, staged): (Vec<_>, Vec<_>) = self
            .reached
            .iter()
            .partition(|reached| reached.class == "declared");
        line(
            &mut out,
            format!(
                "impact {} ({}): {} reached by card relations, {} more only by stage order; {}.",
                self.origin,
                self.origin_kind,
                declared.len(),
                staged.len(),
                self.caveat
            ),
        );
        line(
            &mut out,
            format!("origin  {}", anchor_text(&self.origin_anchor)),
        );
        line(
            &mut out,
            "Each reached item names the earlier item it was reached from and the steps between; follow `from` back to the origin for the whole path.".to_owned(),
        );
        let known = std::iter::once(self.origin.as_str())
            .chain(self.reached.iter().map(|reached| reached.id.as_str()))
            .collect::<BTreeSet<_>>();
        line(
            &mut out,
            "card relations [declared]: produces then consumed-by through one representation (type and role); constrains; is-fallback-of and has-variant read falls-back-to and variant-of backwards:".to_owned(),
        );
        if declared.is_empty() {
            line(&mut out, "  none".to_owned());
        }
        for reached in &declared {
            reached_text(&mut out, reached, &known);
        }
        line(
            &mut out,
            "stage order only: runs-in and contains [derived] match stage calls to card sites, precedes [table] is the stage order; a later phase reads what earlier phases rewrote but need not depend on this change:".to_owned(),
        );
        if staged.is_empty() {
            line(&mut out, "  none".to_owned());
        }
        for reached in &staged {
            reached_text(&mut out, reached, &known);
        }
        for (class, heading) in [
            (
                "declared",
                "counters to re-measure (origin and card relations):",
            ),
            ("stage-order", "counters of stage-order-only algorithms:"),
        ] {
            let counters = self
                .counters
                .iter()
                .filter(|counter| counter.class == class)
                .collect::<Vec<_>>();
            if counters.is_empty() && class == "stage-order" {
                continue;
            }
            line(&mut out, heading.to_owned());
            if counters.is_empty() {
                line(&mut out, "  none declared".to_owned());
            }
            for counter in counters {
                line(
                    &mut out,
                    format!(
                        "  {} ({}) of {}  crates/k-rust-kore/src/measure.rs::Counter::{}",
                        counter.name,
                        counter.variant,
                        counter.algorithms.join(", "),
                        counter.variant
                    ),
                );
            }
        }
        if self.tests.is_empty() {
            line(
                &mut out,
                "tests to rerun: none; no card among these lists `tests`".to_owned(),
            );
        } else {
            line(&mut out, "tests to rerun:".to_owned());
        }
        for test in &self.tests {
            line(
                &mut out,
                format!("  {} named by {}", test.path, test.algorithms.join(", ")),
            );
        }
        for relation in &self.not_followed {
            line(
                &mut out,
                format!(
                    "not followed: {} {} {}: {}",
                    self.origin, relation.edge, relation.other, relation.reason
                ),
            );
        }
        out
    }
}

fn reached_text(out: &mut String, reached: &Reached, known: &BTreeSet<&str>) {
    let kind = if reached.kind == "algorithm" {
        String::new()
    } else {
        format!(" ({})", reached.kind)
    };
    line(
        out,
        format!("  {}{kind}  {}", reached.id, anchor_text(&reached.anchor)),
    );
    let start = reached
        .path
        .iter()
        .rposition(|hop| known.contains(hop.from.as_str()))
        .unwrap_or(0);
    line(
        out,
        format!("    from {}", segment_text(&reached.path[start..])),
    );
    for hop in reached.path[start..]
        .iter()
        .filter(|hop| hop.edge == "constrains")
    {
        if let Some(detail) = &hop.detail {
            line(
                out,
                format!(
                    "    via: {detail}{}",
                    hop.consumer_site
                        .as_ref()
                        .map(|site| format!("  consumer site {}", anchor_text(site)))
                        .unwrap_or_default()
                ),
            );
        }
    }
}

/// Render the steps of a path segment up to, not including, its last node; runs of more than
/// two `precedes` steps collapse to their ends.
fn segment_text(path: &[Hop]) -> String {
    let Some(first) = path.first() else {
        return String::new();
    };
    let mut text = first.from.clone();
    let mut index = 0;
    while index < path.len() {
        let hop = &path[index];
        let run = path[index..]
            .iter()
            .take_while(|hop| hop.step == "precedes")
            .count();
        let (step, target, advance) = if run > 2 {
            (format!("precedes x{run}"), &path[index + run - 1].to, run)
        } else {
            (hop.step.clone(), &hop.to, 1)
        };
        index += advance;
        text.push_str(&format!(" -{step}->"));
        if index < path.len() {
            text.push_str(&format!(" {target}"));
        }
    }
    text
}

// ---------------------------------------------------------------------------------------------
// hot

/// Which join column orders `hot`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum HotOrder {
    SelfSeconds,
    Total,
    Count,
}

/// The identity of the run a join describes.
#[derive(Clone, Debug, Serialize)]
pub struct RunIdentity {
    pub workload: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub claim: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub krust_revision: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timestamp: Option<String>,
    pub receipt: String,
    pub partial: bool,
}

/// The algorithms of one run with the most time or invocations.
#[derive(Clone, Debug, Serialize)]
pub struct HotAnswer {
    pub run: RunIdentity,
    pub by: String,
    pub timed_algorithms: usize,
    pub all_self_seconds: f64,
    pub note: String,
    #[serde(rename = "algorithm")]
    pub rows: Vec<HotRow>,
    /// Algorithms without a span invocation whose declared counters moved; they have no time,
    /// and their verdict is unknown because a counter is not attributed to one algorithm.
    pub counter_only: Vec<String>,
    /// Algorithms that ran by coverage evidence without a span invocation; they have no time.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub coverage_untimed: Vec<String>,
}

/// One timed algorithm.
#[derive(Clone, Debug, Serialize)]
pub struct HotRow {
    pub rank: usize,
    pub id: String,
    pub count: u64,
    pub self_seconds: f64,
    pub total_seconds: f64,
    /// False when the current graph has no algorithm with this id.
    pub in_graph: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub anchor: Option<Anchor>,
    pub cost: Vec<Cost>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub variable: Option<String>,
    /// False when the card declares no counter.
    pub card_has_counters: bool,
    /// Nonzero counters the card declares.
    pub declared_counters: Vec<CounterObservation>,
    /// Counters the card does not declare that moved in the algorithm's spans outside nested
    /// algorithm spans.
    pub undeclared_self_counters: Vec<CounterObservation>,
    /// Counters the card does not declare that moved only inside nested algorithm spans.
    pub nested_only_counters: Vec<String>,
}

/// One nonzero counter observation.
#[derive(Clone, Debug, Serialize)]
pub struct CounterObservation {
    pub name: String,
    /// Delta inside the algorithm's spans, excluding nested algorithm spans.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span_self: Option<u64>,
    /// Delta inside the algorithm's spans, including nested algorithm spans.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span_total: Option<u64>,
    /// Process-wide value from the receipt; not attributed to one algorithm.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub receipt_total: Option<u64>,
}

/// Answer `hot --join <join.toml>`.
pub fn hot(graph: &Graph, join: &Join, by: HotOrder, limit: usize) -> HotAnswer {
    let index = Index::new(graph);
    let mut timed = join
        .algorithms
        .iter()
        .filter(|algorithm| algorithm.count > 0)
        .collect::<Vec<_>>();
    let key = |algorithm: &AlgorithmRun| match by {
        HotOrder::SelfSeconds => algorithm.self_seconds,
        HotOrder::Total => algorithm.total_seconds,
        HotOrder::Count => algorithm.count as f64,
    };
    timed.sort_by(|left, right| {
        key(right)
            .total_cmp(&key(left))
            .then_with(|| left.id.cmp(&right.id))
    });
    let all_self_seconds = timed.iter().map(|algorithm| algorithm.self_seconds).sum();
    let rows = timed
        .iter()
        .take(limit)
        .enumerate()
        .map(|(rank, algorithm)| {
            let node = index
                .nodes
                .get(algorithm.id.as_str())
                .filter(|node| node.kind == "algorithm");
            let observation = |counter: &crate::AlgorithmCounter| CounterObservation {
                name: counter.name.clone(),
                span_self: counter.trace_self,
                span_total: counter.trace_total,
                receipt_total: counter.receipt_total,
            };
            let moved_in_span = |counter: &crate::AlgorithmCounter| {
                counter.trace_total.unwrap_or(0) > 0 || counter.trace_self.unwrap_or(0) > 0
            };
            HotRow {
                rank: rank + 1,
                id: algorithm.id.clone(),
                count: algorithm.count,
                self_seconds: algorithm.self_seconds,
                total_seconds: algorithm.total_seconds,
                in_graph: node.is_some(),
                anchor: node.map(|node| node.anchor.clone()),
                cost: node.map_or_else(|| algorithm.cost.clone(), |node| node.cost.clone()),
                variable: node.and_then(|node| node.variable.clone()),
                declared_counters: algorithm
                    .counters
                    .iter()
                    .filter(|counter| counter.declared)
                    .filter(|counter| {
                        moved_in_span(counter) || counter.receipt_total.unwrap_or(0) > 0
                    })
                    .map(observation)
                    .collect(),
                card_has_counters: algorithm.counters.iter().any(|counter| counter.declared),
                undeclared_self_counters: algorithm
                    .counters
                    .iter()
                    .filter(|counter| !counter.declared && counter.trace_self.unwrap_or(0) > 0)
                    .map(observation)
                    .collect(),
                nested_only_counters: algorithm
                    .counters
                    .iter()
                    .filter(|counter| {
                        !counter.declared
                            && counter.trace_self.unwrap_or(0) == 0
                            && counter.trace_total.unwrap_or(0) > 0
                    })
                    .map(|counter| counter.name.clone())
                    .collect(),
            }
        })
        .collect();
    HotAnswer {
        run: run_identity(join),
        by: match by {
            HotOrder::SelfSeconds => "self",
            HotOrder::Total => "total",
            HotOrder::Count => "count",
        }
        .to_owned(),
        timed_algorithms: timed.len(),
        all_self_seconds,
        note: "times are span wall-clock seconds from one run; self excludes nested algorithm spans, total includes them; card cost and variable are read from the current checkout".to_owned(),
        rows,
        counter_only: join
            .nodes
            .iter()
            .filter(|node| node.kind == "algorithm" && node.evidence == "counter-moved")
            .map(|node| node.id.clone())
            .collect(),
        coverage_untimed: join
            .nodes
            .iter()
            .filter(|node| {
                node.kind == "algorithm"
                    && node.evidence == "coverage"
                    && node.verdict == Verdict::Ran
            })
            .filter(|node| {
                join.algorithms
                    .iter()
                    .any(|algorithm| algorithm.id == node.id && algorithm.count == 0)
            })
            .map(|node| node.id.clone())
            .collect(),
    }
}

impl Answer for HotAnswer {
    fn text(&self) -> String {
        let mut out = String::new();
        line(
            &mut out,
            format!(
                "hot by {}: top {} of {} timed algorithms in {}; {}.",
                self.by,
                self.rows.len(),
                self.timed_algorithms,
                run_text(&self.run),
                self.note
            ),
        );
        for row in &self.rows {
            let share = if self.all_self_seconds > 0.0 {
                format!(
                    " ({:.1}% of all algorithm self time)",
                    100.0 * row.self_seconds / self.all_self_seconds
                )
            } else {
                String::new()
            };
            line(
                &mut out,
                format!(
                    "{}. {}  self {:.4}s{share}  total {:.4}s  count {}  {}",
                    row.rank,
                    row.id,
                    row.self_seconds,
                    row.total_seconds,
                    row.count,
                    row.anchor
                        .as_ref()
                        .map_or_else(|| "(not in the current graph)".to_owned(), anchor_text)
                ),
            );
            for cost in &row.cost {
                line(&mut out, format!("   cost [{}]: {}", cost.mode, cost.bound));
            }
            if let Some(variable) = &row.variable {
                line(&mut out, format!("   variable: {variable}"));
            }
            line(
                &mut out,
                format!(
                    "   declared counters: {}",
                    if row.card_has_counters {
                        observations_text(&row.declared_counters)
                    } else {
                        "none on the card".to_owned()
                    }
                ),
            );
            if !row.undeclared_self_counters.is_empty() {
                line(
                    &mut out,
                    format!(
                        "   undeclared counters moved outside nested spans (its own code or unspanned algorithms it calls): {}",
                        observations_text(&row.undeclared_self_counters)
                    ),
                );
            }
            if !row.nested_only_counters.is_empty() {
                line(
                    &mut out,
                    format!(
                        "   moved only inside nested algorithm spans: {}",
                        row.nested_only_counters.join(", ")
                    ),
                );
            }
        }
        if !self.counter_only.is_empty() {
            line(
                &mut out,
                format!(
                    "no span but declared counters moved, so untimed and of unknown verdict: {}",
                    self.counter_only.join(", ")
                ),
            );
        }
        if !self.coverage_untimed.is_empty() {
            line(
                &mut out,
                format!(
                    "ran by coverage without opening a span, so untimed: {}",
                    self.coverage_untimed.join(", ")
                ),
            );
        }
        out
    }
}

fn observations_text(observations: &[CounterObservation]) -> String {
    if observations.is_empty() {
        return "none nonzero".to_owned();
    }
    observations
        .iter()
        .map(|observation| {
            if observation.span_total.unwrap_or(0) > 0 || observation.span_self.unwrap_or(0) > 0 {
                format!(
                    "{} self={} total={}",
                    observation.name,
                    observation.span_self.unwrap_or(0),
                    observation.span_total.unwrap_or(0)
                )
            } else {
                format!(
                    "{} receipt={} (process-wide, not in these spans)",
                    observation.name,
                    observation.receipt_total.unwrap_or(0)
                )
            }
        })
        .collect::<Vec<_>>()
        .join("; ")
}

// ---------------------------------------------------------------------------------------------
// unexercised

/// The declared algorithms and edges one run did not show running, split by verdict.
#[derive(Clone, Debug, Serialize)]
pub struct UnexercisedAnswer {
    pub run: RunIdentity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub area: Option<String>,
    pub declared_algorithms: usize,
    /// The join's verdict rule.
    pub rule: String,
    /// False when the edge list was not requested.
    pub edges_listed: bool,
    /// Algorithms whose instrumentation would have recorded them and recorded nothing.
    pub not_run: Vec<UnexercisedAlgorithm>,
    /// Algorithms whose evidence in this run cannot tell whether they ran.
    pub unknown: Vec<UnexercisedAlgorithm>,
    /// Edges per kind in the join after the area filter, whatever their verdict.
    pub edge_totals: BTreeMap<String, usize>,
    #[serde(rename = "edge")]
    pub edges: Vec<UnexercisedEdge>,
}

/// One declared algorithm whose verdict is `not-run` or `unknown`.
#[derive(Clone, Debug, Serialize)]
pub struct UnexercisedAlgorithm {
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub area: Option<String>,
    /// The span policy at the receipt's commit, or `absent`.
    pub span: String,
    pub declared_counters: Vec<String>,
    /// The join's evidence code and sentence for the verdict.
    pub evidence: String,
    pub reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub anchor: Option<Anchor>,
}

/// One graph edge whose verdict is `not-run` or `unknown`.
#[derive(Clone, Debug, Serialize)]
pub struct UnexercisedEdge {
    pub kind: String,
    pub from: String,
    pub to: String,
    pub provenance: String,
    pub verdict: Verdict,
    pub evidence: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub anchor: Option<Anchor>,
}

/// Answer `unexercised --join <join.toml> [--area A]` from the join's verdicts.
pub fn unexercised(
    graph: &Graph,
    join: &Join,
    area: Option<&str>,
    include_edges: bool,
) -> Result<UnexercisedAnswer, NotFound> {
    let index = Index::new(graph);
    let areas = join
        .algorithms
        .iter()
        .filter_map(|algorithm| algorithm.area.as_deref())
        .collect::<BTreeSet<_>>();
    if let Some(area) = area
        && !areas.contains(area)
    {
        return Err(NotFound {
            what: "area".to_owned(),
            query: area.to_owned(),
            candidates: nearest(area, areas.iter().copied()),
            hint: Some(format!(
                "areas in this join: {}",
                areas.iter().copied().collect::<Vec<_>>().join(", ")
            )),
        });
    }
    let verdicts = join
        .nodes
        .iter()
        .filter(|node| node.kind == "algorithm")
        .map(|node| (node.id.as_str(), node))
        .collect::<BTreeMap<_, _>>();
    let in_area =
        |algorithm_area: Option<&str>| area.is_none_or(|area| algorithm_area == Some(area));
    let declared = join
        .algorithms
        .iter()
        .filter(|algorithm| algorithm.declared && in_area(algorithm.area.as_deref()))
        .collect::<Vec<_>>();
    let with_verdict = |verdict: Verdict| {
        declared
            .iter()
            .filter_map(|algorithm| {
                let node = verdicts.get(algorithm.id.as_str())?;
                (node.verdict == verdict).then(|| UnexercisedAlgorithm {
                    id: algorithm.id.clone(),
                    area: algorithm.area.clone(),
                    span: algorithm
                        .span_policy
                        .clone()
                        .unwrap_or_else(|| "absent".to_owned()),
                    declared_counters: algorithm
                        .counters
                        .iter()
                        .filter(|counter| counter.declared)
                        .map(|counter| counter.name.clone())
                        .collect(),
                    evidence: node.evidence.clone(),
                    reason: node.reason.clone(),
                    anchor: index.anchor(&algorithm.id),
                })
            })
            .collect::<Vec<_>>()
    };
    let not_run = with_verdict(Verdict::NotRun);
    let unknown = with_verdict(Verdict::Unknown);
    let edge_area = |id: &str| {
        index
            .nodes
            .get(id)
            .and_then(|node| node.area.as_deref())
            .or_else(|| {
                join.algorithms
                    .iter()
                    .find(|algorithm| algorithm.id == id)
                    .and_then(|algorithm| algorithm.area.as_deref())
            })
    };
    let area_edges = join
        .edges
        .iter()
        .filter(|edge| {
            area.is_none() || in_area(edge_area(&edge.from)) || in_area(edge_area(&edge.to))
        })
        .collect::<Vec<_>>();
    let mut edge_totals = BTreeMap::new();
    if include_edges {
        for edge in &area_edges {
            *edge_totals.entry(edge.kind.clone()).or_insert(0) += 1;
        }
    }
    let edges = if include_edges {
        area_edges
            .iter()
            .filter(|edge| edge.verdict != Verdict::Ran)
            .map(|edge| UnexercisedEdge {
                kind: edge.kind.clone(),
                from: edge.from.clone(),
                to: edge.to.clone(),
                provenance: edge.provenance.clone(),
                verdict: edge.verdict,
                evidence: edge.evidence.clone(),
                anchor: [edge.from.as_str(), edge.to.as_str()]
                    .into_iter()
                    .find(|id| matches!(index.kind(id).as_str(), "algorithm" | "contract"))
                    .and_then(|id| index.anchor(id)),
            })
            .collect()
    } else {
        Vec::new()
    };
    Ok(UnexercisedAnswer {
        run: run_identity(join),
        area: area.map(ToOwned::to_owned),
        declared_algorithms: declared.len(),
        rule: join.verdict_rule.clone(),
        edges_listed: include_edges,
        not_run,
        unknown,
        edge_totals,
        edges,
    })
}

impl Answer for UnexercisedAnswer {
    fn text(&self) -> String {
        let mut out = String::new();
        line(
            &mut out,
            format!(
                "not shown running in {}{}: {} of {} declared algorithms ({} not-run, {} unknown), {}.",
                run_text(&self.run),
                self.area
                    .as_deref()
                    .map(|area| format!(", area {area}"))
                    .unwrap_or_default(),
                self.not_run.len() + self.unknown.len(),
                self.declared_algorithms,
                self.not_run.len(),
                self.unknown.len(),
                if self.edges_listed {
                    format!("{} edges", self.edges.len())
                } else {
                    "edges not listed".to_owned()
                },
            ),
        );
        line(&mut out, format!("rule: {}", self.rule));
        line(
            &mut out,
            format!(
                "not-run ({}; the instrumentation would have recorded them and recorded nothing):",
                self.not_run.len()
            ),
        );
        for algorithm in &self.not_run {
            unexercised_line(&mut out, algorithm);
        }
        line(
            &mut out,
            format!(
                "unknown ({}; this run's evidence cannot tell whether they ran):",
                self.unknown.len()
            ),
        );
        for algorithm in &self.unknown {
            unexercised_line(&mut out, algorithm);
        }
        let mut kinds = BTreeMap::<(&str, Verdict), Vec<&UnexercisedEdge>>::new();
        for edge in &self.edges {
            kinds
                .entry((edge.kind.as_str(), edge.verdict))
                .or_default()
                .push(edge);
        }
        let mut rules_stated = BTreeSet::new();
        for ((kind, verdict), edges) in kinds {
            let total = self.edge_totals.get(kind).copied().unwrap_or(edges.len());
            if rules_stated.insert(kind) {
                line(
                    &mut out,
                    format!("edges {kind}: {}", edge_verdict_rule(kind)),
                );
            }
            if edges.len() > 5 {
                line(
                    &mut out,
                    format!(
                        "  {}: {} of {total}; listed in --format toml",
                        verdict.as_str(),
                        edges.len()
                    ),
                );
                continue;
            }
            line(
                &mut out,
                format!("  {}: {} of {total}:", verdict.as_str(), edges.len()),
            );
            for edge in edges {
                line(
                    &mut out,
                    format!(
                        "    {} -> {} [{}] {}{}",
                        edge.from,
                        edge.to,
                        edge.provenance,
                        edge.evidence,
                        edge.anchor
                            .as_ref()
                            .map(|anchor| format!("  {}", anchor_text(anchor)))
                            .unwrap_or_default()
                    ),
                );
            }
        }
        out
    }
}

fn unexercised_line(out: &mut String, algorithm: &UnexercisedAlgorithm) {
    line(
        out,
        format!(
            "  {}  {}  span={} counters={}  {}",
            algorithm.id,
            algorithm.evidence,
            algorithm.span,
            if algorithm.declared_counters.is_empty() {
                "none".to_owned()
            } else {
                algorithm.declared_counters.join(",")
            },
            algorithm
                .anchor
                .as_ref()
                .map_or_else(|| "(not in the current graph)".to_owned(), anchor_text)
        ),
    );
}

// ---------------------------------------------------------------------------------------------
// search

/// Nodes whose id, name, type, files, or symbols contain every word of the text.
#[derive(Clone, Debug, Serialize)]
pub struct SearchAnswer {
    pub text: String,
    pub total: usize,
    #[serde(rename = "match")]
    pub matches: Vec<SearchMatch>,
}

/// One node that matched.
#[derive(Clone, Debug, Serialize)]
pub struct SearchMatch {
    pub kind: String,
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// The field that holds the first word, such as `id`, `name`, `site`, or `file`.
    pub field: String,
    pub value: String,
    pub anchor: Anchor,
}

/// Answer `search <text>`: case-insensitive; every whitespace-separated word must occur in
/// some field of the node.
pub fn search(graph: &Graph, text: &str, limit: usize) -> SearchAnswer {
    let words = text
        .split_whitespace()
        .map(str::to_lowercase)
        .collect::<Vec<_>>();
    let kind_rank = |kind: &str| match kind {
        "algorithm" => 0,
        "contract" => 1,
        "representation" => 2,
        "counter" => 3,
        "test" => 4,
        "phase" => 5,
        _ => 6,
    };
    let mut matches = Vec::new();
    for node in &graph.nodes {
        let mut fields = vec![("id", node.id.clone(), node.anchor.clone())];
        for (key, value) in [
            ("name", &node.name),
            ("registry name", &node.registry_name),
            ("type", &node.type_path),
            ("call", &node.call),
            ("behavior", &node.behavior),
        ] {
            if let Some(value) = value {
                fields.push((key, value.clone(), node.anchor.clone()));
            }
        }
        for anchor in std::iter::once(&node.anchor).chain(&node.sites) {
            fields.push(("site", anchor.symbol.clone(), anchor.clone()));
            fields.push(("file", anchor.file.clone(), anchor.clone()));
        }
        let lowered = fields
            .iter()
            .map(|(_, value, _)| value.to_lowercase())
            .collect::<Vec<_>>();
        if words.is_empty()
            || !words
                .iter()
                .all(|word| lowered.iter().any(|value| value.contains(word)))
        {
            continue;
        }
        let first = lowered
            .iter()
            .position(|value| value.contains(&words[0]))
            .unwrap_or(0);
        let (field, value, anchor) = fields.swap_remove(first);
        let name = match node.kind.as_str() {
            "observation" => node.registry_name.clone(),
            "representation" => None,
            _ => node.name.clone(),
        };
        matches.push(SearchMatch {
            kind: display_kind(node).to_owned(),
            id: node.id.clone(),
            name: name.filter(|name| name != &node.id),
            field: field.to_owned(),
            value,
            anchor,
        });
    }
    matches.sort_by(|left, right| {
        (kind_rank(&left.kind), &left.id).cmp(&(kind_rank(&right.kind), &right.id))
    });
    let total = matches.len();
    matches.truncate(limit);
    SearchAnswer {
        text: text.to_owned(),
        total,
        matches,
    }
}

impl Answer for SearchAnswer {
    fn text(&self) -> String {
        let mut out = String::new();
        line(
            &mut out,
            format!(
                "search {:?}: {} match(es){}; every word must occur in an id, name, type, file, or site symbol.",
                self.text,
                self.total,
                if self.total > self.matches.len() {
                    format!(", first {} shown (raise --limit)", self.matches.len())
                } else {
                    String::new()
                }
            ),
        );
        if self.matches.is_empty() {
            line(
                &mut out,
                "try fewer or shorter words, a file name, or a symbol".to_owned(),
            );
        }
        for found in &self.matches {
            let matched = if matches!(found.field.as_str(), "id" | "name" | "site" | "file") {
                String::new()
            } else {
                format!("  {}: {}", found.field, found.value)
            };
            line(
                &mut out,
                format!(
                    "{} {}{}{}  {}",
                    found.kind,
                    found.id,
                    found
                        .name
                        .as_deref()
                        .map(|name| format!("  \"{name}\""))
                        .unwrap_or_default(),
                    matched,
                    anchor_text(&found.anchor)
                ),
            );
        }
        out
    }
}

// ---------------------------------------------------------------------------------------------
// shared helpers

struct Index<'a> {
    graph: &'a Graph,
    nodes: BTreeMap<&'a str, &'a Node>,
}

impl<'a> Index<'a> {
    fn new(graph: &'a Graph) -> Self {
        let mut nodes = BTreeMap::<&str, &Node>::new();
        for node in &graph.nodes {
            if node.kind == "algorithm" || !nodes.contains_key(node.id.as_str()) {
                nodes.insert(node.id.as_str(), node);
            }
        }
        Self { graph, nodes }
    }

    fn kind(&self, id: &str) -> String {
        self.nodes
            .get(id)
            .map_or_else(|| "unknown".to_owned(), |node| node.kind.clone())
    }

    fn anchor(&self, id: &str) -> Option<Anchor> {
        self.nodes.get(id).map(|node| node.anchor.clone())
    }

    /// Resolve an id, a dotted counter name, or a registry variant name with an optional
    /// `Algorithm::` or `Counter::` prefix.
    fn resolve(&self, query: &str, what: &str) -> Result<&'a Node, NotFound> {
        if let Some(node) = self.nodes.get(query) {
            return Ok(node);
        }
        let bare = query
            .strip_prefix("Algorithm::")
            .or_else(|| query.strip_prefix("Counter::"))
            .unwrap_or(query);
        if let Some(node) = self.nodes.get(bare) {
            return Ok(node);
        }
        if let Some(node) = self
            .graph
            .nodes
            .iter()
            .find(|node| node.registry_name.as_deref() == Some(bare))
        {
            return Ok(node);
        }
        let roles = self
            .graph
            .nodes
            .iter()
            .filter(|node| node.type_path.as_deref() == Some(bare))
            .map(|node| node.id.clone())
            .collect::<Vec<_>>();
        if !roles.is_empty() {
            return Err(NotFound {
                what: what.to_owned(),
                query: query.to_owned(),
                candidates: roles,
                hint: Some(
                    "a representation id is its type path followed by its [role]; the candidates are every role of this type"
                        .to_owned(),
                ),
            });
        }
        Err(NotFound {
            what: what.to_owned(),
            query: query.to_owned(),
            candidates: nearest(query, self.nodes.keys().copied()),
            hint: Some("find ids with `algo-graph query search <words>`".to_owned()),
        })
    }

    fn counters(&self, id: &str) -> Vec<CounterRef> {
        self.measurements(id)
            .filter(|node| node.table.as_deref() == Some(COUNTER_TABLE))
            .map(|node| CounterRef {
                variant: node.id.clone(),
                name: node
                    .registry_name
                    .clone()
                    .unwrap_or_else(|| node.id.clone()),
            })
            .collect()
    }

    fn tests(&self, id: &str) -> Vec<String> {
        self.measurements(id)
            .filter(|node| node.table.as_deref() != Some(COUNTER_TABLE))
            .map(|node| node.id.clone())
            .collect()
    }

    fn measurements<'b>(&'b self, id: &'b str) -> impl Iterator<Item = &'a Node> + 'b {
        self.graph
            .edges
            .iter()
            .filter(move |edge| edge.kind == "measured-by" && edge.from == id)
            .filter_map(|edge| self.nodes.get(edge.to.as_str()).copied())
            .filter(|node| node.kind == "observation")
    }

    fn incoming(&self, id: &str, kind: &str) -> Vec<String> {
        self.graph
            .edges
            .iter()
            .filter(|edge| edge.kind == kind && edge.to == id)
            .map(|edge| edge.from.clone())
            .collect()
    }

    /// `(representation, consumer)` for each representation `id` produces.
    fn feeds_from(&self, id: &str) -> Vec<(String, String)> {
        self.graph
            .edges
            .iter()
            .filter(|edge| edge.kind == "produces" && edge.from == id)
            .flat_map(|produced| {
                self.incoming(&produced.to, "consumes")
                    .into_iter()
                    .filter(|consumer| consumer != id)
                    .map(|consumer| (produced.to.clone(), consumer))
            })
            .collect()
    }

    /// `(representation, producer)` for each representation `id` consumes.
    fn feeds_into(&self, id: &str) -> Vec<(String, String)> {
        self.graph
            .edges
            .iter()
            .filter(|edge| edge.kind == "consumes" && edge.from == id)
            .flat_map(|consumed| {
                self.incoming(&consumed.to, "produces")
                    .into_iter()
                    .filter(|producer| producer != id)
                    .map(|producer| (consumed.to.clone(), producer))
            })
            .collect()
    }

    fn anchored_files(&self) -> BTreeSet<String> {
        self.graph
            .nodes
            .iter()
            .filter(|node| {
                matches!(
                    node.kind.as_str(),
                    "algorithm" | "contract" | "representation"
                )
            })
            .flat_map(node_anchors)
            .map(|anchor| anchor.file.clone())
            .collect()
    }
}

/// The node kind as a reader expects it: an observation is a `counter` or a `test`.
fn display_kind(node: &Node) -> &str {
    match (node.kind.as_str(), node.table.as_deref()) {
        ("observation", Some(COUNTER_TABLE)) => "counter",
        ("observation", _) => "test",
        (kind, _) => kind,
    }
}

fn node_anchors(node: &Node) -> impl Iterator<Item = &Anchor> {
    std::iter::once(&node.anchor).chain(&node.sites)
}

fn dedup(anchors: Vec<Anchor>) -> Vec<Anchor> {
    let mut seen = BTreeSet::new();
    anchors
        .into_iter()
        .filter(|anchor| seen.insert(anchor.clone()))
        .collect()
}

/// A site symbol matches a queried symbol when they are equal, when the query is its last
/// `::` segment (`run` finds `Matcher::run`), when the query is its type (`Matcher` finds
/// `Matcher::run` and `impl Matcher`), or when the site is the query's last segment.
fn symbol_matches(site: &str, query: &str) -> bool {
    let bare = |symbol: &'_ str| -> String {
        symbol
            .trim_start_matches("impl ")
            .trim_start_matches("struct ")
            .trim_start_matches("enum ")
            .trim_start_matches("fn ")
            .to_owned()
    };
    let (site, query) = (bare(site), bare(query));
    site == query
        || site.rsplit("::").next() == Some(query.as_str())
        || site.starts_with(&format!("{query}::"))
}

/// Make a path relative to `root`; an absolute path outside `root` (another checkout of the
/// same repository) maps to the graph file it ends with.
fn relative_path(root: &Path, raw: &str, files: &BTreeSet<String>) -> String {
    let normal = |path: &Path| {
        path.components()
            .filter_map(|component| match component {
                Component::Normal(part) => Some(part.to_string_lossy().into_owned()),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("/")
    };
    let path = Path::new(raw);
    if !path.is_absolute() {
        return normal(path);
    }
    let canonical_root = fs::canonicalize(root).unwrap_or_else(|_| root.to_owned());
    let canonical = fs::canonicalize(path).unwrap_or_else(|_| path.to_owned());
    if let Ok(relative) = canonical
        .strip_prefix(&canonical_root)
        .or_else(|_| path.strip_prefix(root))
    {
        return normal(relative);
    }
    let absolute = normal(path);
    files
        .iter()
        .filter(|file| absolute.ends_with(&format!("/{file}")))
        .max_by_key(|file| file.len())
        .cloned()
        .or_else(|| {
            files
                .iter()
                .flat_map(|file| {
                    Path::new(file)
                        .ancestors()
                        .map(|ancestor| ancestor.to_string_lossy().into_owned())
                        .collect::<Vec<_>>()
                })
                .filter(|directory| {
                    !directory.is_empty() && absolute.ends_with(&format!("/{directory}"))
                })
                .max_by_key(String::len)
        })
        .unwrap_or(absolute)
}

/// The three candidates nearest to `query`: those containing it first, then by edit distance.
fn nearest<'a>(query: &str, candidates: impl IntoIterator<Item = &'a str>) -> Vec<String> {
    let lowered = query.to_lowercase();
    let mut scored = candidates
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|candidate| {
            let candidate_lowered = candidate.to_lowercase();
            (
                !candidate_lowered.contains(&lowered),
                strsim::levenshtein(&lowered, &candidate_lowered),
                candidate,
            )
        })
        .collect::<Vec<_>>();
    scored.sort();
    scored
        .into_iter()
        .take(3)
        .map(|(_, _, candidate)| candidate.to_owned())
        .collect()
}

fn span_policy(node: &Node) -> String {
    node.span
        .clone()
        .unwrap_or_else(|| "absent (the card has no span key)".to_owned())
}

fn run_identity(join: &Join) -> RunIdentity {
    RunIdentity {
        workload: join.receipt.workload.clone(),
        claim: join.receipt.claim.clone(),
        krust_revision: join.receipt.krust_revision.clone(),
        timestamp: join.receipt.timestamp.clone(),
        receipt: join.receipt.directory.clone(),
        partial: join.receipt.timings_partial || join.receipt.counters_partial,
    }
}

fn run_text(run: &RunIdentity) -> String {
    format!(
        "run {}{} at krust {} ({}; receipt {}{})",
        run.workload,
        run.claim
            .as_deref()
            .map(|claim| format!(" claim {claim}"))
            .unwrap_or_default(),
        run.krust_revision
            .as_deref()
            .map(|revision| &revision[..revision.len().min(12)])
            .unwrap_or("unknown"),
        run.timestamp.as_deref().unwrap_or("no timestamp"),
        run.receipt,
        if run.partial {
            "; partial: a timings or counter schema differs from the current one"
        } else {
            ""
        }
    )
}

fn anchor_text(anchor: &Anchor) -> String {
    format!("{}::{}", anchor.file, anchor.symbol)
}

/// Sites grouped by file in order of first appearance, as `file::a, b; other::c`.
fn sites_text(sites: &[Anchor]) -> String {
    let mut files = Vec::<(&str, Vec<&str>)>::new();
    for site in sites {
        match files.iter_mut().find(|(file, _)| *file == site.file) {
            Some((_, symbols)) => symbols.push(&site.symbol),
            None => files.push((&site.file, vec![&site.symbol])),
        }
    }
    files
        .into_iter()
        .map(|(file, symbols)| format!("{file}::{}", symbols.join(", ")))
        .collect::<Vec<_>>()
        .join("; ")
}

fn counters_text(counters: &[CounterRef], no_counter: Option<&str>) -> String {
    if counters.is_empty() {
        return format!("none ({})", no_counter.unwrap_or("no reason recorded"));
    }
    counters
        .iter()
        .map(|counter| format!("{} ({})", counter.variant, counter.name))
        .collect::<Vec<_>>()
        .join(", ")
}

fn tests_text(tests: &[String]) -> String {
    if tests.is_empty() {
        "none declared on the card".to_owned()
    } else {
        tests.join(", ")
    }
}

fn list_or_none(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_owned()
    } else {
        values.join(", ")
    }
}

fn line(out: &mut String, text: String) {
    out.push_str(&text);
    out.push('\n');
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::{
        AlgorithmCounter, EdgeRun, NodeRun, Receipt, Summary, build_graph, workspace_root,
    };

    fn anchor(file: &str, symbol: &str) -> Anchor {
        Anchor {
            crate_name: "test".to_owned(),
            file: file.to_owned(),
            symbol: symbol.to_owned(),
        }
    }

    fn node(kind: &str, id: &str) -> Node {
        Node {
            kind: kind.to_owned(),
            id: id.to_owned(),
            provenance: "declared".to_owned(),
            anchor: anchor(&format!("src/{id}.rs"), id),
            area: id.split_once('.').map(|(area, _)| area.to_owned()),
            name: None,
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
            lean: Vec::new(),
        }
    }

    fn algorithm(id: &str, file: &str, sites: &[&str]) -> Node {
        let sites = sites
            .iter()
            .map(|site| anchor(file, site))
            .collect::<Vec<_>>();
        Node {
            anchor: sites[0].clone(),
            sites,
            name: Some(format!("{id} name")),
            ..node("algorithm", id)
        }
    }

    fn counter(variant: &str, name: &str) -> Node {
        Node {
            table: Some(COUNTER_TABLE.to_owned()),
            registry_name: Some(name.to_owned()),
            anchor: anchor("measure.rs", &format!("Counter::{variant}")),
            ..node("observation", variant)
        }
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

    /// `a` produces `R`, which `b` consumes; `b` constrains `c`; `d` falls back to `a`; `e` is a
    /// variant of `a`; `a` falls back to `f`. Phases `early -> p1 -> p2` and `other -> px`:
    /// `p1` contains `a`, `p2` and `other` contain `g`, `px` contains `k`, `early` contains `h`.
    fn synthetic() -> Graph {
        let mut constrains = edge("constrains", "t.b", "t.c", "declared");
        constrains.detail = Some("an ordering".to_owned());
        constrains.consumer_site = Some(anchor("src/c.rs", "use_order"));
        let mut graph = Graph {
            nodes: vec![
                Node {
                    span: Some("per problem".to_owned()),
                    ..algorithm(
                        "t.a",
                        "src/a.rs",
                        &["run_a", "Matcher::run", "impl Matcher"],
                    )
                },
                algorithm("t.b", "src/b.rs", &["run_b"]),
                algorithm("t.c", "src/c.rs", &["run_c", "use_order"]),
                algorithm("t.d", "src/d.rs", &["run_d"]),
                algorithm("t.e", "src/e.rs", &["run_e"]),
                algorithm("t.f", "src/f.rs", &["run_f"]),
                algorithm("t.g", "src/g.rs", &["run_g"]),
                algorithm("t.h", "src/h.rs", &["run_h"]),
                algorithm("t.k", "src/k.rs", &["run_k"]),
                Node {
                    type_path: Some("crate::R".to_owned()),
                    anchor: anchor("src/r.rs", "R"),
                    ..node("representation", "crate::R [role]")
                },
                counter("CounterA", "t.counter_a"),
                Node {
                    table: None,
                    anchor: anchor("tests/a.rs", "tests/a.rs"),
                    ..node("observation", "tests/a.rs")
                },
                node("phase", "early"),
                node("phase", "p1"),
                node("phase", "p2"),
                node("phase", "other"),
                node("phase", "px"),
            ],
            edges: vec![
                edge("produces", "t.a", "crate::R [role]", "declared"),
                edge("consumes", "t.b", "crate::R [role]", "declared"),
                constrains,
                edge("falls-back-to", "t.d", "t.a", "declared"),
                edge("variant-of", "t.e", "t.a", "declared"),
                edge("falls-back-to", "t.a", "t.f", "declared"),
                edge("measured-by", "t.a", "CounterA", "declared"),
                edge("measured-by", "t.a", "tests/a.rs", "declared"),
                edge("follows", "early", "p1", "table"),
                edge("follows", "p1", "p2", "table"),
                edge("follows", "other", "px", "table"),
                edge("contains", "p1", "t.a", "derived"),
                edge("contains", "p2", "t.g", "derived"),
                edge("contains", "other", "t.g", "derived"),
                edge("contains", "px", "t.k", "derived"),
                edge("contains", "early", "t.h", "derived"),
            ],
        };
        graph.sort();
        graph
    }

    fn reached<'a>(answer: &'a ImpactAnswer, id: &str) -> Option<&'a Reached> {
        answer.reached.iter().find(|reached| reached.id == id)
    }

    fn steps_of(reached: &Reached) -> Vec<(&str, &str, &str)> {
        reached
            .path
            .iter()
            .map(|hop| (hop.from.as_str(), hop.step.as_str(), hop.to.as_str()))
            .collect()
    }

    #[test]
    fn impact_follows_dependencies_in_their_direction_with_paths() {
        let answer = impact(&synthetic(), "t.a").unwrap();
        let b = reached(&answer, "t.b").unwrap();
        assert_eq!(b.class, "declared");
        assert_eq!(
            steps_of(b),
            [
                ("t.a", "produces", "crate::R [role]"),
                ("crate::R [role]", "consumed-by", "t.b")
            ]
        );
        let c = reached(&answer, "t.c").unwrap();
        assert_eq!(steps_of(c).last(), Some(&("t.b", "constrains", "t.c")));
        assert_eq!(
            c.path.last().unwrap().consumer_site,
            Some(anchor("src/c.rs", "use_order"))
        );
        assert_eq!(
            steps_of(reached(&answer, "t.d").unwrap()),
            [("t.a", "is-fallback-of", "t.d")]
        );
        assert_eq!(
            steps_of(reached(&answer, "t.e").unwrap()),
            [("t.a", "has-variant", "t.e")]
        );
        // The origin's own fallback is reported as not followed, never reached.
        assert!(reached(&answer, "t.f").is_none());
        assert_eq!(answer.not_followed.len(), 1);
        assert_eq!(answer.not_followed[0].other, "t.f");
        // Counters and tests are listed, never traversed.
        assert!(
            answer
                .reached
                .iter()
                .all(|reached| reached.kind != "observation")
        );
        assert_eq!(answer.counters.len(), 1);
        assert_eq!(answer.counters[0].name, "t.counter_a");
        assert_eq!(answer.tests[0].path, "tests/a.rs");
    }

    #[test]
    fn impact_stage_order_reaches_later_phases_only() {
        let answer = impact(&synthetic(), "t.a").unwrap();
        let g = reached(&answer, "t.g").unwrap();
        assert_eq!(g.class, "stage-order");
        assert_eq!(
            steps_of(g),
            [
                ("t.a", "runs-in", "p1"),
                ("p1", "precedes", "p2"),
                ("p2", "contains", "t.g")
            ]
        );
        // `early` runs before `p1`, and `px` follows `other`, a phase `g` also runs in but
        // which the change does not reach.
        assert!(reached(&answer, "t.h").is_none());
        assert!(reached(&answer, "t.k").is_none());
        let text = answer.text();
        assert!(text.contains("an absent relation proves nothing"), "{text}");
        assert!(
            text.contains(
                "  t.g  src/g.rs::run_g\n    from t.a -runs-in-> p1 -precedes-> p2 -contains->\n"
            ),
            "{text}"
        );
    }

    #[test]
    fn impact_from_a_phase_reaches_its_algorithms_as_declared() {
        let answer = impact(&synthetic(), "p1").unwrap();
        assert_eq!(reached(&answer, "t.a").unwrap().class, "declared");
        assert_eq!(reached(&answer, "t.b").unwrap().class, "declared");
        assert_eq!(reached(&answer, "t.g").unwrap().class, "stage-order");
    }

    #[test]
    fn impact_rejects_counters_and_unknown_ids() {
        let error = impact(&synthetic(), "t.counter_a").unwrap_err();
        assert_eq!(error.candidates, ["t.a"]);
        let error = impact(&synthetic(), "t.zz").unwrap_err();
        assert_eq!(error.what, "id");
        assert_eq!(error.candidates.len(), 3);
    }

    #[test]
    fn unknown_ids_name_the_three_nearest() {
        let error = show(&synthetic(), "t.bb").unwrap_err();
        assert_eq!(error.candidates.len(), 3);
        assert_eq!(error.candidates[0], "t.b");
        let rendered = error.to_string();
        assert!(
            rendered.starts_with("unknown id `t.bb`; nearest: t.b, "),
            "{rendered}"
        );
        assert_eq!(
            nearest(
                "match",
                ["backend.matching.syntactic", "x", "mat", "zzzzzz"]
            ),
            ["backend.matching.syntactic", "mat", "x"]
        );
    }

    #[test]
    fn show_resolves_registry_names_and_lists_relations() {
        let graph = synthetic();
        assert_eq!(show(&graph, "t.counter_a").unwrap().node.id, "CounterA");
        assert_eq!(
            show(&graph, "Counter::CounterA").unwrap().node.id,
            "CounterA"
        );
        let answer = show(&graph, "t.a").unwrap();
        assert!(answer.relations.iter().any(|relation| {
            relation.kind == "feeds" && relation.direction == "out" && relation.other == "t.b"
        }));
        assert!(answer.relations.iter().any(|relation| {
            relation.kind == "falls-back-to"
                && relation.direction == "in"
                && relation.other == "t.d"
        }));
        assert!(
            answer
                .relations
                .iter()
                .all(|relation| relation.kind != "measured-by")
        );
        assert_eq!(answer.tests, ["tests/a.rs"]);
        let error = show(&graph, "crate::R").unwrap_err();
        assert_eq!(error.candidates, ["crate::R [role]"]);
    }

    #[test]
    fn owner_matches_paths_symbols_and_directories() {
        let graph = synthetic();
        let root = Path::new("/nonexistent-root");
        let answer = owner(&graph, root, "src/a.rs").unwrap();
        assert_eq!(answer.owners.len(), 1);
        assert_eq!(answer.owners[0].id, "t.a");
        assert!(answer.owners[0].primary_card_here);
        assert_eq!(answer.owners[0].counters[0].name, "t.counter_a");
        assert_eq!(answer.owners[0].tests, ["tests/a.rs"]);
        assert_eq!(answer.owners[0].span, "per problem");

        for symbol in ["run", "Matcher::run", "Matcher"] {
            let answer = owner(&graph, root, &format!("./src/a.rs::{symbol}")).unwrap();
            assert!(answer.symbol_is_site, "{symbol}");
            assert_eq!(answer.owners[0].id, "t.a");
            assert!(
                answer.owners[0]
                    .matched
                    .iter()
                    .all(|site| site.symbol.contains("Matcher")),
                "{symbol}"
            );
        }
        // A site of `t.c`, whose card is elsewhere, in the queried file.
        let answer = owner(&graph, root, "src/c.rs::use_order").unwrap();
        assert_eq!(answer.owners[0].matched, [anchor("src/c.rs", "use_order")]);

        let answer = owner(&graph, root, "src/a.rs::helper").unwrap();
        assert!(!answer.symbol_is_site);
        assert_eq!(answer.owners[0].id, "t.a");
        assert!(answer.text().contains("no card names `helper` as a site"));

        let answer = owner(&graph, root, "src").unwrap();
        assert_eq!(answer.owners.len(), 9);
        assert_eq!(answer.representations.len(), 1);

        let answer = owner(&graph, root, "run_g").unwrap();
        assert_eq!(answer.owners[0].id, "t.g");

        let error = owner(&graph, root, "src/aa.rs").unwrap_err();
        assert_eq!(error.what, "path");
        assert_eq!(error.candidates.len(), 3);
        assert!(error.candidates.contains(&"src/a.rs".to_owned()));
        assert_eq!(
            owner(&graph, root, "no_such_site").unwrap_err().what,
            "site symbol"
        );
    }

    #[test]
    fn absolute_paths_map_into_the_graph() {
        let files = BTreeSet::from(["src/a.rs".to_owned(), "src/deep/b.rs".to_owned()]);
        let root = Path::new("/nonexistent-root");
        assert_eq!(
            relative_path(root, "/nonexistent-root/src/a.rs", &files),
            "src/a.rs"
        );
        assert_eq!(
            relative_path(root, "/other/checkout/src/a.rs", &files),
            "src/a.rs"
        );
        assert_eq!(
            relative_path(root, "/other/checkout/src/deep", &files),
            "src/deep"
        );
        assert_eq!(relative_path(root, "./src//a.rs", &files), "src/a.rs");
    }

    fn join(algorithms: Vec<AlgorithmRun>, nodes: Vec<NodeRun>, edges: Vec<EdgeRun>) -> Join {
        Join {
            schema_version: crate::JOIN_SCHEMA_VERSION,
            aggregation_rule: crate::AGGREGATION_RULE.to_owned(),
            verdict_rule: crate::VERDICT_RULE.to_owned(),
            receipt: Receipt {
                directory: "evidence/w/c".to_owned(),
                workload: "w".to_owned(),
                claim: Some("claim".to_owned()),
                timestamp: None,
                krust_revision: Some("0123456789abcdef".to_owned()),
                binary_sha256: None,
                metadata_schema: "1".to_owned(),
                timings_schema: "1".to_owned(),
                current_timings_schema: 1,
                timings_partial: false,
                counter_schema: "9".to_owned(),
                current_counter_schema: 9,
                counters_partial: false,
                trace_schema: "chrome-trace-event-B/E".to_owned(),
                tools: Vec::new(),
                revisions: Vec::new(),
                coverage: None,
            },
            summary: Summary {
                largest_self_time_algorithm: None,
                largest_self_seconds: 0.0,
                declared_algorithms: algorithms.len(),
                ran_algorithms: 0,
                not_run_algorithms: 0,
                unknown_algorithms: 0,
                not_run_backend_algorithms: Vec::new(),
                unknown_backend_algorithms: Vec::new(),
                span_bypasses: Vec::new(),
            },
            algorithms,
            phases: Vec::new(),
            observed_nests: Vec::new(),
            observed_contains: Vec::new(),
            receipt_counters: Vec::new(),
            nodes,
            edges,
        }
    }

    fn run(id: &str, count: u64, self_seconds: f64, total_seconds: f64) -> AlgorithmRun {
        AlgorithmRun {
            id: id.to_owned(),
            declared: true,
            area: id.split_once('.').map(|(area, _)| area.to_owned()),
            span_policy: None,
            count,
            total_seconds,
            self_seconds,
            cost: Vec::new(),
            counters: Vec::new(),
        }
    }

    fn observed(name: &str, declared: bool, own: u64, total: u64) -> AlgorithmCounter {
        AlgorithmCounter {
            name: name.to_owned(),
            observation: None,
            declared,
            trace_total: Some(total),
            trace_self: Some(own),
            receipt_total: Some(total),
        }
    }

    fn node_run(id: &str, verdict: Verdict, evidence: &str) -> NodeRun {
        NodeRun {
            kind: "algorithm".to_owned(),
            id: id.to_owned(),
            verdict,
            evidence: evidence.to_owned(),
            reason: format!("{evidence} reason"),
        }
    }

    #[test]
    fn hot_orders_timed_algorithms_and_splits_counters() {
        let mut a = run("t.a", 5, 0.2, 0.9);
        a.counters = vec![
            observed("t.counter_a", true, 7, 7),
            observed("t.declared_idle", true, 0, 0),
            observed("t.own", false, 3, 3),
            observed("t.nested", false, 0, 4),
        ];
        let joined = join(
            vec![
                a,
                run("t.b", 50, 0.3, 0.3),
                run("t.c", 1, 0.3, 0.4),
                run("t.d", 0, 0.0, 0.0),
                run("zz.unknown", 2, 0.01, 0.01),
            ],
            vec![
                node_run("t.e", Verdict::Unknown, "counter-moved"),
                node_run("t.d", Verdict::Ran, "coverage"),
                node_run("t.b", Verdict::Ran, "coverage"),
            ],
            Vec::new(),
        );
        let graph = synthetic();
        let ids = |answer: &HotAnswer| {
            answer
                .rows
                .iter()
                .map(|row| row.id.clone())
                .collect::<Vec<_>>()
        };
        let by_self = hot(&graph, &joined, HotOrder::SelfSeconds, 10);
        assert_eq!(ids(&by_self), ["t.b", "t.c", "t.a", "zz.unknown"]);
        assert_eq!(by_self.timed_algorithms, 4);
        assert_eq!(
            ids(&hot(&graph, &joined, HotOrder::Total, 2)),
            ["t.a", "t.c"]
        );
        assert_eq!(ids(&hot(&graph, &joined, HotOrder::Count, 1)), ["t.b"]);
        let row = &by_self.rows[2];
        assert_eq!(row.anchor, Some(anchor("src/a.rs", "run_a")));
        assert_eq!(row.declared_counters.len(), 1);
        assert_eq!(row.undeclared_self_counters[0].name, "t.own");
        assert_eq!(row.nested_only_counters, ["t.nested"]);
        assert!(!by_self.rows[3].in_graph);
        assert_eq!(by_self.counter_only, ["t.e"]);
        // `t.b` ran by coverage and opened its span, so only `t.d` is untimed.
        assert_eq!(by_self.coverage_untimed, ["t.d"]);
        let text = by_self.text();
        assert!(
            text.contains("ran by coverage without opening a span, so untimed: t.d"),
            "{text}"
        );
        assert!(text.starts_with("hot by self: top 4 of 4 timed algorithms in run w claim claim at krust 0123456789ab"), "{text}");
        assert!(text.contains("3. t.a  self 0.2000s"), "{text}");
    }

    #[test]
    fn unexercised_lists_the_join_verdicts_and_filters_by_area() {
        let edge_run = |kind: &str, from: &str, to: &str, verdict: Verdict| EdgeRun {
            kind: kind.to_owned(),
            from: from.to_owned(),
            to: to.to_owned(),
            provenance: "declared".to_owned(),
            detail: None,
            order: None,
            verdict,
            evidence: match verdict {
                Verdict::Ran => "observed",
                Verdict::NotRun => "endpoint-not-run",
                Verdict::Unknown => "unobserved",
            }
            .to_owned(),
        };
        let mut spanned = run("t.a", 0, 0.0, 0.0);
        spanned.span_policy = Some("per call".to_owned());
        let mut counted = run("t.b", 0, 0.0, 0.0);
        counted.counters = vec![observed("t.counter_b", true, 0, 0)];
        let joined = join(
            vec![
                spanned,
                counted,
                run("t.c", 0, 0.0, 0.0),
                run("t.d", 3, 0.1, 0.1),
                run("u.x", 0, 0.0, 0.0),
            ],
            vec![
                node_run("t.a", Verdict::Unknown, "zero-span"),
                node_run("t.b", Verdict::NotRun, "synthetic"),
                node_run("t.c", Verdict::Unknown, "unobservable"),
                node_run("t.d", Verdict::Ran, "span"),
                node_run("u.x", Verdict::Unknown, "unobservable"),
            ],
            vec![
                edge_run("constrains", "t.b", "t.c", Verdict::Unknown),
                edge_run("constrains", "t.c", "t.b", Verdict::NotRun),
                edge_run("constrains", "u.x", "u.y", Verdict::Unknown),
                edge_run("produces", "t.a", "crate::R [role]", Verdict::Ran),
            ],
        );
        let answer = unexercised(&synthetic(), &joined, Some("t"), true).unwrap();
        let ids = |algorithms: &[UnexercisedAlgorithm]| {
            algorithms
                .iter()
                .map(|algorithm| (algorithm.id.clone(), algorithm.evidence.clone()))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            ids(&answer.not_run),
            [("t.b".to_owned(), "synthetic".to_owned())]
        );
        assert_eq!(
            ids(&answer.unknown),
            [
                ("t.a".to_owned(), "zero-span".to_owned()),
                ("t.c".to_owned(), "unobservable".to_owned())
            ]
        );
        assert_eq!(answer.not_run[0].declared_counters, ["t.counter_b"]);
        assert_eq!(answer.declared_algorithms, 4);
        assert_eq!(answer.rule, crate::VERDICT_RULE);
        assert_eq!(answer.edges.len(), 2);
        assert_eq!(answer.edges[0].verdict, Verdict::Unknown);
        assert_eq!(answer.edges[1].verdict, Verdict::NotRun);
        assert_eq!(answer.edge_totals.get("constrains"), Some(&2));
        let text = answer.text();
        assert!(
            text.contains("3 of 4 declared algorithms (1 not-run, 2 unknown)"),
            "{text}"
        );
        assert!(
            text.contains(&format!("rule: {}", crate::VERDICT_RULE)),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "edges constrains: {}",
                edge_verdict_rule("constrains")
            )),
            "{text}"
        );
        assert!(
            unexercised(&synthetic(), &joined, None, false)
                .unwrap()
                .edges
                .is_empty()
        );
        let error = unexercised(&synthetic(), &joined, Some("tt"), true).unwrap_err();
        assert_eq!(error.what, "area");
        assert_eq!(error.candidates, ["t", "u"]);
    }

    #[test]
    fn search_requires_every_word() {
        let graph = synthetic();
        let answer = search(&graph, "matcher A.RS", 10);
        assert_eq!(answer.total, 1);
        assert_eq!(answer.matches[0].id, "t.a");
        assert_eq!(answer.matches[0].field, "site");
        let answer = search(&graph, "t.", 2);
        assert_eq!(answer.total, 10);
        assert_eq!(answer.matches.len(), 2);
        assert_eq!(answer.matches[0].kind, "algorithm");
        assert!(answer.text().contains("first 2 shown"));
        assert_eq!(search(&graph, "counter_a", 10).matches[0].kind, "counter");
    }

    /// Every subcommand answers against the workspace graph and renders as text and TOML.
    #[test]
    fn smoke_every_subcommand_on_the_workspace_graph() {
        let root = workspace_root();
        let graph = build_graph(&root).unwrap().graph;
        let check = |answer: &dyn Fn() -> (String, String)| {
            let (text, toml) = answer();
            assert!(!text.is_empty());
            assert!(!text.contains('\x1b'));
            toml::from_str::<toml::Table>(&toml).unwrap();
            text
        };
        let text = check(&|| {
            let answer = owner(&graph, &root, "crates/k-rust-backend/src/matching/mod.rs").unwrap();
            (answer.text(), answer.toml().unwrap())
        });
        assert!(text.contains("backend.matching.syntactic"), "{text}");
        assert!(
            text.contains("MatchingProblems (matching.problems)"),
            "{text}"
        );
        let text = check(&|| {
            let answer = show(&graph, "backend.matching.syntactic").unwrap();
            (answer.text(), answer.toml().unwrap())
        });
        assert!(text.contains("cost [one matching problem]"), "{text}");
        let text = check(&|| {
            let answer = impact(&graph, "kompile.sentences.number").unwrap();
            (answer.text(), answer.toml().unwrap())
        });
        assert!(
            text.contains("  backend.definition.internalize  ")
                && text.contains("    from kompile.sentences.number -constrains->"),
            "{text}"
        );
        let text = check(&|| {
            let answer = search(&graph, "sort projection", 40);
            (answer.text(), answer.toml().unwrap())
        });
        assert!(text.contains("kompile.sort_helpers.generate"), "{text}");

        let algorithms = graph
            .nodes
            .iter()
            .filter(|node| node.kind == "algorithm")
            .map(|node| {
                let count = u64::from(node.id == "backend.matching.syntactic");
                AlgorithmRun {
                    span_policy: node.span.clone(),
                    ..run(&node.id, count, 0.5 * count as f64, count as f64)
                }
            })
            .collect::<Vec<_>>();
        let nodes = algorithms
            .iter()
            .map(|algorithm| {
                if algorithm.count > 0 {
                    node_run(&algorithm.id, Verdict::Ran, "span")
                } else {
                    node_run(&algorithm.id, Verdict::Unknown, "zero-span")
                }
            })
            .collect();
        let joined = join(algorithms, nodes, Vec::new());
        let text = check(&|| {
            let answer = hot(&graph, &joined, HotOrder::SelfSeconds, 10);
            (answer.text(), answer.toml().unwrap())
        });
        assert!(
            text.contains("1. backend.matching.syntactic  self 0.5000s"),
            "{text}"
        );
        let text = check(&|| {
            let answer = unexercised(&graph, &joined, Some("backend"), true).unwrap();
            (answer.text(), answer.toml().unwrap())
        });
        assert!(text.contains("backend.rewrite.step"), "{text}");
        assert!(!text.contains("backend.matching.syntactic "), "{text}");
    }
}
