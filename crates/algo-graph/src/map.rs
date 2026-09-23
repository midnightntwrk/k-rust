//! The generated algorithm map: the whole graph as one Markdown document for work that spans
//! algorithms.
//!
//! The map states only what the graph declares or derives from declarations: phase order and
//! `contains` from the stage tables, `produces` and `consumes` from cards, and the `feeds`
//! relation between a producer and a consumer of one representation. The static graph has no
//! call graph and no `nests` edge (nesting is observed only in runs), so an algorithm that no
//! phase contains and no representation connects has no position in any pipeline.

use std::collections::{BTreeMap, BTreeSet};

use crate::{Graph, Node};

/// Workspace-relative path of the checked-in map.
pub const MAP_PATH: &str = "docs/algorithm-map.md";

/// The command that regenerates [`MAP_PATH`].
pub const MAP_COMMAND: &str = "cargo run -p algo-graph -- map";

/// An entry command, identified by the representations its run returns.
///
/// The graph has no command nodes; this table is the renderer's one assumption, and the map
/// prints it.
#[derive(Clone, Copy, Debug)]
pub struct Command {
    /// The command name, such as `kprove`.
    pub name: &'static str,
    /// Representation type paths the command's run returns.
    pub roots: &'static [&'static str],
    /// Whether the stage tables' phases belong to this command.
    pub phases: bool,
}

/// The workspace's entry commands, in the order the map renders them.
pub const COMMANDS: &[Command] = &[
    Command {
        name: "kompile",
        roots: &[
            "k_rust_kore::kore::ast::Definition",
            "k_rust::PreparedDefinitionManifest",
        ],
        phases: true,
    },
    Command {
        name: "kprove",
        roots: &["k_rust_backend::proof::ProofResult"],
        phases: false,
    },
    Command {
        name: "krun",
        roots: &["k_rust_backend::rewrite::ExecutionResult"],
        phases: false,
    },
];

/// A bound longer than this many characters is cut.
const BOUND_WIDTH: usize = 50;

/// The number of claiming cards or constrained consumers at which the `many declarers` rule fires.
const MANY_DECLARERS: usize = 3;

/// Render the map of `graph` for the workspace commands: kompile, kprove, and krun.
pub fn render_map(graph: &Graph) -> String {
    render_map_with(graph, COMMANDS)
}

/// Render the map of `graph` for the given commands.
pub fn render_map_with(graph: &Graph, commands: &[Command]) -> String {
    let index = Index::new(graph);
    let mut output = String::new();
    header(&mut output, graph, commands);
    pipelines(&mut output, &index, commands);
    representations(&mut output, &index);
    contracts(&mut output, &index);
    fallbacks(&mut output, &index);
    entry_sites(&mut output, &index);
    leads_section(&mut output, &index);
    output
}

struct Index<'g> {
    graph: &'g Graph,
    nodes: BTreeMap<&'g str, &'g Node>,
    algorithms: Vec<&'g Node>,
    representations: Vec<&'g Node>,
    producers: BTreeMap<&'g str, BTreeSet<&'g str>>,
    consumers: BTreeMap<&'g str, BTreeSet<&'g str>>,
    consumes: BTreeMap<&'g str, BTreeSet<&'g str>>,
    produces: BTreeMap<&'g str, BTreeSet<&'g str>>,
    labels: BTreeMap<&'g str, String>,
}

impl<'g> Index<'g> {
    fn new(graph: &'g Graph) -> Self {
        let mut nodes = BTreeMap::new();
        for node in &graph.nodes {
            nodes.entry(node.id.as_str()).or_insert(node);
        }
        let mut algorithms = graph
            .nodes
            .iter()
            .filter(|node| node.kind == "algorithm")
            .collect::<Vec<_>>();
        algorithms.sort_by(|left, right| left.id.cmp(&right.id));
        let mut representations = graph
            .nodes
            .iter()
            .filter(|node| node.kind == "representation")
            .collect::<Vec<_>>();
        representations.sort_by(|left, right| left.id.cmp(&right.id));
        let mut producers = BTreeMap::<&str, BTreeSet<&str>>::new();
        let mut consumers = BTreeMap::<&str, BTreeSet<&str>>::new();
        let mut consumes = BTreeMap::<&str, BTreeSet<&str>>::new();
        let mut produces = BTreeMap::<&str, BTreeSet<&str>>::new();
        for edge in &graph.edges {
            match edge.kind.as_str() {
                "produces" => {
                    producers.entry(&edge.to).or_default().insert(&edge.from);
                    produces.entry(&edge.from).or_default().insert(&edge.to);
                }
                "consumes" => {
                    consumers.entry(&edge.to).or_default().insert(&edge.from);
                    consumes.entry(&edge.from).or_default().insert(&edge.to);
                }
                _ => {}
            }
        }
        let labels = representation_labels(&representations);
        Self {
            graph,
            nodes,
            algorithms,
            representations,
            producers,
            consumers,
            consumes,
            produces,
            labels,
        }
    }

    fn edges(&self, kind: &str) -> impl Iterator<Item = &'g crate::Edge> + use<'g, '_> {
        let kind = kind.to_owned();
        self.graph
            .edges
            .iter()
            .filter(move |edge| edge.kind == kind)
    }

    fn label(&self, representation: &str) -> String {
        self.labels
            .get(representation)
            .cloned()
            .unwrap_or_else(|| format!("[{representation}]"))
    }

    fn labels_of(&self, representations: Option<&BTreeSet<&str>>) -> String {
        representations
            .map(|set| {
                set.iter()
                    .map(|representation| self.label(representation))
                    .collect::<Vec<_>>()
                    .join(", ")
            })
            .filter(|text| !text.is_empty())
            .unwrap_or_else(|| "–".to_owned())
    }

    /// The algorithms a producer feeds: consumers of a representation it produces, itself excluded.
    fn feeds(&self, producer: &str) -> BTreeSet<&'g str> {
        self.produces
            .get(producer)
            .into_iter()
            .flatten()
            .flat_map(|representation| self.consumers.get(representation).into_iter().flatten())
            .copied()
            .filter(|consumer| *consumer != producer)
            .collect()
    }

    fn algorithm_line(&self, node: &Node) -> String {
        let mut line = node.id.clone();
        if !node.cost.is_empty() {
            line.push_str(" — ");
            line.push_str(&bounds(node));
        }
        let ins = self.consumes.get(node.id.as_str());
        let outs = self.produces.get(node.id.as_str());
        let sides = [("in", ins), ("out", outs)]
            .into_iter()
            .filter(|(_, side)| side.is_some_and(|set| !set.is_empty()))
            .map(|(name, side)| format!("{name}: {}", self.labels_of(side)))
            .collect::<Vec<_>>();
        if !sides.is_empty() {
            line.push_str(" — ");
            line.push_str(&sides.join(" → "));
        }
        line
    }
}

/// The first cost mode's bound, cut at [`BOUND_WIDTH`] characters on a word boundary, then the
/// number of modes left out.
fn bounds(node: &Node) -> String {
    let Some(first) = node.cost.first() else {
        return String::new();
    };
    let mut text = if first.bound.chars().count() <= BOUND_WIDTH {
        first.bound.clone()
    } else {
        let cut = first
            .bound
            .char_indices()
            .take_while(|(position, _)| first.bound[..*position].chars().count() < BOUND_WIDTH)
            .filter(|(_, character)| *character == ' ')
            .map(|(position, _)| position)
            .last()
            .unwrap_or(first.bound.len());
        format!("{}…", first.bound[..cut].trim_end_matches([',', ';']))
    };
    let omitted = node.cost.len() - 1;
    if omitted > 0 {
        text.push_str(&format!(
            " +{omitted} mode{}",
            if omitted == 1 { "" } else { "s" }
        ));
    }
    text
}

/// Short representation labels: the role when it is unique, else the simple type name and the
/// role, else the full id.
fn representation_labels<'g>(representations: &[&'g Node]) -> BTreeMap<&'g str, String> {
    let candidates = |node: &Node| {
        let simple = node
            .type_path
            .as_deref()
            .map(|path| simple_type_name(path).to_owned())
            .unwrap_or_else(|| node.id.clone());
        let mut candidates = Vec::new();
        if let Some(role) = &node.role {
            candidates.push(format!("[{role}]"));
            candidates.push(format!("[{simple}: {role}]"));
        } else {
            candidates.push(format!("[{simple}]"));
        }
        candidates.push(format!("[{}]", node.id));
        candidates
    };
    let mut counts = BTreeMap::<String, usize>::new();
    for node in representations {
        for candidate in candidates(node) {
            *counts.entry(candidate).or_default() += 1;
        }
    }
    representations
        .iter()
        .map(|node| {
            let all = candidates(node);
            let label = all
                .iter()
                .find(|candidate| counts[*candidate] == 1)
                .unwrap_or_else(|| all.last().expect("the id candidate is always present"))
                .clone();
            (node.id.as_str(), label)
        })
        .collect()
}

/// The type path without generic arguments, as `k_rust::definition::PartialOrder` for
/// `k_rust::definition::PartialOrder<String>`.
fn plain_type(type_path: &str) -> &str {
    type_path
        .split_once('<')
        .map_or(type_path, |(head, _)| head)
        .trim()
}

fn simple_type_name(type_path: &str) -> &str {
    let plain = plain_type(type_path);
    plain.rsplit("::").next().unwrap_or(plain)
}

/// `crates/<crate>/src/<rest>` becomes `<crate without its k-rust- prefix>/<rest>`.
fn short_path(file: &str) -> String {
    let Some(rest) = file.strip_prefix("crates/") else {
        return file.to_owned();
    };
    let Some((crate_name, rest)) = rest.split_once("/src/") else {
        return file.to_owned();
    };
    let short = crate_name.strip_prefix("k-rust-").unwrap_or(crate_name);
    format!("{short}/{rest}")
}

/// `k_rust_<crate>::` becomes `<crate>::`.
fn short_type(type_path: &str) -> String {
    type_path
        .strip_prefix("k_rust_")
        .filter(|rest| rest.contains("::"))
        .map_or_else(|| type_path.to_owned(), ToOwned::to_owned)
}

fn header(output: &mut String, graph: &Graph, commands: &[Command]) {
    let count = |items: Vec<&str>| {
        let mut counts = BTreeMap::<&str, usize>::new();
        for item in items {
            *counts.entry(item).or_default() += 1;
        }
        counts
            .into_iter()
            .map(|(kind, count)| format!("{count} {kind}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let nodes = count(graph.nodes.iter().map(|node| node.kind.as_str()).collect());
    let edges = count(graph.edges.iter().map(|edge| edge.kind.as_str()).collect());
    output.push_str("# Algorithm map\n\n");
    output.push_str(&format!(
        "Generated by `{MAP_COMMAND}`; `crates/algo-graph/tests/freshness.rs` fails when this file is stale.\n"
    ));
    output.push_str("It is the starting point for work that spans algorithms.\n");
    output.push_str("It holds only what the algorithm graph declares on cards (`docs/algorithm-cards.md`), reads from tables (the kompile stage tables, `Counter::ALL`), or derives from both.\n");
    output.push_str("An absent edge proves nothing: there is no call graph, and code that no card names belongs to no algorithm.\n");
    output.push_str(&format!("Graph: nodes {nodes}; edges {edges}.\n\n"));
    output.push_str("- `algo-graph query show <id>` prints a whole card (every cost mode, variables, counters, tests); `query impact <id>` prints what a change reaches.\n");
    output.push_str("- `algo-graph atlas` writes the cost atlas: measured self-time shares, Amdahl ceilings, and growth exponents per workload. This map has no measured cost.\n");
    output.push_str("- An algorithm line is `id — bound — in: consumed → out: produced`, without a side the card does not declare; `query show` prints the card's name.\n");
    output.push_str(&format!("- A bound is the card's first cost mode, cut at {BOUND_WIDTH} characters with `…`; `+n modes` counts the modes left out.\n"));
    output.push_str("- `[role]` names a representation (`[Type: role]` when types share a role). Paths write `crates/<crate>/src/` as `<crate>/` and types `k_rust_<crate>::` as `<crate>::`, both without the `k-rust-` prefix.\n\n");
    output.push_str("The graph has no command nodes.\n");
    output.push_str("This map roots each command at the representations its run returns: ");
    output.push_str(
        &commands
            .iter()
            .map(|command| {
                format!(
                    "{} → {}",
                    command.name,
                    command
                        .roots
                        .iter()
                        .map(|root| format!("`{}`", short_type(root)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect::<Vec<_>>()
            .join("; "),
    );
    output.push_str(".\n\n");
}

/// Where an algorithm's full line was printed.
struct Placement {
    command: &'static str,
    at: String,
}

fn pipelines(output: &mut String, index: &Index, commands: &[Command]) {
    output.push_str("## Pipelines\n\n");
    output.push_str(
        "An algorithm's full line appears where it is first placed, later as `= id (where)`.\n",
    );
    output.push_str("Phases are in stage-table `sequence`; a run marked `follows` has a declared `follows` edge between adjacent phases, one marked table order has none. Under a phase are the algorithms it `contains` (derived: the phase's call names one of their sites).\n");
    output.push_str("Representation flow runs upstream from the command's roots over `feeds` (producer of a representation → its consumer), stopping at algorithms an earlier command placed. `[n]` is the longest `feeds` path from a flow source; one `[n]` means no `feeds` order, listed by id; `⟲` marks a `feeds` cycle. Flow is data dependency, not observed execution order.\n\n");

    let mut placed = BTreeMap::<&str, Placement>::new();
    for command in commands {
        output.push_str(&format!("### {}\n\n", command.name));
        if command.phases {
            phase_outline(output, index, command, &mut placed);
        }
        flow_outline(output, index, command, &mut placed);
        output.push('\n');
    }

    let unplaced = index
        .algorithms
        .iter()
        .filter(|node| !placed.contains_key(node.id.as_str()))
        .collect::<Vec<_>>();
    if unplaced.is_empty() {
        return;
    }
    output.push_str("### Without a declared position\n\n");
    output.push_str("No phase contains these algorithms and no representation connects them to a command's roots; the graph does not say which command runs them or when.\n");
    output.push('\n');
    for node in unplaced {
        output.push_str(&format!("- {}\n", index.algorithm_line(node)));
    }
    output.push('\n');
}

fn phase_outline<'g>(
    output: &mut String,
    index: &Index<'g>,
    command: &Command,
    placed: &mut BTreeMap<&'g str, Placement>,
) {
    let mut phases = index
        .graph
        .nodes
        .iter()
        .filter(|node| node.kind == "phase")
        .collect::<Vec<_>>();
    if phases.is_empty() {
        return;
    }
    phases.sort_by_key(|phase| (phase.sequence.unwrap_or(usize::MAX), phase.id.clone()));
    let follows = index
        .edges("follows")
        .map(|edge| (edge.from.as_str(), edge.to.as_str()))
        .collect::<BTreeSet<_>>();
    let mut contains = BTreeMap::<&str, Vec<&str>>::new();
    for edge in index.edges("contains") {
        contains.entry(&edge.from).or_default().push(&edge.to);
    }

    // A segment is a maximal run of adjacent phases joined by `follows` edges, or a maximal run
    // of adjacent phases of one table with no `follows` edge between them.
    let mut segments = Vec::<(bool, Vec<&Node>)>::new();
    for phase in phases {
        let Some((chained, members)) = segments.last_mut() else {
            segments.push((false, vec![phase]));
            continue;
        };
        let previous = *members.last().expect("segments are never empty");
        let linked = follows.contains(&(previous.id.as_str(), phase.id.as_str()));
        if linked && (*chained || members.len() == 1) {
            *chained = true;
            members.push(phase);
        } else if linked {
            members.pop();
            segments.push((true, vec![previous, phase]));
        } else if !*chained && previous.table == phase.table {
            members.push(phase);
        } else {
            segments.push((false, vec![phase]));
        }
    }

    output.push_str("Phases:\n\n");
    for (chained, members) in segments {
        let tables = members
            .iter()
            .filter_map(|phase| phase.table.as_deref())
            .fold(Vec::<&str>::new(), |mut tables, table| {
                if !tables.contains(&table) {
                    tables.push(table);
                }
                tables
            })
            .iter()
            .map(|table| format!("`{table}`"))
            .collect::<Vec<_>>()
            .join(" + ");
        let first = sequence(members[0]);
        let last = sequence(members[members.len() - 1]);
        output.push_str(&format!(
            "- {tables} {first}–{last}, {}:\n",
            if chained { "follows" } else { "table order" }
        ));
        let separator = if chained { " → " } else { " · " };
        let mut idle = Vec::<String>::new();
        for phase in members {
            let label = format!("{} {}", sequence(phase), phase.id);
            let Some(algorithms) = contains.get(phase.id.as_str()) else {
                idle.push(label);
                continue;
            };
            if !idle.is_empty() {
                output.push_str(&format!("  - {}\n", idle.join(separator)));
                idle.clear();
            }
            let lines = algorithms
                .iter()
                .filter_map(|algorithm| index.nodes.get(algorithm))
                .map(|node| {
                    place(
                        index,
                        node,
                        command.name,
                        format!("phase {}", sequence(phase)),
                        placed,
                    )
                })
                .collect::<Vec<_>>();
            if let [line] = lines.as_slice()
                && line.starts_with("= ")
            {
                output.push_str(&format!("  - {label}: {line}\n"));
                continue;
            }
            output.push_str(&format!("  - {label}\n"));
            for line in lines {
                output.push_str(&format!("    - {line}\n"));
            }
        }
        if !idle.is_empty() {
            output.push_str(&format!("  - {}\n", idle.join(separator)));
        }
    }
    output.push('\n');
}

fn sequence(phase: &Node) -> String {
    phase
        .sequence
        .map_or_else(|| "?".to_owned(), |sequence| sequence.to_string())
}

/// The full line on first placement, a reference afterwards.
fn place<'g>(
    index: &Index<'g>,
    node: &'g Node,
    command: &'static str,
    at: String,
    placed: &mut BTreeMap<&'g str, Placement>,
) -> String {
    match placed.get(node.id.as_str()) {
        Some(placement) if placement.command == command => {
            format!("= {} ({})", node.id, placement.at)
        }
        Some(placement) => format!("= {} ({} {})", node.id, placement.command, placement.at),
        None => {
            placed.insert(&node.id, Placement { command, at });
            index.algorithm_line(node)
        }
    }
}

fn flow_outline<'g>(
    output: &mut String,
    index: &Index<'g>,
    command: &Command,
    placed: &mut BTreeMap<&'g str, Placement>,
) {
    let roots = index
        .representations
        .iter()
        .filter(|node| {
            node.type_path
                .as_deref()
                .is_some_and(|path| command.roots.contains(&path))
        })
        .map(|node| node.id.as_str())
        .collect::<Vec<_>>();
    let root_labels = roots
        .iter()
        .map(|root| index.label(root))
        .collect::<Vec<_>>()
        .join(", ");
    let earlier = |id: &str| {
        placed
            .get(id)
            .is_some_and(|placement| placement.command != command.name)
    };

    let mut members = BTreeSet::<&str>::new();
    let mut boundary = BTreeSet::<(&str, &str)>::new();
    let mut pending = roots
        .iter()
        .flat_map(|root| index.producers.get(root).into_iter().flatten())
        .copied()
        .collect::<Vec<_>>();
    pending.retain(|id| !earlier(id) && members.insert(id));
    // Invariant: `members` holds every algorithm reached so far upstream of the roots that no
    // earlier command placed, and `pending` holds members whose consumed representations are
    // unscanned; an id is pushed only when `members.insert` admits it.
    while let Some(current) = pending.pop() {
        for representation in index.consumes.get(current).into_iter().flatten() {
            for producer in index.producers.get(representation).into_iter().flatten() {
                if earlier(producer) {
                    boundary.insert((representation, producer));
                } else if members.insert(producer) {
                    pending.push(producer);
                }
            }
        }
    }
    if roots.is_empty() || members.is_empty() {
        output.push_str(&format!(
            "Representation flow: no algorithm produces {}.\n",
            if root_labels.is_empty() {
                "a root representation of the graph".to_owned()
            } else {
                root_labels
            }
        ));
        return;
    }
    output.push_str(&format!("Representation flow into {root_labels}:\n\n"));
    let mut inputs = BTreeMap::<&str, Vec<String>>::new();
    for (representation, producer) in &boundary {
        inputs
            .entry(producer)
            .or_default()
            .push(index.label(representation));
    }
    for (producer, labels) in inputs {
        let at = placed
            .get(producer)
            .map(|placement| format!("{} {}", placement.command, placement.at))
            .unwrap_or_default();
        output.push_str(&format!(
            "- from {at}: {producer} → {}\n",
            labels.join(", ")
        ));
    }

    let edges = members
        .iter()
        .map(|member| {
            let targets = index
                .feeds(member)
                .into_iter()
                .filter(|target| members.contains(target))
                .collect::<BTreeSet<_>>();
            (*member, targets)
        })
        .collect::<BTreeMap<_, _>>();
    let reach = members
        .iter()
        .map(|member| (*member, reachable(member, &edges)))
        .collect::<BTreeMap<_, _>>();
    let cyclic = |id: &str| reach[id].contains(id);
    let component = |id: &str| {
        members
            .iter()
            .copied()
            .filter(|other| {
                *other == id || (reach[id].contains(other) && reach[other].contains(id))
            })
            .collect::<BTreeSet<_>>()
    };
    let mut depth = BTreeMap::<&str, usize>::new();
    for member in &members {
        longest_path(member, &members, &edges, &component, &mut depth);
    }
    let mut ordered = members.iter().copied().collect::<Vec<_>>();
    ordered.sort_by_key(|id| (depth[id], *id));
    for id in ordered {
        let Some(node) = index.nodes.get(id) else {
            continue;
        };
        let at = format!("flow [{}]", depth[id]);
        output.push_str(&format!(
            "- [{}]{} {}\n",
            depth[id],
            if cyclic(id) { " ⟲" } else { "" },
            place(index, node, command.name, at, placed)
        ));
    }
}

fn reachable<'g>(start: &str, edges: &BTreeMap<&'g str, BTreeSet<&'g str>>) -> BTreeSet<&'g str> {
    let mut seen = BTreeSet::new();
    let mut pending = edges
        .get(start)
        .into_iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    // Invariant: `seen` holds the algorithms reached from `start` by one or more edges so far,
    // and `pending` holds reached algorithms whose edges are unscanned.
    while let Some(current) = pending.pop() {
        if seen.insert(current) {
            pending.extend(edges.get(current).into_iter().flatten().copied());
        }
    }
    seen
}

/// The longest `feeds` path from a source of the flow to `id`, counting a cycle as one step.
fn longest_path<'g>(
    id: &'g str,
    members: &BTreeSet<&'g str>,
    edges: &BTreeMap<&'g str, BTreeSet<&'g str>>,
    component: &dyn Fn(&str) -> BTreeSet<&'g str>,
    depth: &mut BTreeMap<&'g str, usize>,
) -> usize {
    if let Some(known) = depth.get(id) {
        return *known;
    }
    let own = component(id);
    let predecessors = members
        .iter()
        .copied()
        .filter(|candidate| !own.contains(candidate))
        .filter(|candidate| own.iter().any(|member| edges[candidate].contains(member)))
        .collect::<Vec<_>>();
    let value = predecessors
        .into_iter()
        .map(|predecessor| longest_path(predecessor, members, edges, component, depth) + 1)
        .max()
        .unwrap_or(0);
    for member in own {
        depth.insert(member, value);
    }
    value
}

fn representations(output: &mut String, index: &Index) {
    output.push_str("## Representations\n\n");
    output.push_str("`[label]` type: producers → consumers. `(n producers)` marks more than one producer; `none` means no card declares that side (an input file or another process).\n\n");
    for node in &index.representations {
        let list = |map: &BTreeMap<&str, BTreeSet<&str>>| {
            map.get(node.id.as_str())
                .filter(|set| !set.is_empty())
                .map(|set| set.iter().copied().collect::<Vec<_>>().join(", "))
                .unwrap_or_else(|| "none".to_owned())
        };
        let producer_count = index
            .producers
            .get(node.id.as_str())
            .map_or(0, BTreeSet::len);
        output.push_str(&format!(
            "- {} {}{}: {} → {}\n",
            index.label(&node.id),
            short_type(node.type_path.as_deref().unwrap_or(&node.id)),
            if producer_count > 1 {
                format!(" ({producer_count} producers)")
            } else {
                String::new()
            },
            list(&index.producers),
            list(&index.consumers)
        ));
    }
    output.push('\n');
}

fn contracts(output: &mut String, index: &Index) {
    let mut groups = BTreeMap::<&str, Vec<&crate::Edge>>::new();
    for edge in index.edges("constrains") {
        groups.entry(&edge.from).or_default().push(edge);
    }
    output.push_str("## Contracts\n\n");
    output.push_str("Each group names a producer whose output later algorithms or contracts rely on without a call (`constrains`), with the declared carrier (`via`); `query show` prints the consumer site.\n\n");
    for (producer, edges) in groups {
        output.push_str(&format!("- {producer}\n"));
        for edge in edges {
            output.push_str(&format!(
                "  - → {}: {}\n",
                edge.to,
                edge.detail.as_deref().unwrap_or("no carrier declared")
            ));
        }
    }
    output.push('\n');
}

fn fallbacks(output: &mut String, index: &Index) {
    output.push_str("## Fallbacks and variants\n\n");
    let mut any = false;
    for edge in index.edges("falls-back-to") {
        any = true;
        output.push_str(&format!(
            "- {} falls back to {}{}\n",
            edge.from,
            edge.to,
            edge.order
                .map(|order| format!(" (fallback {})", order + 1))
                .unwrap_or_default()
        ));
    }
    for edge in index.edges("variant-of") {
        any = true;
        if edge.from == edge.to {
            output.push_str(&format!(
                "- {} is a variant of itself (a variant site card names its own id)\n",
                edge.from
            ));
        } else {
            output.push_str(&format!("- {} is a variant of {}\n", edge.from, edge.to));
        }
    }
    if !any {
        output.push_str("- none declared\n");
    }
    output.push('\n');
}

fn entry_sites(output: &mut String, index: &Index) {
    let mut files = BTreeMap::<String, Vec<String>>::new();
    for node in &index.algorithms {
        let site = &node.anchor;
        files
            .entry(short_path(&site.file))
            .or_default()
            .push(format!("{} `{}`", node.id, site.symbol));
    }
    output.push_str("## Entry sites\n\n");
    output.push_str("The first site of each algorithm's primary card, grouped by file.\n\n");
    output.push_str("| file | algorithm `first site` |\n| --- | --- |\n");
    for (file, entries) in files {
        output.push_str(&format!("| {file} | {} |\n", entries.join("; ")));
    }
    output.push('\n');
}

fn leads_section(output: &mut String, index: &Index) {
    output.push_str("## Leads\n\n");
    output.push_str("A lead is structure computed from the graph that marks a place to look for a structural optimization, not a finding. Each line starts with its rule:\n\n");
    output.push_str("- `reconversion`: a representation converted into another and back, over two or three representations;\n");
    output.push_str("- `several producers`: one representation (type and role) produced by algorithms that are not a declared fallback or variant pair;\n");
    output.push_str(&format!("- `many declarers`: a counter claimed by {MANY_DECLARERS} or more cards, or a producer that {MANY_DECLARERS} or more consumers constrain (one property established or checked in several places);\n"));
    output.push_str("- `rebuild`: an algorithm that consumes a type and produces the same type with another role.\n\n");
    let lines = lead_lines(index);
    if lines.is_empty() {
        output.push_str("No rule fires.\n");
    }
    for line in lines {
        output.push_str(&format!("- {line}\n"));
    }
}

fn lead_lines(index: &Index) -> Vec<String> {
    let mut lines = reconversions(index);
    lines.extend(several_producers(index));
    lines.extend(many_declarers(index));
    lines.extend(rebuilds(index));
    lines
}

/// Representation cycles of length two or three through `consumes A, produces B` steps.
fn reconversions(index: &Index) -> Vec<String> {
    let mut steps = BTreeMap::<(&str, &str), BTreeSet<&str>>::new();
    for (algorithm, consumed) in &index.consumes {
        for input in consumed {
            for produced in index.produces.get(algorithm).into_iter().flatten() {
                if input != produced {
                    steps
                        .entry((input, produced))
                        .or_default()
                        .insert(algorithm);
                }
            }
        }
    }
    let successors = |from: &str| {
        steps
            .keys()
            .filter(move |(source, _)| *source == from)
            .map(|(_, target)| *target)
            .collect::<Vec<_>>()
    };
    let describe = |cycle: &[&str]| {
        let mut parts = Vec::new();
        for (position, from) in cycle.iter().enumerate() {
            let to = cycle[(position + 1) % cycle.len()];
            parts.push(format!(
                "{} → {} by {}",
                index.label(from),
                index.label(to),
                steps[&(*from, to)]
                    .iter()
                    .copied()
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        format!("reconversion: {}", parts.join("; "))
    };
    let mut lines = Vec::new();
    let starts = steps
        .keys()
        .map(|(source, _)| *source)
        .collect::<BTreeSet<_>>();
    for start in starts {
        for second in successors(start) {
            if second <= start {
                continue;
            }
            if steps.contains_key(&(second, start)) {
                lines.push(describe(&[start, second]));
            }
            for third in successors(second) {
                if third <= start || third == second {
                    continue;
                }
                if steps.contains_key(&(third, start)) {
                    lines.push(describe(&[start, second, third]));
                }
            }
        }
    }
    lines
}

/// Representations produced by more than one algorithm, unless every pair of producers is a
/// declared fallback or variant pair.
fn several_producers(index: &Index) -> Vec<String> {
    let related = index
        .edges("falls-back-to")
        .chain(index.edges("variant-of"))
        .flat_map(|edge| {
            [
                (edge.from.as_str(), edge.to.as_str()),
                (edge.to.as_str(), edge.from.as_str()),
            ]
        })
        .collect::<BTreeSet<_>>();
    let mut lines = Vec::new();
    for node in &index.representations {
        let Some(producers) = index.producers.get(node.id.as_str()) else {
            continue;
        };
        let producers = producers.iter().copied().collect::<Vec<_>>();
        let alternatives = producers.iter().enumerate().all(|(position, left)| {
            producers[position + 1..]
                .iter()
                .all(|right| related.contains(&(*left, *right)))
        });
        if producers.len() > 1 && !alternatives {
            lines.push(format!(
                "several producers: {} ← {}",
                index.label(&node.id),
                producers.join(", ")
            ));
        }
    }
    lines
}

/// Counters claimed by, and producers constrained by, [`MANY_DECLARERS`] or more cards.
fn many_declarers(index: &Index) -> Vec<String> {
    let mut claims = BTreeMap::<&str, BTreeSet<&str>>::new();
    for edge in index.edges("measured-by") {
        let is_counter = index.nodes.get(edge.to.as_str()).is_some_and(|node| {
            node.kind == "observation" && node.table.as_deref() == Some("Counter::ALL")
        });
        if is_counter {
            claims.entry(&edge.to).or_default().insert(&edge.from);
        }
    }
    let mut constrained = BTreeMap::<&str, BTreeSet<&str>>::new();
    for edge in index.edges("constrains") {
        constrained.entry(&edge.from).or_default().insert(&edge.to);
    }
    let mut lines = Vec::new();
    for (counter, algorithms) in claims {
        if algorithms.len() >= MANY_DECLARERS {
            lines.push(format!(
                "many declarers: counter {counter}, {} cards: {}",
                algorithms.len(),
                algorithms.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }
    }
    for (producer, consumers) in constrained {
        if consumers.len() >= MANY_DECLARERS {
            lines.push(format!(
                "many declarers: {producer} constrains {} consumers: {}",
                consumers.len(),
                consumers.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }
    }
    lines
}

/// Algorithms that consume a type and produce the same type with another role.
fn rebuilds(index: &Index) -> Vec<String> {
    let mut lines = Vec::new();
    for node in &index.algorithms {
        let id = node.id.as_str();
        let plain = |representation: &&str| {
            index
                .nodes
                .get(representation)
                .and_then(|node| node.type_path.as_deref())
                .map(plain_type)
        };
        for input in index.consumes.get(id).into_iter().flatten() {
            for output in index.produces.get(id).into_iter().flatten() {
                if input != output && plain(input).is_some() && plain(input) == plain(output) {
                    lines.push(format!(
                        "rebuild: {id} consumes {} and produces {}",
                        index.label(input),
                        index.label(output)
                    ));
                }
            }
        }
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Anchor, Cost, Edge};

    fn node(kind: &str, id: &str) -> Node {
        Node {
            kind: kind.to_owned(),
            id: id.to_owned(),
            provenance: "declared".to_owned(),
            anchor: Anchor {
                crate_name: "k-rust".to_owned(),
                file: format!("crates/k-rust/src/{}.rs", id.replace('.', "/")),
                symbol: "run".to_owned(),
            },
            area: None,
            name: Some(format!("the {id} algorithm")),
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
        }
    }

    fn algorithm(id: &str, bound: &str) -> Node {
        let mut node = node("algorithm", id);
        node.cost = vec![Cost {
            mode: "one call".to_owned(),
            bound: bound.to_owned(),
        }];
        node
    }

    fn phase(id: &str, table: &str, sequence: usize) -> Node {
        let mut node = node("phase", id);
        node.table = Some(table.to_owned());
        node.sequence = Some(sequence);
        node
    }

    fn representation(type_path: &str, role: &str) -> Node {
        let mut node = node("representation", &format!("{type_path} [{role}]"));
        node.type_path = Some(type_path.to_owned());
        node.role = Some(role.to_owned());
        node
    }

    fn counter(id: &str) -> Node {
        let mut node = node("observation", id);
        node.table = Some("Counter::ALL".to_owned());
        node
    }

    fn relation(kind: &str, from: &str, to: &str) -> Edge {
        Edge {
            kind: kind.to_owned(),
            from: from.to_owned(),
            to: to.to_owned(),
            provenance: "declared".to_owned(),
            detail: None,
            order: None,
            consumer_site: None,
        }
    }

    const ONE: &str = "k_rust::One [one]";
    const TWO: &str = "k_rust::Two [two]";
    const OUT: &str = "k_rust::Out [out]";

    const TEST_COMMANDS: &[Command] = &[Command {
        name: "build",
        roots: &["k_rust::Out"],
        phases: true,
    }];

    /// Phases p0 and p1 of table T1 without `follows`, p2 → p3 of table T2 with `follows`;
    /// the flow a.parse → a.lower → a.emit into the root, a.check in p3, a.idle unconnected.
    fn pipeline_graph() -> Graph {
        let mut graph = Graph {
            nodes: vec![
                phase("p0", "T1", 0),
                phase("p1", "T1", 1),
                phase("p2", "T2", 2),
                phase("p3", "T2", 3),
                algorithm("a.parse", "O(n)"),
                algorithm("a.lower", "O(n log n)"),
                algorithm("a.emit", "O(n)"),
                algorithm("a.check", "O(1)"),
                algorithm("a.idle", "O(1)"),
                representation("k_rust::One", "one"),
                representation("k_rust::Two", "two"),
                representation("k_rust::Out", "out"),
            ],
            edges: vec![
                relation("follows", "p2", "p3"),
                relation("contains", "p3", "a.check"),
                relation("contains", "p2", "a.lower"),
                relation("produces", "a.parse", ONE),
                relation("consumes", "a.lower", ONE),
                relation("produces", "a.lower", TWO),
                relation("consumes", "a.emit", TWO),
                relation("produces", "a.emit", OUT),
            ],
        };
        graph.sort();
        graph
    }

    #[test]
    fn phases_split_into_follows_runs_and_table_runs() {
        let map = render_map_with(&pipeline_graph(), TEST_COMMANDS);
        assert!(
            map.contains("- `T1` 0–1, table order:\n  - 0 p0 · 1 p1\n"),
            "{map}"
        );
        assert!(map.contains("- `T2` 2–3, follows:\n  - 2 p2\n    - a.lower — O(n log n) — in: [one] → out: [two]\n  - 3 p3\n    - a.check — O(1)\n"), "{map}");
    }

    #[test]
    fn flow_orders_producers_before_consumers_and_refers_back_to_phases() {
        let map = render_map_with(&pipeline_graph(), TEST_COMMANDS);
        let flow = map
            .split("Representation flow into [out]:\n\n")
            .nth(1)
            .expect("the flow is rendered");
        assert!(
            flow.starts_with(
                "- [0] a.parse — O(n) — out: [one]\n- [1] = a.lower (phase 2)\n- [2] a.emit — O(n) — in: [two] → out: [out]\n"
            ),
            "{flow}"
        );
        assert!(map.contains("### Without a declared position\n"), "{map}");
        assert!(map.contains("\n- a.idle — O(1)\n"), "{map}");
        assert!(!map.contains("- a.check — O(1)\n- a.idle"), "{map}");
    }

    #[test]
    fn a_later_command_stops_at_an_earlier_commands_algorithms() {
        let mut graph = pipeline_graph();
        graph.nodes.push(algorithm("b.run", "O(s)"));
        graph.nodes.push(representation("k_rust::Result", "result"));
        graph.edges.push(relation("consumes", "b.run", OUT));
        graph
            .edges
            .push(relation("produces", "b.run", "k_rust::Result [result]"));
        graph.sort();
        let commands = [
            TEST_COMMANDS[0],
            Command {
                name: "run",
                roots: &["k_rust::Result"],
                phases: false,
            },
        ];
        let map = render_map_with(&graph, &commands);
        assert!(
            map.contains("### run\n\nRepresentation flow into [result]:\n\n- from build flow [2]: a.emit → [out]\n- [0] b.run — O(s) — in: [out] → out: [result]\n"),
            "{map}"
        );
    }

    #[test]
    fn labels_fall_back_to_the_type_when_a_role_is_shared() {
        let mut graph = pipeline_graph();
        graph.nodes.push(representation("k_rust::Other", "one"));
        graph.sort();
        let map = render_map_with(&graph, TEST_COMMANDS);
        assert!(map.contains("out: [One: one]"), "{map}");
        assert!(
            map.contains("- [Other: one] k_rust::Other: none → none\n"),
            "{map}"
        );
    }

    #[test]
    fn representations_mark_several_producers() {
        let mut graph = pipeline_graph();
        graph.nodes.push(algorithm("a.alternative", "O(n)"));
        graph.edges.push(relation("produces", "a.alternative", ONE));
        graph.sort();
        let map = render_map_with(&graph, TEST_COMMANDS);
        assert!(
            map.contains("- [one] k_rust::One (2 producers): a.alternative, a.parse → a.lower\n"),
            "{map}"
        );
        assert!(
            map.contains("- [two] k_rust::Two: a.lower → a.emit\n"),
            "{map}"
        );
    }

    #[test]
    fn several_producers_fires_unless_the_producers_are_a_fallback_pair() {
        let mut graph = pipeline_graph();
        assert!(several_producers(&Index::new(&graph)).is_empty());
        graph.nodes.push(algorithm("a.alternative", "O(n)"));
        graph.edges.push(relation("produces", "a.alternative", ONE));
        graph.sort();
        assert_eq!(
            several_producers(&Index::new(&graph)),
            ["several producers: [one] ← a.alternative, a.parse"]
        );
        graph
            .edges
            .push(relation("falls-back-to", "a.parse", "a.alternative"));
        graph.sort();
        assert!(several_producers(&Index::new(&graph)).is_empty());
    }

    #[test]
    fn reconversion_fires_on_two_and_three_representation_cycles_only() {
        let mut graph = pipeline_graph();
        assert!(reconversions(&Index::new(&graph)).is_empty());
        graph.nodes.push(algorithm("a.raise", "O(n)"));
        graph.edges.push(relation("consumes", "a.raise", TWO));
        graph.edges.push(relation("produces", "a.raise", ONE));
        graph.sort();
        assert_eq!(
            reconversions(&Index::new(&graph)),
            ["reconversion: [one] → [two] by a.lower; [two] → [one] by a.raise"]
        );

        let mut graph = pipeline_graph();
        graph.nodes.push(algorithm("a.back", "O(n)"));
        graph.edges.push(relation("consumes", "a.back", OUT));
        graph.edges.push(relation("produces", "a.back", ONE));
        graph.sort();
        assert_eq!(
            reconversions(&Index::new(&graph)),
            [
                "reconversion: [one] → [two] by a.lower; [two] → [out] by a.emit; [out] → [one] by a.back"
            ]
        );

        graph.nodes.push(representation("k_rust::Four", "four"));
        graph
            .edges
            .retain(|edge| !(edge.from == "a.back" && edge.kind == "consumes"));
        graph
            .edges
            .push(relation("consumes", "a.back", "k_rust::Four [four]"));
        graph.nodes.push(algorithm("a.four", "O(n)"));
        graph.edges.push(relation("consumes", "a.four", OUT));
        graph
            .edges
            .push(relation("produces", "a.four", "k_rust::Four [four]"));
        graph.sort();
        assert!(
            reconversions(&Index::new(&graph)).is_empty(),
            "a four-representation cycle is not a lead"
        );
    }

    #[test]
    fn many_declarers_fires_at_three_cards_or_consumers() {
        let mut graph = pipeline_graph();
        graph.nodes.push(counter("Steps"));
        for id in ["a.parse", "a.lower"] {
            graph.edges.push(relation("measured-by", id, "Steps"));
        }
        for id in ["a.lower", "a.emit"] {
            let mut constraint = relation("constrains", "a.parse", id);
            constraint.detail = Some("a shared table".to_owned());
            graph.edges.push(constraint);
        }
        graph.sort();
        assert!(many_declarers(&Index::new(&graph)).is_empty());

        graph.edges.push(relation("measured-by", "a.emit", "Steps"));
        graph
            .edges
            .push(relation("constrains", "a.parse", "a.check"));
        graph.sort();
        assert_eq!(
            many_declarers(&Index::new(&graph)),
            [
                "many declarers: counter Steps, 3 cards: a.emit, a.lower, a.parse",
                "many declarers: a.parse constrains 3 consumers: a.check, a.emit, a.lower",
            ]
        );
    }

    #[test]
    fn rebuild_fires_on_one_type_with_two_roles() {
        let mut graph = pipeline_graph();
        assert!(rebuilds(&Index::new(&graph)).is_empty());
        graph.nodes.push(representation("k_rust::One", "refined"));
        graph
            .edges
            .push(relation("produces", "a.lower", "k_rust::One [refined]"));
        graph.sort();
        assert_eq!(
            rebuilds(&Index::new(&graph)),
            ["rebuild: a.lower consumes [one] and produces [refined]"]
        );
    }

    #[test]
    fn bounds_keep_the_first_mode_and_cut_long_text_on_a_word() {
        let mut node = algorithm(
            "a.long",
            "O(n) plus one pass over every sentence of every module in the definition",
        );
        node.cost.push(Cost {
            mode: "slow".to_owned(),
            bound: "O(n^2)".to_owned(),
        });
        assert_eq!(
            bounds(&node),
            "O(n) plus one pass over every sentence of every… +1 mode"
        );
        assert_eq!(bounds(&algorithm("a.short", "O(n)")), "O(n)");
    }

    #[test]
    fn paths_and_types_drop_the_crate_prefixes() {
        assert_eq!(
            short_path("crates/k-rust-backend/src/matching/mod.rs"),
            "backend/matching/mod.rs"
        );
        assert_eq!(short_path("crates/k-rust/src/main.rs"), "k-rust/main.rs");
        assert_eq!(
            short_type("k_rust_backend::matching::MatchResult"),
            "backend::matching::MatchResult"
        );
        assert_eq!(short_type("k_rust::kast::Term"), "k_rust::kast::Term");
    }

    #[test]
    fn the_workspace_map_is_deterministic_and_within_budget() {
        let graph = crate::build_graph(&crate::workspace_root()).unwrap().graph;
        let map = render_map(&graph);
        assert_eq!(map, render_map(&graph));
        let tokens = map.chars().count() / 4;
        assert!(
            tokens <= 8_000,
            "the map is {tokens} tokens, above the 8k budget"
        );
    }
}
