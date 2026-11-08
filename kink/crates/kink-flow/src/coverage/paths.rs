//! The syntax paths family (depth above 1; module documentation of [`crate::coverage`], "Syntax
//! paths"): its universe, read from the definition's grammar graph before any program runs, its
//! items before [`super::derive`] names them, and their derived part.

use super::{ARGUED, FIELD_VALUE, HEATING, PRODUCTION, REACHED, UNREACHED, at_of, ids, measure};
use super::{FIRED, MATCHED, UNMATCHED, position, without};
use crate::results::{ProgramRow, ResultClass};
use kink_corpus::admission::AdmissionRefusal;
use kink_native::coverage::GrammarGraph;
use kink_patch::SentenceRef;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The kind of a syntax paths item kink-flow builds: a path of the grammar graph.
pub const PATH: &str = "path";
/// The kind of a syntax paths item a front end adds: the joint values of a template's fields.
pub const FIELD_VALUES: &str = "field-values";

/// A path: its symbols by KORE name and the 0-based argument positions between them.
type Path = (Vec<String>, Vec<usize>);

/// The universe of the syntax paths family of depth `depth`: the grammar graph of the syntax
/// family's productions (kink-native `coverage::grammar_graph`), and the number of its paths of
/// each length `2..=depth`. Both are functions of the definition and the front end's selection,
/// computed before any program runs.
pub(super) struct Universe {
    graph: GrammarGraph,
    /// The productions' symbols, in the syntax family's order.
    order: Vec<String>,
    /// The number of paths of each length from 2, saturating.
    by_length: Vec<u64>,
}

impl Universe {
    /// The universe of `spec` under `manifest`'s syntax selection at `depth`, or why the
    /// definition could not be read.
    pub(super) fn of(
        spec: &crate::admit::AdmittedSpec,
        manifest: &crate::manifest::FlowManifest,
        depth: usize,
    ) -> Result<Self, String> {
        let definition = spec.definition.as_ref().map_err(Clone::clone)?;
        let facts = spec.syntax.as_ref().map_err(Clone::clone)?;
        let order = super::productions(spec, manifest, facts)
            .into_iter()
            .map(|production| production.symbol)
            .collect::<Vec<_>>();
        let graph =
            kink_native::coverage::grammar_graph(definition, &order.iter().cloned().collect());
        // The paths of `k` symbols from each symbol, for k = 1, 2, ...
        let mut from = order
            .iter()
            .map(|symbol| (symbol.as_str(), 1_u64))
            .collect::<BTreeMap<_, _>>();
        let mut by_length = Vec::new();
        for _ in 2..=depth {
            from = order
                .iter()
                .map(|symbol| {
                    let paths = graph
                        .arguments(symbol)
                        .iter()
                        .flatten()
                        .filter_map(|next| from.get(next.as_str()))
                        .fold(0_u64, |sum, paths| sum.saturating_add(*paths));
                    (symbol.as_str(), paths)
                })
                .collect();
            by_length.push(
                from.values()
                    .fold(0_u64, |sum, paths| sum.saturating_add(*paths)),
            );
        }
        Ok(Self {
            graph,
            order,
            by_length,
        })
    }

    /// The number of obligations, saturating.
    pub(super) fn obligations(&self) -> u64 {
        self.by_length
            .iter()
            .fold(0, |sum, count| sum.saturating_add(*count))
    }

    /// The refusal of a universe larger than `max` (`[coverage] max_obligations`), with its
    /// counts, or `None`.
    pub(super) fn refusal(&self, max: u64) -> Option<AdmissionRefusal> {
        let obligations = self.obligations();
        let counted = self
            .by_length
            .iter()
            .enumerate()
            .map(|(index, count)| format!("length {}: {count}", index + 2))
            .collect::<Vec<_>>()
            .join(", ");
        (obligations > max).then(|| AdmissionRefusal {
            stage: "coverage".into(),
            reason: "max-obligations".into(),
            detail: format!(
                "the syntax paths family has {obligations} obligations ({counted}; the grammar \
                 graph has {} productions and {} edges), more than [coverage] max_obligations = \
                 {max}: lower the depth, or raise max_obligations to count them",
                self.order.len(),
                self.graph.edges(),
            ),
        })
    }
}

/// The syntax paths family before [`derive`] (module documentation of [`crate::coverage`],
/// "Syntax paths"), from `universe`, the comparable programs' records (`rows`, in manifest
/// order), the rules family's items (`rules`, whose sentences of the rules universe count, as
/// for the syntax family) and the syntax family's items (`syntax`, which say which productions
/// are reached, a path of length 1).
///
/// Each item is a path of the universe, by length then in the productions' order, each path's
/// extensions in argument then production order: its `symbols`, its 0-based argument `positions`,
/// its `length`, the comparable programs whose record holds it (`covered_by`) and the others
/// (`uncounted`), and whether it is on the frontier (`frontier`: not reached, while the path of
/// its first `length - 1` symbols is, a single production being reached when the syntax family
/// says so). `outside_universe` lists the paths of the productions a comparable program's record
/// holds that the graph does not: the graph is an over-approximation, so the list is empty
/// unless it failed, and its paths are not counted.
pub(super) fn family(
    universe: &Universe,
    depth: usize,
    rows: &[ProgramRow],
    programs: &[crate::manifest::Program],
    rules: &[Value],
    syntax: &[Value],
) -> Value {
    let counted = rules
        .iter()
        .filter(|rule| rule["kind"] != HEATING)
        .filter(|rule| matches!(rule["status"].as_str(), Some(FIRED | MATCHED | UNMATCHED)))
        .filter_map(at_of)
        .collect::<BTreeSet<SentenceRef>>();
    let nodes = universe.order.iter().cloned().collect::<BTreeSet<_>>();
    // Per path the records hold, the comparable programs and then the others.
    let mut taken = BTreeMap::<Path, [Vec<&str>; 2]>::new();
    for (program, row) in programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        let slot = usize::from(!ResultClass::can_kill(&record["class"]));
        for sentence in record["coverage"]["bindings"]["paths"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|sentence| at_of(sentence).is_some_and(|at| counted.contains(&at)))
        {
            for path in sentence["paths"].as_array().into_iter().flatten() {
                let symbols = path["symbols"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|symbol| symbol.as_str().map(str::to_owned))
                    .collect::<Option<Vec<_>>>();
                let positions = path["positions"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|position| position.as_u64().and_then(|p| usize::try_from(p).ok()))
                    .collect::<Option<Vec<_>>>();
                let (Some(symbols), Some(positions)) = (symbols, positions) else {
                    continue;
                };
                if !(2..=depth).contains(&symbols.len()) || positions.len() + 1 != symbols.len() {
                    continue;
                }
                let lists = taken.entry((symbols, positions)).or_default();
                if !lists[slot].contains(&program.id.as_str()) {
                    lists[slot].push(&program.id);
                }
            }
        }
    }
    let reached = syntax
        .iter()
        .filter(|item| item["kind"] == PRODUCTION && item["status"] == REACHED)
        .filter_map(|item| item["symbol"].as_str())
        .collect::<BTreeSet<_>>();
    let mut items = Vec::new();
    let mut level = universe
        .order
        .iter()
        .map(|symbol| (vec![symbol.clone()], Vec::new()))
        .collect::<Vec<Path>>();
    let mut covered_paths = universe
        .order
        .iter()
        .filter(|symbol| reached.contains(symbol.as_str()))
        .map(|symbol| (vec![symbol.clone()], Vec::new()))
        .collect::<BTreeSet<Path>>();
    let mut universe_paths = BTreeSet::new();
    for _ in 2..=depth {
        let mut next = Vec::new();
        let mut covered_here = BTreeSet::new();
        for prefix in &level {
            let last = prefix.0.last().expect("a path has a symbol");
            for (position, successors) in universe.graph.arguments(last).iter().enumerate() {
                for successor in universe
                    .order
                    .iter()
                    .filter(|symbol| successors.contains(*symbol))
                {
                    let mut path = prefix.clone();
                    path.0.push(successor.clone());
                    path.1.push(position);
                    let [covered_by, uncounted] = taken.get(&path).cloned().unwrap_or_default();
                    let covered = !covered_by.is_empty();
                    let frontier = !covered && covered_paths.contains(prefix);
                    if covered {
                        covered_here.insert(path.clone());
                    }
                    items.push(json!({
                        "kind": PATH,
                        "length": path.0.len(),
                        "symbols": path.0,
                        "positions": path.1,
                        "status": if covered { REACHED } else { UNREACHED },
                        "covered_by": covered_by,
                        "uncounted": uncounted,
                        "frontier": frontier,
                    }));
                    universe_paths.insert(path.clone());
                    next.push(path);
                }
            }
        }
        covered_paths = covered_here;
        level = next;
    }
    let outside = taken
        .iter()
        .filter(|(path, lists)| {
            !lists[0].is_empty()
                && path.0.iter().all(|symbol| nodes.contains(symbol))
                && !universe_paths.contains(*path)
        })
        .map(|((symbols, positions), lists)| {
            json!({"symbols": symbols, "positions": positions, "covered_by": lists[0]})
        })
        .collect::<Vec<_>>();
    json!({
        "tier": 1,
        "depth": depth,
        "productions": universe.order.len(),
        "edges": universe.graph.edges(),
        "items": items,
        "outside_universe": outside,
    })
}

/// The syntax paths family of a document whose definition could not be read: no universe, and
/// why.
pub(super) fn unread(depth: usize, reason: &str) -> Value {
    json!({"tier": 1, "depth": depth, "items": [], "outside_universe": [], "reason": reason})
}

/// What [`derive`] gives the document's derivation: `(covered, obligations)` (`None` without a
/// universe) and the family's targets, in item order.
pub(super) struct Derived {
    pub(super) counts: Option<(usize, usize)>,
    pub(super) targets: Vec<Value>,
}

/// Fill the derived part of the syntax paths family `family` ([`family`]): each item's `id`,
/// `obligation`, `covered` and `touched_only_by`, the counts and the measure, and a target per
/// open path on the frontier. `syntax` are the syntax family's items as [`super::derive`] named
/// them, whose names a path's id spells (`path:<production>/<position>/<production>...`), and
/// `argued` the `[[coverage.argued]]` entries. An item a front end added (kind [`FIELD_VALUES`])
/// is named by its front end (`path:<krs.item>`), states its own frontier, its target's text
/// (`krs.target`) and the field values it joins (`krs.parts`, their `krs.item`s): a field value
/// argued while unreached argues every joint value that holds it, since an instance that binds
/// the joint value binds each of its field values.
///
/// A path no entry names whose first production an entry argues while it is unreached, or one of
/// whose prefixes (a path of its first symbols, two or more) an entry argues while no program
/// covers it, is `argued` too, with `argued_by` naming that item: a fired instance touches the
/// first position of each path it records (a position of its own text, or the root of a value it
/// reads), so the argument that no instance touches the production, or no instance records the
/// prefix, is one that no instance records the path. No other part argues it: a path's later
/// symbols lie below a touched position without being touched themselves.
pub(super) fn derive(
    family: &mut Value,
    syntax: &[Value],
    argued: &BTreeMap<String, String>,
) -> Derived {
    let none = Derived {
        counts: None,
        targets: Vec::new(),
    };
    if !family.is_object() {
        return none;
    }
    // Each production's name, its syntax item's id without `syntax:`, and whether it is argued
    // while unreached.
    let productions = syntax
        .iter()
        .filter(|item| item["kind"] == PRODUCTION)
        .filter_map(|item| {
            let id = item["id"].as_str()?;
            Some((item["symbol"].as_str()?, (id, item)))
        })
        .collect::<BTreeMap<_, _>>();
    // Each field value a front end added, by its name (`krs.item`).
    let field_values = syntax
        .iter()
        .filter(|item| item["kind"] == FIELD_VALUE)
        .filter_map(|item| Some((item["krs"]["item"].as_str()?, item)))
        .collect::<BTreeMap<_, _>>();
    let name = |symbol: &str| {
        productions.get(symbol).map_or_else(
            || symbol.to_owned(),
            |(id, _)| id.strip_prefix("syntax:").unwrap_or(id).to_owned(),
        )
    };
    let Some(items) = family.get_mut("items").and_then(Value::as_array_mut) else {
        return none;
    };
    let mut targets = Vec::new();
    let mut by_length = BTreeMap::<u64, [usize; 2]>::new();
    let mut covered_count = 0;
    let mut frontier_count = 0;
    // The paths argued while open, by their symbols and positions.
    let mut argued_paths = BTreeMap::<Path, String>::new();
    let mut prefix_programs = BTreeMap::<Path, Value>::new();
    for item in items.iter_mut() {
        if let Some(object) = item.as_object_mut() {
            for derived in [
                "argument",
                "argument_needless",
                "unargued_status",
                "argued_by",
            ] {
                object.remove(derived);
            }
        }
        let covered_by = ids(&item["covered_by"]);
        let covered = !covered_by.is_empty() || item["status"] == REACHED;
        let length = item["length"].as_u64().unwrap_or(0);
        let counts = by_length.entry(length).or_default();
        counts[0] += 1;
        counts[1] += usize::from(covered);
        covered_count += usize::from(covered);
        item["obligation"] = json!(true);
        item["covered"] = json!(covered);
        item["status"] = json!(if covered { REACHED } else { UNREACHED });
        item["touched_only_by"] = json!(if covered {
            Vec::new()
        } else {
            without(ids(&item["uncounted"]), &[])
        });
        if item["kind"] == FIELD_VALUES {
            let id = format!("path:{}", item["krs"]["item"].as_str().unwrap_or_default());
            item["id"] = json!(id);
            if covered || argued.contains_key(&id) {
                continue;
            }
            // A field value of the joint values argued while unreached argues them.
            let by_part = item["krs"]["parts"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .find_map(|part| {
                    let value = field_values.get(part)?;
                    let id = value["id"].as_str()?;
                    (value["covered"] == false && argued.contains_key(id)).then(|| id.to_owned())
                });
            if let Some(by) = by_part {
                item["unargued_status"] = json!(UNREACHED);
                item["status"] = json!(ARGUED);
                item["argument"] = json!(argued.get(&by).cloned().unwrap_or_default());
                item["argued_by"] = json!(by);
                continue;
            }
            if item["frontier"] != true {
                continue;
            }
            frontier_count += 1;
            let (file, line) = position(item);
            let touched = ids(&item["touched_only_by"]);
            targets.push(json!({
                "family": "syntax_paths",
                "item": id,
                "text": format!(
                    "{}{}",
                    item["krs"]["target"].as_str().unwrap_or_default(),
                    super::touched_note(&touched)
                ),
                "file": file,
                "line": line,
                "programs": item["programs"].clone(),
                "pattern": null,
                "fuzz": null,
            }));
            continue;
        }
        let symbols = item["symbols"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect::<Vec<_>>();
        let positions = item["positions"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_u64)
            .filter_map(|position| usize::try_from(position).ok())
            .collect::<Vec<_>>();
        let names = symbols
            .iter()
            .map(|symbol| name(symbol))
            .collect::<Vec<_>>();
        let mut spelled = names[0].clone();
        for (position, name) in positions.iter().zip(&names[1..]) {
            spelled.push_str(&format!("/{position}/{name}"));
        }
        let id = format!("path:{spelled}");
        item["id"] = json!(id);
        let path = (symbols.clone(), positions.clone());
        if covered {
            prefix_programs.insert(path, item["covered_by"].clone());
            continue;
        }
        if argued.contains_key(&id) {
            argued_paths.insert(path.clone(), id.clone());
        }
        // The first production argued while unreached, then a prefix argued while open, which
        // precedes this path in item order.
        let first = productions.get(symbols[0].as_str()).and_then(|(id, item)| {
            (item["covered"] == false && argued.contains_key(*id)).then(|| (*id).to_owned())
        });
        let by_part = first.or_else(|| {
            (2..symbols.len()).rev().find_map(|length| {
                argued_paths
                    .get(&(symbols[..length].to_vec(), positions[..length - 1].to_vec()))
                    .cloned()
            })
        });
        if !argued.contains_key(&id)
            && let Some(by) = by_part
        {
            argued_paths.insert(path, by.clone());
            item["unargued_status"] = json!(UNREACHED);
            item["status"] = json!(ARGUED);
            item["argument"] = json!(argued.get(&by).cloned().unwrap_or_default());
            item["argued_by"] = json!(by);
            continue;
        }
        if item["frontier"] != true {
            continue;
        }
        frontier_count += 1;
        let mut text = format!("a case in which a fired step touches {}", names[0]);
        for (index, (position, name)) in positions.iter().zip(&names[1..]).enumerate() {
            text.push_str(&if index == 0 {
                format!(" holding {name} at argument {position}")
            } else {
                format!(", which holds {name} at argument {position}")
            });
        }
        let prefix = (
            symbols[..symbols.len() - 1].to_vec(),
            positions[..positions.len() - 1].to_vec(),
        );
        let programs = if prefix.0.len() == 1 {
            productions
                .get(symbols[0].as_str())
                .map_or(Value::Array(Vec::new()), |(_, item)| {
                    item["reached_by"].clone()
                })
        } else {
            prefix_programs
                .get(&prefix)
                .cloned()
                .unwrap_or(Value::Array(Vec::new()))
        };
        let reached = ids(&programs);
        // The cases that reached the prefix, the templates of a case that extends it.
        let prefix_text = if prefix.0.len() == 1 {
            names[0].clone()
        } else {
            format!("its first {} productions", prefix.0.len())
        };
        text.push_str(&if reached.is_empty() {
            format!("; no comparable case reaches {prefix_text}")
        } else {
            format!(
                "; the comparable cases that reach {prefix_text}: {}",
                reached.join(", ")
            )
        });
        let first_production = productions
            .get(symbols[0].as_str())
            .map_or(&Value::Null, |(_, item)| *item);
        let (file, line) = position(first_production);
        targets.push(json!({
            "family": "syntax_paths",
            "item": id,
            "text": text,
            "file": file,
            "line": line,
            "programs": programs,
            "pattern": null,
            "fuzz": null,
        }));
    }
    let obligations = items.len();
    let argued_count = items.iter().filter(|item| item["status"] == ARGUED).count();
    let mut lengths = Map::new();
    for (length, [obligations, covered]) in by_length {
        lengths.insert(
            length.to_string(),
            json!({"obligations": obligations, "covered": covered}),
        );
    }
    let kind = |kind: &str| {
        let of_kind = items
            .iter()
            .filter(|item| item["kind"] == kind)
            .collect::<Vec<_>>();
        json!({
            "obligations": of_kind.len(),
            "covered": of_kind.iter().filter(|item| item["covered"] == true).count(),
        })
    };
    let (paths, field_values) = (kind(PATH), kind(FIELD_VALUES));
    family["obligations"] = json!(obligations);
    family["covered"] = json!(covered_count);
    family["measure"] = measure(covered_count, obligations);
    family["counts"] = json!({
        "reached": covered_count,
        "unreached": obligations - covered_count - argued_count,
        "argued": argued_count,
        "frontier": frontier_count,
        "by_length": lengths,
        "paths": paths,
        "field_values": field_values,
    });
    Derived {
        counts: if family["reason"].is_string() {
            None
        } else {
            Some((covered_count, obligations))
        },
        targets,
    }
}
