//! Guard outcomes in result records: what a program's baseline run saw of each guard of the
//! specification's authored sentences (k-rust `coverage.guards`, kink-native
//! `TestCoverage::guards`).
//!
//! A record holds, per baseline sentence with a guarded compiled axiom, each axiom's nodes (its
//! written `requires` in preorder: path, shape, and the outcomes the node took where it was
//! reached), its guard outcomes, and its valuation combinations. Atom terms are compact KORE
//! text, as a record's ends are. The coverage document reads them ([`crate::coverage`]).

use k_rust::backend::{AxiomGuardOutput, GuardShapeOutput};
use k_rust::kore::ast::Pattern;
use kink_native::coverage::TestCoverage;
use serde_json::{Value, json};

/// The record value of one axiom's guard outcomes.
fn axiom_value(guard: &AxiomGuardOutput<Pattern>) -> Value {
    let nodes = guard
        .nodes
        .iter()
        .map(|node| {
            let shape = match &node.shape {
                GuardShapeOutput::Connective { connective } => {
                    json!({"node": "connective", "connective": connective})
                }
                GuardShapeOutput::Equals { literal } => {
                    json!({"node": "equals", "literal": literal})
                }
                GuardShapeOutput::Term { term } => {
                    json!({"node": "term", "kore": term.to_string()})
                }
                GuardShapeOutput::Predicate { term } => {
                    json!({"node": "predicate", "kore": term.to_string()})
                }
            };
            json!({"path": node.path, "shape": shape, "reached": node.reached})
        })
        .collect::<Vec<_>>();
    json!({
        "axiom": guard.axiom,
        "nodes": nodes,
        "outcomes": guard.outcomes,
        "combinations": guard.combinations,
        "combinations_truncated": guard.combinations_truncated,
    })
}

/// A record's guard outcomes: per baseline sentence (`module`, `index`), its guarded axioms,
/// in sentence order.
pub(crate) fn record_value(coverage: &TestCoverage) -> Value {
    Value::Array(
        coverage
            .guards
            .iter()
            .map(|(at, guards)| {
                json!({
                    "module": at.module,
                    "index": at.index,
                    "axioms": guards.iter().map(axiom_value).collect::<Vec<_>>(),
                })
            })
            .collect(),
    )
}

/// The token of a node outcome a record holds that a row reports under `true_by`.
const TRUE: &str = "true";
const FALSE: &str = "false";
const UNDEFINED: &str = "undefined";

/// The guard entries of one sentence: each comparable program's axioms that the sentence
/// compiled to, as its record holds them.
#[derive(Default)]
pub(crate) struct SentenceGuards<'r> {
    entries: Vec<(&'r str, &'r Value)>,
}

impl<'r> SentenceGuards<'r> {
    /// The guard entries of every sentence in `records`, each a comparable program's id and its
    /// record, by `(module, index)`.
    pub(crate) fn of(
        records: impl IntoIterator<Item = (&'r str, &'r Value)>,
    ) -> std::collections::BTreeMap<(String, u64), Self> {
        let mut by_sentence = std::collections::BTreeMap::<(String, u64), Self>::new();
        for (program, record) in records {
            for sentence in record["coverage"]["guards"]
                .as_array()
                .into_iter()
                .flatten()
            {
                let (Some(module), Some(index)) =
                    (sentence["module"].as_str(), sentence["index"].as_u64())
                else {
                    continue;
                };
                let slot = by_sentence.entry((module.to_owned(), index)).or_default();
                for axiom in sentence["axioms"].as_array().into_iter().flatten() {
                    slot.entries.push((program, axiom));
                }
            }
        }
        by_sentence
    }
}

/// The programs of one outcome class, in corpus order, each once.
#[derive(Default)]
struct Programs(Vec<String>);

impl Programs {
    fn add(&mut self, program: &str) {
        if !self.0.iter().any(|known| known == program) {
            self.0.push(program.to_owned());
        }
    }
}

/// The undecided programs of a node or a guard, each with its causes.
#[derive(Default)]
struct Undecided(Vec<(String, Vec<String>)>);

impl Undecided {
    fn add(&mut self, program: &str, cause: &str) {
        if let Some((_, causes)) = self.0.iter_mut().find(|(known, _)| known == program) {
            if !causes.iter().any(|known| known == cause) {
                causes.push(cause.to_owned());
                causes.sort();
            }
        } else {
            self.0.push((program.to_owned(), vec![cause.to_owned()]));
        }
    }

    fn value(&self) -> Value {
        Value::Array(
            self.0
                .iter()
                .map(|(program, causes)| json!({"program": program, "causes": causes}))
                .collect(),
        )
    }
}

/// The outcomes one node took over the comparable programs.
#[derive(Default)]
struct NodeOutcomes {
    true_by: Programs,
    false_by: Programs,
    undefined_by: Programs,
    undecided_by: Undecided,
}

impl NodeOutcomes {
    fn add(&mut self, program: &str, outcome: &str) {
        match outcome {
            TRUE => self.true_by.add(program),
            FALSE => self.false_by.add(program),
            UNDEFINED => self.undefined_by.add(program),
            other => self
                .undecided_by
                .add(program, other.strip_prefix("undecided-").unwrap_or(other)),
        }
    }

    /// The two-valued outcomes no program saw: `true` and `false` (an undefined Boolean is
    /// neither, and an undecided entry decides nothing).
    fn never(&self) -> Vec<&'static str> {
        let mut never = Vec::new();
        if self.true_by.0.is_empty() {
            never.push(TRUE);
        }
        if self.false_by.0.is_empty() {
            never.push(FALSE);
        }
        never
    }

    /// Fill `value`, a node's object, with the outcomes; with `never` where the node's outcomes
    /// are its own ([`own_outcomes`]).
    fn fill(&self, value: &mut Value, own: bool) {
        value["true_by"] = json!(self.true_by.0);
        value["false_by"] = json!(self.false_by.0);
        value["undefined_by"] = json!(self.undefined_by.0);
        value["undecided_by"] = self.undecided_by.value();
        if own {
            value["never"] = json!(self.never());
        }
    }
}

/// Whether a node of kind `kind` (a row's `guard.operands[].kind`) has outcomes of its own, which
/// its operands' reported outcomes do not already state, so that a gap in them is a gap of the
/// node: an atom, and an exclusive connective (`xorBool`, `\iff`), both of whose operands are
/// reached on every entry, so that its truth is a function of their joint values, which the
/// per-node sets do not hold. A conjunction is `true` where its last operand was reached `true`
/// and `false` where some operand was reached `false`, a disjunction dually, an implication is
/// `notBool A orBool B`, and a negation and an `\equals(b, literal)` restate their operand's:
/// their gaps are their operands' gaps, so they carry no `never`.
#[must_use]
pub fn own_outcomes(kind: &str) -> bool {
    matches!(kind, "atom" | "exclusive")
}

/// A node of the skeleton a record holds.
struct Node<'r> {
    path: Vec<u64>,
    shape: &'r Value,
}

fn skeleton(axiom: &Value) -> Vec<Node<'_>> {
    axiom["nodes"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|node| Node {
            path: node["path"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_u64)
                .collect(),
            shape: &node["shape"],
        })
        .collect()
}

/// The kind a row names a connective by: conjunctions, disjunctions, implications, the
/// exclusive connectives, negations.
fn connective_kind(connective: &str) -> &'static str {
    match connective {
        "andBool" | "andThenBool" | "\\and" => "conjunction",
        "orBool" | "orElseBool" | "\\or" => "disjunction",
        "impliesBool" | "\\implies" => "implication",
        "xorBool" | "\\iff" => "exclusive",
        _ => "negation",
    }
}

/// Prints a skeleton's atoms as K text.
pub(crate) trait AtomPrinter {
    /// The text of the atom whose compact KORE text is `kore`.
    fn print(&self, kore: &str) -> String;
}

impl AtomPrinter for crate::evidence::EndReader {
    fn print(&self, kore: &str) -> String {
        match k_rust::kore::parser::parse_pattern(kore) {
            Ok(pattern) => self.print(&pattern, ATOM_CAP)["text"]
                .as_str()
                .unwrap_or(kore)
                .to_owned(),
            Err(_) => kore.to_owned(),
        }
    }
}

/// The most characters of an atom's text a row shows.
const ATOM_CAP: usize = 400;

/// The rendering of one sentence's skeleton: its operand nodes in display order.
struct Rendering<'s, 'r> {
    nodes: &'s [Node<'r>],
    printer: &'s dyn AtomPrinter,
    /// Per skeleton node, its display path, when it is shown.
    shown: Vec<Option<String>>,
    operands: Vec<Value>,
}

impl Rendering<'_, '_> {
    fn index(&self, path: &[u64]) -> Option<usize> {
        self.nodes.iter().position(|node| node.path == path)
    }

    fn children(&self, path: &[u64]) -> Vec<usize> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| node.path.len() == path.len() + 1 && node.path.starts_with(path))
            .map(|(index, _)| index)
            .collect()
    }

    /// The operands of the connective at `index`, a left-nested chain of one connective read as
    /// one n-ary node: the skeleton indices of its display operands.
    fn chain(&self, index: usize, connective: &str) -> Vec<usize> {
        let children = self.children(&self.nodes[index].path);
        let mut operands = Vec::new();
        if let Some((first, rest)) = children.split_first() {
            if self.nodes[*first].shape["node"] == "connective"
                && self.nodes[*first].shape["connective"] == connective
                && matches!(connective_kind(connective), "conjunction" | "disjunction")
            {
                operands.extend(self.chain(*first, connective));
            } else {
                operands.push(*first);
            }
            operands.extend(rest.iter().copied());
        }
        operands
    }

    /// Show the node at `index` under the display path `path`, and below it; returns its text.
    fn show(&mut self, index: usize, path: String) -> String {
        self.shown[index] = Some(path.clone());
        let shape = self.nodes[index].shape;
        let mut value = json!({"path": path});
        let text = match shape["node"].as_str() {
            Some("connective") => {
                let connective = shape["connective"].as_str().unwrap_or_default().to_owned();
                let operands = self.chain(index, &connective);
                let position = self.operands.len();
                self.operands.push(Value::Null);
                let mut paths = Vec::new();
                let mut texts = Vec::new();
                for (k, operand) in operands.iter().enumerate() {
                    let child = format!("{path}.{k}");
                    paths.push(child.clone());
                    let text = self.show(*operand, child);
                    let nested = self.nodes[*operand].shape["node"] == "connective";
                    texts.push(if nested { format!("({text})") } else { text });
                }
                value["kind"] = json!(connective_kind(&connective));
                value["connective"] = json!(connective);
                value["operands"] = json!(paths);
                let text = if texts.len() == 1 {
                    format!("{connective} {}", texts[0])
                } else {
                    texts.join(&format!(" {connective} "))
                };
                value["text"] = json!(text);
                self.operands[position] = value;
                return text;
            }
            Some("equals") => {
                let children = self.children(&self.nodes[index].path);
                let position = self.operands.len();
                self.operands.push(Value::Null);
                let literal = shape["literal"].as_bool().unwrap_or(true);
                let child = format!("{path}.0");
                let inner = children
                    .first()
                    .map(|child_index| self.show(*child_index, child.clone()))
                    .unwrap_or_default();
                let text = format!("\\equals({inner}, {literal})");
                value["kind"] = json!("equals");
                value["operands"] = json!([child]);
                value["text"] = json!(text);
                self.operands[position] = value;
                return text;
            }
            _ => self
                .printer
                .print(shape["kore"].as_str().unwrap_or_default()),
        };
        value["kind"] = json!("atom");
        value["text"] = json!(text);
        self.operands.push(value);
        text
    }
}

/// The record values of a sentence's static skeletons (kink-native `coverage::guard_skeletons`),
/// as a record holds its axioms, in axiom order.
pub(crate) fn skeleton_values(skeletons: &[AxiomGuardOutput<Pattern>]) -> Vec<Value> {
    let mut values = skeletons.iter().map(axiom_value).collect::<Vec<_>>();
    values.sort_by_key(|axiom| axiom["axiom"].as_str().map(str::to_owned));
    values
}

/// The guard outcomes of `entries` (program, axiom): the programs of each class, in corpus
/// order.
#[derive(Default)]
struct GuardOutcomes {
    held: Programs,
    refuted: Programs,
    undefined: Programs,
    solver: Programs,
    stopped: Programs,
    undecided: Undecided,
}

impl GuardOutcomes {
    fn of(entries: &[(&str, &Value)]) -> Self {
        let mut outcomes = Self::default();
        for (program, axiom) in entries {
            for outcome in axiom["outcomes"].as_array().into_iter().flatten() {
                let outcome = outcome.as_str().unwrap_or_default();
                let into: Option<&mut Programs> = match outcome {
                    "held" => Some(&mut outcomes.held),
                    "stopped" => Some(&mut outcomes.stopped),
                    "refuted-false" => Some(&mut outcomes.refuted),
                    "refuted-undefined" => {
                        outcomes.undefined.add(program);
                        Some(&mut outcomes.refuted)
                    }
                    "refuted-decided" => {
                        outcomes.solver.add(program);
                        Some(&mut outcomes.refuted)
                    }
                    other => {
                        outcomes
                            .undecided
                            .add(program, other.strip_prefix("undecided-").unwrap_or(other));
                        None
                    }
                };
                if let Some(into) = into {
                    into.add(program);
                }
            }
        }
        outcomes
    }
}

/// The entries of `entries`, by axiom.
fn sorted<'r>(entries: Option<&SentenceGuards<'r>>) -> Vec<(&'r str, &'r Value)> {
    let mut entries = entries.map(|e| e.entries.clone()).unwrap_or_default();
    entries.sort_by_key(|(_, axiom)| axiom["axiom"].as_str().map(str::to_owned));
    entries
}

/// The outcomes each skeleton node took over `entries`, by preorder index.
fn node_outcomes(entries: &[(&str, &Value)], nodes: usize) -> Vec<NodeOutcomes> {
    let mut outcomes = (0..nodes)
        .map(|_| NodeOutcomes::default())
        .collect::<Vec<_>>();
    for (program, axiom) in entries {
        for (index, node) in axiom["nodes"].as_array().into_iter().flatten().enumerate() {
            for outcome in node["reached"].as_array().into_iter().flatten() {
                if let (Some(slot), Some(outcome)) = (outcomes.get_mut(index), outcome.as_str()) {
                    slot.add(program, outcome);
                }
            }
        }
    }
    outcomes
}

/// A row's `guard` (module documentation of [`crate::coverage`]): the guard outcomes of a
/// sentence with a condition over the comparable programs, each node of its written condition
/// with the outcomes it took where it was reached, and the conjuncts the compile added apart.
/// `entries` are the sentence's entries by comparable programs (`None` when none entered it),
/// `others` its entries by programs that are not comparable, and `skeletons` the record values
/// of the sentence's static skeletons ([`skeleton_values`]), which give the nodes whether or not
/// a program entered the condition, or why the definition's skeleton of it cannot be read: the
/// guard then shows no node, whichever programs entered it, so that the nodes it shows never
/// depend on the programs. The outcomes the programs of `others` saw are listed apart, as
/// `uncounted` (null when none entered it): they count for no outcome of the guard. With
/// `combinations`, a guard that shows the nodes of an authored conjunct also has its comparable
/// programs' valuation combinations in display terms ([`combinations_value`]), which the
/// unique-cause level of the requirements reads.
pub(crate) fn row_guard(
    entries: Option<&SentenceGuards<'_>>,
    others: Option<&SentenceGuards<'_>>,
    skeletons: Result<&[Value], &str>,
    printer: &dyn AtomPrinter,
    combinations: bool,
) -> Value {
    let mut guard = json!({
        "held_by": [], "refuted_by": [], "undefined_by": [], "solver_refuted_by": [],
        "undecided_by": [], "stopped_by": [], "never": ["held", "refuted"],
        "operands": [], "compiled": [], "operands_reason": null, "uncounted": null,
    });
    let entries = sorted(entries);
    let others = sorted(others);
    let outcomes = GuardOutcomes::of(&entries);
    let never = [("held", &outcomes.held), ("refuted", &outcomes.refuted)]
        .into_iter()
        .filter(|(_, programs)| programs.0.is_empty())
        .map(|(name, _)| name)
        .collect::<Vec<_>>();
    guard["held_by"] = json!(outcomes.held.0);
    guard["refuted_by"] = json!(outcomes.refuted.0);
    guard["undefined_by"] = json!(outcomes.undefined.0);
    guard["solver_refuted_by"] = json!(outcomes.solver.0);
    guard["undecided_by"] = outcomes.undecided.value();
    guard["stopped_by"] = json!(outcomes.stopped.0);
    guard["never"] = json!(never);
    let skeletons = match skeletons {
        Ok(skeletons) => skeletons,
        Err(reason) => {
            if !others.is_empty() {
                let other = GuardOutcomes::of(&others);
                guard["uncounted"] = json!({
                    "held_by": other.held.0,
                    "refuted_by": other.refuted.0,
                    "nodes": {},
                });
            }
            guard["operands_reason"] = json!(reason);
            return guard;
        }
    };
    // The skeleton: the static one where the definition gives it, else the first entry's; every
    // axiom of the sentence, entered or not, must have it.
    let Some(first) = skeletons
        .first()
        .or_else(|| entries.first().map(|(_, axiom)| *axiom))
        .or_else(|| others.first().map(|(_, axiom)| *axiom))
    else {
        guard["operands_reason"] = json!("no comparable program entered the condition");
        return guard;
    };
    let nodes = skeleton(first);
    let same = skeletons
        .iter()
        .chain(entries.iter().chain(&others).map(|(_, axiom)| *axiom))
        .all(|axiom| {
            let other = skeleton(axiom);
            other.len() == nodes.len()
                && other
                    .iter()
                    .zip(&nodes)
                    .all(|(a, b)| a.path == b.path && a.shape == b.shape)
        });
    if !same {
        guard["operands_reason"] = json!("the sentence compiles to conditions of different shapes");
        return guard;
    }
    let outcomes = node_outcomes(&entries, nodes.len());
    let uncounted = node_outcomes(&others, nodes.len());
    let mut rendering = Rendering {
        nodes: &nodes,
        printer,
        shown: vec![None; nodes.len()],
        operands: Vec::new(),
    };
    let conjuncts = nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.path.len() == 1)
        .map(|(index, node)| (index, node.path[0]))
        .collect::<Vec<_>>();
    let mut compiled = Vec::new();
    let mut authored = 0usize;
    for (index, conjunct) in &conjuncts {
        let shape = nodes[*index].shape;
        if shape["node"] == "equals" && shape["literal"] == true {
            if let Some(root) = rendering.index(&[*conjunct, 0]) {
                rendering.show(root, conjunct.to_string());
                authored += 1;
            }
        } else {
            let mut value = json!({
                "kind": "compiled",
                "text": match shape["node"].as_str() {
                    Some("predicate" | "term") => printer.print(shape["kore"].as_str().unwrap_or_default()),
                    _ => shape["connective"].as_str().unwrap_or("?").to_owned(),
                },
            });
            outcomes[*index].fill(&mut value, true);
            compiled.push(value);
        }
    }
    let mut operands = rendering.operands;
    let mut uncounted_nodes = serde_json::Map::new();
    for operand in &mut operands {
        let path = operand["path"].as_str().unwrap_or_default().to_owned();
        if let Some(index) = rendering
            .shown
            .iter()
            .position(|shown| shown.as_deref() == Some(path.as_str()))
        {
            let own = own_outcomes(operand["kind"].as_str().unwrap_or_default());
            outcomes[index].fill(operand, own);
            let other = &uncounted[index];
            if !other.true_by.0.is_empty() || !other.false_by.0.is_empty() {
                uncounted_nodes.insert(
                    path,
                    json!({"true_by": other.true_by.0, "false_by": other.false_by.0}),
                );
            }
        }
    }
    guard["operands"] = json!(operands);
    guard["compiled"] = json!(compiled);
    if !others.is_empty() {
        let other = GuardOutcomes::of(&others);
        guard["uncounted"] = json!({
            "held_by": other.held.0,
            "refuted_by": other.refuted.0,
            "nodes": uncounted_nodes,
        });
    }
    if combinations && authored > 0 {
        guard["combinations"] = combinations_value(&nodes, &rendering.shown, &entries);
    }
    if authored == 0 {
        let quantified = conjuncts.iter().any(|(index, _)| {
            nodes[*index].shape["kore"]
                .as_str()
                .is_some_and(|kore| kore.starts_with("\\exists"))
        });
        guard["operands_reason"] = json!(if quantified {
            "the condition binds variables of its own (an existential), so it is one atom"
        } else {
            "the compiled condition has no conjunct of the written requires"
        });
    }
    guard
}

/// The path in the written `requires` (the backend's node path: the conjunct's index, then the
/// operand's index at each level down) of each node a row's guard shows, by its display path,
/// for the skeleton `axiom` (a record value, [`skeleton_values`]): the rendering of
/// [`row_guard`], which shows each `\equals(b, true)` conjunct's `b` at the conjunct's index and
/// reads a left-nested chain of one conjunction or disjunction as one n-ary node.
pub(crate) fn display_paths(axiom: &Value) -> std::collections::BTreeMap<String, Vec<u32>> {
    struct Silent;
    impl AtomPrinter for Silent {
        fn print(&self, _: &str) -> String {
            String::new()
        }
    }
    let nodes = skeleton(axiom);
    let mut rendering = Rendering {
        nodes: &nodes,
        printer: &Silent,
        shown: vec![None; nodes.len()],
        operands: Vec::new(),
    };
    for node in nodes.iter().filter(|node| node.path.len() == 1) {
        let conjunct = node.path[0];
        if node.shape["node"] == "equals"
            && node.shape["literal"] == true
            && let Some(root) = rendering.index(&[conjunct, 0])
        {
            rendering.show(root, conjunct.to_string());
        }
    }
    rendering
        .shown
        .iter()
        .zip(&nodes)
        .filter_map(|(shown, node)| {
            let path = node
                .path
                .iter()
                .map(|step| u32::try_from(*step).ok())
                .collect::<Option<Vec<_>>>()?;
            Some((shown.clone()?, path))
        })
        .collect()
}

/// Whether a combination's guard outcome (a record's token) is a decision: `held`, or a
/// refutation of any kind. An undecided or stopped attempt decided nothing.
#[must_use]
pub fn decided(outcome: &str) -> Option<bool> {
    match outcome {
        "held" => Some(true),
        _ if outcome.starts_with("refuted") => Some(false),
        _ => None,
    }
}

/// The truth of a skeleton's condition (every conjunct, the compile's included) under `atoms`,
/// the two-valued truth of each atom by preorder ordinal, `None` where an atom it reads has
/// none or a node is of no shape it knows. With every atom two-valued, the strict and the
/// short-circuit readings of the Boolean connectives agree, so this is the condition's value.
fn evaluate(nodes: &[Node<'_>], atoms: &[Option<bool>]) -> Option<bool> {
    let ordinal = |index: usize| {
        nodes[..index]
            .iter()
            .filter(|node| matches!(node.shape["node"].as_str(), Some("term" | "predicate")))
            .count()
    };
    let children = |index: usize| {
        let path = &nodes[index].path;
        nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| node.path.len() == path.len() + 1 && node.path.starts_with(path))
            .map(|(child, _)| child)
            .collect::<Vec<_>>()
    };
    fn value(
        nodes: &[Node<'_>],
        index: usize,
        atoms: &[Option<bool>],
        ordinal: &dyn Fn(usize) -> usize,
        children: &dyn Fn(usize) -> Vec<usize>,
    ) -> Option<bool> {
        let shape = nodes[index].shape;
        let operands = || {
            children(index)
                .into_iter()
                .map(|child| value(nodes, child, atoms, ordinal, children))
                .collect::<Option<Vec<_>>>()
        };
        match shape["node"].as_str()? {
            "term" | "predicate" => atoms.get(ordinal(index)).copied().flatten(),
            "equals" => {
                let literal = shape["literal"].as_bool()?;
                match operands()?.as_slice() {
                    [one] => Some(*one == literal),
                    _ => None,
                }
            }
            "connective" => {
                let operands = operands()?;
                match (shape["connective"].as_str()?, operands.as_slice()) {
                    ("notBool" | "\\not", [one]) => Some(!one),
                    ("andBool" | "andThenBool" | "\\and", all) => Some(all.iter().all(|b| *b)),
                    ("orBool" | "orElseBool" | "\\or", any) => Some(any.iter().any(|b| *b)),
                    ("impliesBool" | "\\implies", [a, b]) => Some(!a || *b),
                    ("xorBool", [a, b]) => Some(a != b),
                    ("\\iff", [a, b]) => Some(a == b),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    let mut held = true;
    for (index, node) in nodes.iter().enumerate() {
        if node.path.len() == 1 {
            held &= value(nodes, index, atoms, &ordinal, &children)?;
        }
    }
    Some(held)
}

/// A guard's valuation combinations in display terms (`guard.combinations`): `atoms`, the
/// display path of each atom of the record's combinations in preorder (`null` for an atom of a
/// conjunct the compile added, which no node shows); `rows`, each distinct combination of the
/// comparable programs' `entries` (`truths`, the record's truth of each atom, and `outcome`, the
/// entry's guard outcome) with the `programs` that made it, in corpus order, and `flipped`, for
/// each shown atom, the outcome (`held` or `refuted`) the condition takes under the combination
/// with that atom's two-valued truth negated, null where another atom has no two-valued truth;
/// and `truncated_by`, the programs whose record left a combination out (`combinations_truncated`),
/// since the least ones kept are a function of the full set but not all of it.
fn combinations_value(
    nodes: &[Node<'_>],
    shown: &[Option<String>],
    entries: &[(&str, &Value)],
) -> Value {
    let atoms = nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| matches!(node.shape["node"].as_str(), Some("term" | "predicate")))
        .map(|(index, _)| shown[index].clone())
        .collect::<Vec<_>>();
    let mut rows = std::collections::BTreeMap::<(Vec<String>, String), Programs>::new();
    let mut truncated = Programs::default();
    for (program, axiom) in entries {
        if axiom["combinations_truncated"] == true {
            truncated.add(program);
        }
        for combination in axiom["combinations"].as_array().into_iter().flatten() {
            let truths = combination["atoms"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|truth| truth.as_str().unwrap_or_default().to_owned())
                .collect::<Vec<_>>();
            if truths.len() != atoms.len() {
                continue;
            }
            let outcome = combination["outcome"]
                .as_str()
                .unwrap_or_default()
                .to_owned();
            rows.entry((truths, outcome)).or_default().add(program);
        }
    }
    let two_valued = |truth: &str| match truth {
        TRUE => Some(true),
        FALSE => Some(false),
        _ => None,
    };
    let rows = rows
        .into_iter()
        .map(|((truths, outcome), programs)| {
            let values = truths.iter().map(|t| two_valued(t)).collect::<Vec<_>>();
            let mut flipped = serde_json::Map::new();
            for (ordinal, path) in atoms.iter().enumerate() {
                let Some(path) = path else {
                    continue;
                };
                let mut negated = values.clone();
                negated[ordinal] = values[ordinal].map(|truth| !truth);
                let outcome = evaluate(nodes, &negated).map_or(Value::Null, |held| {
                    json!(if held { "held" } else { "refuted" })
                });
                flipped.insert(path.clone(), outcome);
            }
            json!({"truths": truths, "outcome": outcome, "programs": programs.0,
                   "flipped": flipped})
        })
        .collect::<Vec<_>>();
    json!({"atoms": atoms, "rows": rows, "truncated_by": truncated.0})
}

/// The gaps of `guard`, a row's guard, as a reader reports them: its `never` (of `held` and
/// `refuted`) and the operands that may miss an outcome. Where a front end grouped the guard by
/// its own constructs (`guard.krs`, krs's annotation), those are its `never` and its authored
/// operands (`authored`), the inserted tests and the pattern's templates being listed apart and
/// not counted; else the row's `never` and its operands with outcomes of their own
/// ([`own_outcomes`]). A front end's `never` reads the author's condition alone, so a guard
/// with no authored conjunct has no gap (its `held_by` is `null`, [`authored_condition`]).
#[must_use]
pub fn gaps(guard: &Value) -> (&Value, Vec<&Value>) {
    let named = &guard["krs"];
    if named.is_object() {
        let operands = named["authored"].as_array().into_iter().flatten().collect();
        return (&named["never"], operands);
    }
    let operands = guard["operands"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|operand| operand.get("never").is_some())
        .collect();
    (&guard["never"], operands)
}

fn non_empty(value: &Value) -> bool {
    value.as_array().is_some_and(|items| !items.is_empty())
}

/// Whether `guard`, a row's guard, misses an outcome ([`gaps`]): the guard never held or never
/// refuted, or an operand never `true` or never `false`.
#[must_use]
pub fn misses(guard: &Value) -> bool {
    let (never, operands) = gaps(guard);
    non_empty(never) || operands.iter().any(|operand| non_empty(&operand["never"]))
}

/// Whether `guard`, a row's guard, has a condition a reader reports: every guard but one a front
/// end grouped by its own constructs and found no authored conjunct in (`guard.krs.held_by`
/// `null`: only a pattern's templates or the tests the front end inserted, which refute nothing
/// the author wrote). Which conjuncts are the author's is a fact of the definition, so a front
/// end decides it alike for a guard some program entered and one none did.
#[must_use]
pub fn authored_condition(guard: &Value) -> bool {
    let named = &guard["krs"];
    !named.is_object() || !named["held_by"].is_null()
}

/// The summary's `guards` of `rules`, a document's rows ([`gaps`]): the sentences with a guard
/// that has a condition a reader reports ([`authored_condition`]), those never held and never
/// refuted, and the operands that miss an outcome. A front end that groups guards by its own
/// constructs computes it again over its annotated rows, so that the count is of the operands
/// its rows report.
#[must_use]
pub fn summary(rules: &[Value]) -> Value {
    let gaps = rules
        .iter()
        .filter_map(|rule| rule.get("guard"))
        .filter(|guard| authored_condition(guard))
        .map(gaps)
        .collect::<Vec<_>>();
    let never = |outcome: &str| {
        gaps.iter()
            .filter(|(never, _)| {
                never
                    .as_array()
                    .is_some_and(|never| never.iter().any(|item| item == outcome))
            })
            .count()
    };
    let operands = gaps
        .iter()
        .flat_map(|(_, operands)| operands)
        .filter(|operand| non_empty(&operand["never"]))
        .count();
    json!({
        "sentences": gaps.len(),
        "never_held": never("held"),
        "never_refuted": never("refuted"),
        "operands_missing_an_outcome": operands,
    })
}

/// Whether `requires`, a sentence's K condition, is no condition: the token `true`.
pub(crate) fn unconditional(requires: &k_rust::kast::Term) -> bool {
    use k_rust::kast::Term;
    match requires {
        Term::Annotated { term, .. } => unconditional(term),
        Term::Token { token, .. } => token == "true",
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Prints an atom's KORE text as it is.
    struct Verbatim;

    impl AtomPrinter for Verbatim {
        fn print(&self, kore: &str) -> String {
            kore.to_owned()
        }
    }

    fn node(path: &[u64], shape: Value, reached: &[&str]) -> Value {
        json!({"path": path, "shape": shape, "reached": reached})
    }

    fn atom(text: &str) -> Value {
        json!({"node": "term", "kore": text})
    }

    fn connective(name: &str) -> Value {
        json!({"node": "connective", "connective": name})
    }

    fn equals() -> Value {
        json!({"node": "equals", "literal": true})
    }

    /// `(A andBool B) andBool C` under `\equals(_, true)`: one entry with A true and B false.
    fn chain(axiom: &str, reached_b: &[&str]) -> Value {
        json!({
            "axiom": axiom,
            "nodes": [
                node(&[0], equals(), &["false"]),
                node(&[0, 0], connective("andBool"), &["false"]),
                node(&[0, 0, 0], connective("andBool"), &["false"]),
                node(&[0, 0, 0, 0], atom("A"), &["true"]),
                node(&[0, 0, 0, 1], atom("B"), reached_b),
                node(&[0, 0, 1], atom("C"), &[]),
            ],
            "outcomes": ["refuted-false"],
            "combinations": [],
            "combinations_truncated": false,
        })
    }

    /// A left-nested chain of one connective is one n-ary node whose paths index its operands
    /// in written order; an operand that was never reached has no outcome and misses both.
    #[test]
    fn a_left_nested_chain_is_one_node() {
        let record = json!({"coverage": {"guards": [
            {"module": "M", "index": 0, "axioms": [chain("a", &["false"])]},
        ]}});
        let guards = SentenceGuards::of([("p", &record)]);
        let guard = row_guard(
            guards.get(&("M".to_owned(), 0)),
            None,
            Ok(&[]),
            &Verbatim,
            false,
        );
        let operands = guard["operands"].as_array().unwrap();
        let paths = operands
            .iter()
            .map(|operand| operand["path"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(paths, ["0", "0.0", "0.1", "0.2"]);
        assert_eq!(operands[0]["operands"], json!(["0.0", "0.1", "0.2"]));
        assert_eq!(operands[0]["text"], "A andBool B andBool C");
        // The conjunction's outcomes restate its operands': it carries no gap of its own.
        assert!(operands[0].get("never").is_none(), "{guard:#}");
        assert_eq!(operands[0]["false_by"], json!(["p"]));
        assert_eq!(operands[1]["true_by"], json!(["p"]));
        assert_eq!(operands[2]["false_by"], json!(["p"]));
        assert_eq!(operands[3]["never"], json!(["true", "false"]));
        assert_eq!(guard["refuted_by"], json!(["p"]));
        assert_eq!(guard["never"], json!(["held"]));
        assert!(misses(&guard));
        assert_eq!(guard["operands_reason"], Value::Null);
    }

    /// The definition's skeleton gives a guard no comparable program entered its nodes, each with
    /// no outcome; a program that is not comparable is listed apart, as `uncounted`, and counts
    /// for no outcome.
    #[test]
    fn a_skeleton_names_the_nodes_of_an_unentered_guard() {
        let mut skeleton = chain("a", &[]);
        for node in skeleton["nodes"].as_array_mut().unwrap() {
            node["reached"] = json!([]);
        }
        skeleton["outcomes"] = json!([]);
        let unknown = json!({"coverage": {"guards": [
            {"module": "M", "index": 0, "axioms": [chain("a", &["false"])]},
        ]}});
        let others = SentenceGuards::of([("u", &unknown)]);
        let guard = row_guard(
            None,
            others.get(&("M".to_owned(), 0)),
            Ok(&[skeleton]),
            &Verbatim,
            false,
        );
        let operands = guard["operands"].as_array().unwrap();
        assert_eq!(operands.len(), 4, "{guard:#}");
        assert_eq!(operands[1]["never"], json!(["true", "false"]));
        assert_eq!(guard["never"], json!(["held", "refuted"]));
        assert_eq!(guard["refuted_by"], json!([]));
        assert_eq!(guard["operands_reason"], Value::Null);
        assert_eq!(guard["uncounted"]["refuted_by"], json!(["u"]));
        assert_eq!(guard["uncounted"]["nodes"]["0.0"]["true_by"], json!(["u"]));
        assert_eq!(guard["uncounted"]["nodes"]["0.1"]["false_by"], json!(["u"]));
    }

    /// Two axioms of one sentence whose skeletons differ give no operands, with the reason; a
    /// sentence no program entered has the reason too; a condition that is one existential is
    /// one compiled conjunct, with the reason.
    #[test]
    fn operands_reasons() {
        let mut other = chain("b", &["false"]);
        other["nodes"][5]["shape"] = atom("D");
        let record = json!({"coverage": {"guards": [
            {"module": "M", "index": 0, "axioms": [chain("a", &["false"]), other]},
        ]}});
        let guards = SentenceGuards::of([("p", &record)]);
        let differing = row_guard(
            guards.get(&("M".to_owned(), 0)),
            None,
            Ok(&[]),
            &Verbatim,
            false,
        );
        assert_eq!(differing["operands"], json!([]));
        assert_eq!(
            differing["operands_reason"],
            "the sentence compiles to conditions of different shapes"
        );
        let unentered = row_guard(None, None, Ok(&[]), &Verbatim, false);
        assert_eq!(
            unentered["operands_reason"],
            "no comparable program entered the condition"
        );
        assert_eq!(unentered["never"], json!(["held", "refuted"]));
        // A skeleton the definition cannot give: no node, although a program entered it, so the
        // nodes a guard shows never depend on which programs entered it.
        let unreadable = row_guard(
            guards.get(&("M".to_owned(), 0)),
            None,
            Err("the skeleton cannot be read"),
            &Verbatim,
            false,
        );
        assert_eq!(unreadable["operands"], json!([]));
        assert_eq!(unreadable["operands_reason"], "the skeleton cannot be read");
        assert_eq!(unreadable["refuted_by"], json!(["p"]));
        let quantified = json!({"coverage": {"guards": [{"module": "M", "index": 1, "axioms": [{
            "axiom": "q",
            "nodes": [node(&[0], json!({"node": "predicate", "kore": "\\exists{R}(X, P)"}), &["true"])],
            "outcomes": ["held"], "combinations": [], "combinations_truncated": false,
        }]}]}});
        let guards = SentenceGuards::of([("p", &quantified)]);
        let guard = row_guard(
            guards.get(&("M".to_owned(), 1)),
            None,
            Ok(&[]),
            &Verbatim,
            false,
        );
        assert_eq!(guard["compiled"][0]["true_by"], json!(["p"]));
        assert!(
            guard["operands_reason"]
                .as_str()
                .unwrap()
                .contains("existential"),
            "{guard:#}"
        );
    }
}
