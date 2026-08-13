//! Complete configuration abstractions into fixed-arity cell applications.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::{
    definition::{
        Definition, LabelHead, ModuleId, ProductionCatalog, ProductionItem, ResolvedDefinition,
        Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
};

const MACRO_ATTRIBUTES: &[&str] = &["macro", "macro-rec", "alias", "alias-rec"];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConcretizeCellsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ConcretizeCellsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "cell concretization produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ConcretizeCellsError {}

/// Apply Java's `ConcretizeCells` definition transformation.
pub fn concretize_cells(definition: &Definition) -> Result<Definition, ConcretizeCellsError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(|error| ConcretizeCellsError {
            diagnostics: vec![plain_error(error.to_string())],
        })?;
    let main_id = resolved.main_module_id();
    let model = CellModel::new(&resolved, main_id).map_err(|message| ConcretizeCellsError {
        diagnostics: vec![plain_error(message)],
    })?;
    if model.cells.is_empty() {
        return Ok(definition.clone());
    }

    let mut output = definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            let original = sentence.clone();
            match Concretizer::new(&model, &productions).sentence(original) {
                Ok(transformed) => *sentence = transformed,
                Err(message) => diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidCellConcretization,
                    message,
                    sentence,
                )),
            }
        }
    }
    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ConcretizeCellsError { diagnostics })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Multiplicity {
    One,
    Optional,
    Star,
}

#[derive(Clone, Debug)]
struct Child {
    sort: Sort,
    multiplicity: Multiplicity,
    value_sort: Sort,
    unit: Option<Label>,
    concat: Option<Label>,
    default: Option<Label>,
}

#[derive(Clone, Debug)]
struct Cell {
    label: Label,
    sort: Sort,
    children: Vec<Child>,
    leaf_sort: Option<Sort>,
}

struct CellModel {
    cells: BTreeMap<Sort, Cell>,
    by_label: BTreeMap<LabelHead, Sort>,
    cell_term_sort: BTreeMap<LabelHead, Sort>,
    collection_member: BTreeMap<LabelHead, Sort>,
    parents: BTreeMap<Sort, Sort>,
    levels: BTreeMap<Sort, usize>,
    root: Sort,
    close_operators: BTreeMap<Sort, (Label, bool, bool)>,
}

impl CellModel {
    fn new(definition: &ResolvedDefinition, module: ModuleId) -> Result<Self, String> {
        let productions = definition.production_catalog(module);
        let subsorts = definition
            .subsorts(module)
            .map_err(|error| error.to_string())?;
        let raw_cells = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    items,
                    attributes,
                    ..
                } if attributes.get("cell").is_some() && attributes.get("internal").is_none() => {
                    Some((
                        sort.clone(),
                        label.clone(),
                        items.clone(),
                        attributes.clone(),
                    ))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        if raw_cells.is_empty() {
            return Ok(Self {
                cells: BTreeMap::new(),
                by_label: BTreeMap::new(),
                cell_term_sort: BTreeMap::new(),
                collection_member: BTreeMap::new(),
                parents: BTreeMap::new(),
                levels: BTreeMap::new(),
                root: Sort::new("GeneratedTopCell"),
                close_operators: BTreeMap::new(),
            });
        }
        let cell_sorts = raw_cells
            .iter()
            .map(|(sort, ..)| sort.clone())
            .collect::<BTreeSet<_>>();
        let cell_attributes = raw_cells
            .iter()
            .map(|(sort, _, _, attributes)| (sort.clone(), attributes.clone()))
            .collect::<BTreeMap<_, _>>();
        let collections = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label,
                    sort,
                    attributes,
                    ..
                } if attributes.get("cellCollection").is_some() => Some((
                    sort.clone(),
                    label.clone(),
                    attributes.get_str("unit").map(Label::new),
                )),
                _ => None,
            })
            .collect::<Vec<_>>();
        let initializers = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    items,
                    attributes,
                    ..
                } if attributes.get("initializer").is_some()
                    && items
                        .iter()
                        .all(|item| !matches!(item, ProductionItem::NonTerminal { .. })) =>
                {
                    Some((sort.clone(), label.clone()))
                }
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();

        let mut cells = BTreeMap::new();
        let mut by_label = BTreeMap::new();
        let mut collection_member = BTreeMap::new();
        for (sort, label, items, _attributes) in raw_cells {
            if cells.contains_key(&sort) {
                return Err(format!("Too many productions for cell sort: {sort}"));
            }
            let mut children = Vec::new();
            let nonterminals = items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                _ => None,
            });
            for child_sort in nonterminals {
                if cell_sorts.contains(&child_sort) {
                    let child_attributes = &cell_attributes[&child_sort];
                    let multiplicity = if child_attributes.get_str("unit").is_some() {
                        Multiplicity::Optional
                    } else {
                        Multiplicity::One
                    };
                    children.push(Child {
                        sort: child_sort.clone(),
                        multiplicity,
                        value_sort: child_sort.clone(),
                        unit: child_attributes.get_str("unit").map(Label::new),
                        concat: None,
                        default: initializers.get(&child_sort).cloned(),
                    });
                    continue;
                }
                if let Some((collection_sort, concat, unit)) = collections
                    .iter()
                    .find(|(collection_sort, ..)| collection_sort == &child_sort)
                {
                    let mut members = cell_sorts
                        .iter()
                        .filter(|cell| subsorts.directly_less_than(cell, collection_sort))
                        .cloned()
                        .collect::<Vec<_>>();
                    members.sort();
                    for member in members {
                        children.push(Child {
                            sort: member.clone(),
                            multiplicity: Multiplicity::Star,
                            value_sort: collection_sort.clone(),
                            unit: unit.clone(),
                            concat: concat.clone(),
                            default: initializers.get(collection_sort).cloned(),
                        });
                        if let Some(label) = concat {
                            collection_member.insert(LabelHead::from(label), member.clone());
                        }
                        if let Some(label) = unit {
                            collection_member.insert(LabelHead::from(label), member.clone());
                        }
                    }
                }
            }
            let leaf_sort = if children.is_empty() {
                items.iter().find_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                    _ => None,
                })
            } else {
                None
            };
            by_label.insert(LabelHead::from(&label), sort.clone());
            cells.insert(
                sort.clone(),
                Cell {
                    label,
                    sort,
                    children,
                    leaf_sort,
                },
            );
        }

        let mut parents = BTreeMap::new();
        for (parent_sort, cell) in &cells {
            for child in &cell.children {
                if let Some(previous) = parents.insert(child.sort.clone(), parent_sort.clone())
                    && previous != *parent_sort
                {
                    return Err(format!(
                        "Cell sort {} has multiple parents: {previous} and {parent_sort}",
                        child.sort
                    ));
                }
            }
        }
        let roots = cells
            .keys()
            .filter(|sort| !parents.contains_key(*sort))
            .cloned()
            .collect::<Vec<_>>();
        let root = match roots.as_slice() {
            [root] => root.clone(),
            [] => return Err("No root cell found".into()),
            _ => {
                return Err(format!(
                    "Too many top cells: {}",
                    roots
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        };
        let mut levels = BTreeMap::new();
        levels.insert(root.clone(), 0);
        let mut changed = true;
        while changed {
            changed = false;
            for (child, parent) in &parents {
                if let Some(level) = levels.get(parent).copied()
                    && levels.insert(child.clone(), level + 1) != Some(level + 1)
                {
                    changed = true;
                }
            }
        }

        let mut close_operators = BTreeMap::new();
        let cell_term_sort = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    ..
                } if cell_sorts.contains(sort) => Some((LabelHead::from(label), sort.clone())),
                _ => None,
            })
            .collect();
        for (_, production) in productions.productions() {
            let Sentence::Production {
                label: Some(label),
                sort,
                items,
                attributes,
                ..
            } = production
            else {
                continue;
            };
            if attributes.get("assoc").is_none()
                || items
                    .iter()
                    .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                    .count()
                    != 2
            {
                continue;
            }
            close_operators.entry(sort.clone()).or_insert((
                label.clone(),
                true,
                attributes.get("comm").is_some(),
            ));
        }
        Ok(Self {
            cells,
            by_label,
            cell_term_sort,
            collection_member,
            parents,
            levels,
            root,
            close_operators,
        })
    }

    fn cell_for_label(&self, label: &Label) -> Option<&Cell> {
        self.by_label
            .get(&LabelHead::from(label))
            .and_then(|sort| self.cells.get(sort))
    }

    fn sort_for_term(&self, term: &Term) -> Option<Sort> {
        match term.unannotated() {
            Term::Apply { label, .. } => self
                .cell_term_sort
                .get(&LabelHead::from(label))
                .or_else(|| self.collection_member.get(&LabelHead::from(label)))
                .cloned(),
            Term::Variable { sort, .. } => sort
                .clone()
                .or_else(|| term.metadata().and_then(|metadata| metadata.sort.clone()))
                .filter(|sort| self.cells.contains_key(sort)),
            Term::Rewrite { left, right } => {
                let left = self.sort_for_side(left);
                let right = self.sort_for_side(right);
                if left == right { left } else { None }
            }
            _ => None,
        }
    }

    fn sort_for_side(&self, term: &Term) -> Option<Sort> {
        let mut sorts = flatten_cells(term)
            .into_iter()
            .filter_map(|term| self.sort_for_term(term))
            .collect::<BTreeSet<_>>();
        if sorts.len() == 1 {
            sorts.pop_first()
        } else {
            None
        }
    }
}

struct Concretizer<'a> {
    model: &'a CellModel,
    productions: &'a ProductionCatalog<'a>,
    variables: BTreeSet<String>,
    fragments: BTreeMap<String, FragmentInfo>,
    counter: usize,
}

#[derive(Clone)]
struct FragmentInfo {
    parent: Sort,
    candidates: BTreeSet<Sort>,
    split: BTreeMap<Sort, Term>,
}

impl<'a> Concretizer<'a> {
    fn new(model: &'a CellModel, productions: &'a ProductionCatalog<'a>) -> Self {
        Self {
            model,
            productions,
            variables: BTreeSet::new(),
            fragments: BTreeMap::new(),
            counter: 0,
        }
    }

    fn sentence(&mut self, sentence: Sentence) -> Result<Sentence, String> {
        if matches!(&sentence, Sentence::Claim { body, .. } if !contains_cell(body, self.model)) {
            return Ok(sentence);
        }
        if skip_sentence(&sentence) {
            return Ok(sentence);
        }
        self.variables.clear();
        self.fragments.clear();
        self.counter = 0;
        for root in sentence_roots(&sentence) {
            root.visit_preorder(&mut |term| {
                if let Term::Variable { name, .. } = term.unannotated() {
                    self.variables.insert(name.clone());
                }
            });
        }
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.concretize_body(body)?;
                self.analyze_fragments([&body, &requires, &ensures])?;
                Ok(Sentence::Rule {
                    body: self.sort_cells(body)?,
                    requires: self.sort_cells(requires)?,
                    ensures: self.sort_cells(ensures)?,
                    attributes,
                })
            }
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.concretize_body(body)?;
                self.analyze_fragments([&body, &requires, &ensures])?;
                Ok(Sentence::Claim {
                    body: self.sort_cells(body)?,
                    requires: self.sort_cells(requires)?,
                    ensures: self.sort_cells(ensures)?,
                    attributes,
                })
            }
            Sentence::Context {
                body,
                requires,
                attributes,
            } => {
                let body = self.concretize_body(body)?;
                self.analyze_fragments([&body, &requires])?;
                Ok(Sentence::Context {
                    body: self.sort_cells(body)?,
                    requires: self.sort_cells(requires)?,
                    attributes,
                })
            }
            sentence => Ok(sentence),
        }
    }

    fn concretize_body(&mut self, body: Term) -> Result<Term, String> {
        let body = if is_function(&body, self.productions) {
            body
        } else {
            self.add_root(body)?
        };
        let body = self.add_parents(body)?;
        self.close(body, false)
    }

    fn analyze_fragments<'b>(
        &mut self,
        roots: impl IntoIterator<Item = &'b Term>,
    ) -> Result<(), String> {
        let mut observations = Vec::<(String, Sort, BTreeSet<Sort>)>::new();
        for root in roots {
            collect_fragment_observations(root, self.model, &mut observations);
        }
        for (name, parent, candidates) in observations {
            let entry = self.fragments.entry(name.clone()).or_insert(FragmentInfo {
                parent: parent.clone(),
                candidates: candidates.clone(),
                split: BTreeMap::new(),
            });
            if entry.parent != parent {
                return Err(format!(
                    "Cell variable {name} is used under two cells: {} and {parent}",
                    entry.parent
                ));
            }
            entry.candidates = entry
                .candidates
                .intersection(&candidates)
                .cloned()
                .collect();
        }
        let pending = self
            .fragments
            .iter()
            .map(|(name, info)| (name.clone(), info.candidates.clone()))
            .collect::<Vec<_>>();
        for (name, candidates) in pending {
            let mut split = BTreeMap::new();
            for sort in candidates {
                let child = self
                    .model
                    .cells
                    .get(&self.fragments[&name].parent)
                    .and_then(|cell| cell.children.iter().find(|child| child.sort == sort))
                    .expect("fragment candidates are parent children");
                let term = if self.fragments[&name].candidates.len() == 1 {
                    Term::Variable {
                        name: name.clone(),
                        sort: Some(child.value_sort.clone()),
                    }
                } else {
                    self.fresh_variable(Some(child.value_sort.clone()), "_CellFragment")
                };
                split.insert(sort, term);
            }
            self.fragments.get_mut(&name).unwrap().split = split;
        }
        Ok(())
    }

    fn add_root(&self, term: Term) -> Result<Term, String> {
        let root = self
            .model
            .cells
            .get(&self.model.root)
            .ok_or_else(|| "No root cell found".to_owned())?;
        if matches!(term.unannotated(), Term::Apply { label, .. } if label.name == root.label.name)
        {
            return Ok(term);
        }
        if let Term::Rewrite { left, right: _ } = term.unannotated() {
            let wrapped_left = self.add_root((**left).clone())?;
            if wrapped_left == **left {
                return Ok(term);
            }
            return Ok(incomplete_cell(&root.label, true, term, true));
        }
        Ok(incomplete_cell(&root.label, true, term, true))
    }

    fn add_parents(&self, term: Term) -> Result<Term, String> {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated() {
            Term::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.add_parents(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let application = Term::Apply {
                    label: label.clone(),
                    arguments,
                };
                if let Some(cell) = self.model.cell_for_label(&label)
                    && !cell.children.is_empty()
                {
                    self.complete_parent(application, cell)?
                } else {
                    application
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.add_parents(*left)?),
                right: Box::new(self.add_parents(*right)?),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.add_parents(*pattern)?),
                alias: Box::new(self.add_parents(*alias)?),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.add_parents(item))
                    .collect::<Result<_, _>>()?,
            ),
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!(),
        };
        Ok(with_metadata(rebuilt, metadata))
    }

    fn complete_parent(&self, application: Term, cell: &Cell) -> Result<Term, String> {
        let Term::Apply { label, arguments } = application.unannotated() else {
            unreachable!()
        };
        let (open_left, contents, open_right) = incomplete_parts(arguments)?;
        let mut completion = Vec::new();
        let mut others = Vec::new();
        for item in flatten_cells(contents) {
            if self.model.sort_for_term(item).is_some() {
                completion.push(item.clone());
            } else {
                others.push(item.clone());
            }
        }
        let target_level = self.model.levels[&cell.sort] + 1;
        while completion.iter().any(|item| {
            self.model
                .sort_for_term(item)
                .and_then(|sort| self.model.levels.get(&sort).copied())
                .is_some_and(|level| level > target_level)
        }) {
            let deepest = completion
                .iter()
                .filter_map(|item| {
                    self.model
                        .sort_for_term(item)
                        .and_then(|sort| self.model.levels.get(&sort).copied())
                })
                .max()
                .expect("completion terms have levels");
            let mut grouped = BTreeMap::<Sort, Vec<Term>>::new();
            let mut retained = Vec::new();
            for item in completion {
                let Some(sort) = self.model.sort_for_term(&item) else {
                    retained.push(item);
                    continue;
                };
                if self.model.levels[&sort] == deepest {
                    let parent = self.model.parents.get(&sort).ok_or_else(|| {
                        format!("Cell sort {sort} has no parent during completion")
                    })?;
                    grouped.entry(parent.clone()).or_default().push(item);
                } else {
                    retained.push(item);
                }
            }
            for (parent, items) in grouped {
                let parent = &self.model.cells[&parent];
                retained.push(incomplete_cell(
                    &parent.label,
                    open_left || open_right,
                    make_body(items),
                    open_left || open_right,
                ));
            }
            completion = retained;
        }
        others.extend(completion);
        Ok(Term::Apply {
            label: label.clone(),
            arguments: vec![dot(open_left), make_body(others), dot(open_right)],
        })
    }

    fn close(&mut self, term: Term, on_rhs: bool) -> Result<Term, String> {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated() {
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.close(*left, false)?),
                right: Box::new(self.close(*right, true)?),
            },
            Term::Apply { label, arguments } => {
                let application = Term::Apply {
                    label: label.clone(),
                    arguments,
                };
                if let Some(cell) = self.model.cell_for_label(&label) {
                    self.close_cell(application, cell, on_rhs)?
                } else {
                    let Term::Apply { label, arguments } = application else {
                        unreachable!()
                    };
                    Term::Apply {
                        label,
                        arguments: arguments
                            .into_iter()
                            .map(|argument| self.close(argument, on_rhs))
                            .collect::<Result<_, _>>()?,
                    }
                }
            }
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.close(*pattern, on_rhs)?),
                alias: Box::new(self.close(*alias, on_rhs)?),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.close(item, on_rhs))
                    .collect::<Result<_, _>>()?,
            ),
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!(),
        };
        Ok(with_metadata(rebuilt, metadata))
    }

    fn close_cell(&mut self, application: Term, cell: &Cell, on_rhs: bool) -> Result<Term, String> {
        let Term::Apply { label, arguments } = application else {
            unreachable!()
        };
        let (open_left, body, open_right) = incomplete_parts(&arguments)?;
        let contents = flatten_cells(body)
            .into_iter()
            .cloned()
            .map(|item| self.close(item, on_rhs))
            .collect::<Result<Vec<_>, _>>()?;
        if !cell.children.is_empty() {
            let required = |side_right: bool| {
                let mut required = cell
                    .children
                    .iter()
                    .filter(|child| child.multiplicity == Multiplicity::One)
                    .map(|child| child.sort.clone())
                    .collect::<BTreeSet<_>>();
                for item in &contents {
                    let side = match item.unannotated() {
                        Term::Rewrite { left, right } => {
                            if side_right {
                                right.as_ref()
                            } else {
                                left.as_ref()
                            }
                        }
                        _ => item,
                    };
                    for term in flatten_cells(side) {
                        if let Some(sort) = self.model.sort_for_term(term) {
                            required.remove(&sort);
                        } else if matches!(term.unannotated(), Term::Variable { .. }) {
                            required.clear();
                        }
                    }
                }
                required
            };
            let required_left = required(false);
            let required_right = required(true);
            if !open_left
                && !open_right
                && (!required_left.is_empty() || !required_right.is_empty())
            {
                return Err(format!(
                    "Closed parent cell {} missing required children {:?} on the left and {:?} on the right",
                    label.name, required_left, required_right
                ));
            }
            let mut contents = contents;
            if open_left || open_right {
                if on_rhs {
                    for sort in required_left {
                        let child = cell
                            .children
                            .iter()
                            .find(|child| child.sort == sort)
                            .unwrap();
                        let default = child.default.as_ref().ok_or_else(|| {
                            format!(
                                "Cannot close cell on right hand side because the initializer for {} is unavailable",
                                child.sort
                            )
                        })?;
                        contents.push(Term::Apply {
                            label: default.clone(),
                            arguments: Vec::new(),
                        });
                    }
                } else {
                    contents.push(self.fresh_variable(None, "_DotVar"));
                }
            }
            return Ok(Term::Apply {
                label,
                arguments: contents,
            });
        }

        if contents.len() != 1 {
            return Err(format!(
                "Leaf cells should contain exactly 1 body term, but {} contains {}",
                label.name,
                contents.len()
            ));
        }
        let mut body = contents.into_iter().next().unwrap();
        if !open_left && !open_right {
            return Ok(Term::Apply {
                label,
                arguments: vec![body],
            });
        }
        if on_rhs {
            return Err(format!(
                "Leaf cell {} on the right hand side of a rewrite may not be open",
                label.name
            ));
        }
        let cell_sort = cell.leaf_sort.clone().unwrap_or_else(|| Sort::new("K"));
        if cell_sort.name == "K" {
            let mut items = Vec::new();
            if open_left {
                items.push(self.fresh_variable(Some(cell_sort.clone()), "_DotVar"));
            }
            match body.unannotated() {
                Term::Sequence(sequence) => items.extend(sequence.clone()),
                _ => items.push(body),
            }
            if open_right {
                items.push(self.fresh_variable(Some(cell_sort), "_DotVar"));
            }
            body = Term::Sequence(items);
        } else {
            let (operator, associative, commutative) = self
                .model
                .close_operators
                .get(&cell_sort)
                .cloned()
                .ok_or_else(|| {
                    format!("No operator registered for closing cells of sort {cell_sort}")
                })?;
            if !associative && open_left && open_right {
                return Err(format!(
                    "Ambiguity closing cell {}: operator {} is not associative",
                    label.name, operator.name
                ));
            }
            let (open_left, open_right) = if commutative {
                (false, open_left || open_right)
            } else {
                (open_left, open_right)
            };
            if open_right {
                body = Term::apply(
                    operator.name.clone(),
                    vec![
                        body,
                        self.fresh_variable(Some(cell_sort.clone()), "_DotVar"),
                    ],
                );
            }
            if open_left {
                body = Term::apply(
                    operator.name,
                    vec![self.fresh_variable(Some(cell_sort), "_DotVar"), body],
                );
            }
        }
        Ok(Term::Apply {
            label,
            arguments: vec![body],
        })
    }

    fn sort_cells(&mut self, term: Term) -> Result<Term, String> {
        self.sort_cells_with_fragments(term, true)
    }

    fn sort_cells_with_fragments(
        &mut self,
        term: Term,
        replace_fragments: bool,
    ) -> Result<Term, String> {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated() {
            Term::Apply { label, arguments } => {
                if let [argument] = arguments.as_slice()
                    && let Term::Variable { name, .. } = argument.unannotated()
                    && let Some(info) = self.fragments.get(name)
                    && (label.name == format!("is{}Fragment", info.parent) || label.name == "isBag")
                {
                    fragment_predicate(info, self.model)
                } else if let Some(cell) = self.model.cell_for_label(&label)
                    && !cell.children.is_empty()
                {
                    let ordered = self.order_children(label, arguments, cell)?;
                    let Term::Apply { label, arguments } = ordered else {
                        unreachable!()
                    };
                    Term::Apply {
                        label,
                        arguments: arguments
                            .into_iter()
                            .map(|argument| self.sort_cells_with_fragments(argument, false))
                            .collect::<Result<_, _>>()?,
                    }
                } else {
                    Term::Apply {
                        label,
                        arguments: arguments
                            .into_iter()
                            .map(|argument| {
                                self.sort_cells_with_fragments(argument, replace_fragments)
                            })
                            .collect::<Result<_, _>>()?,
                    }
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.sort_cells_with_fragments(*left, replace_fragments)?),
                right: Box::new(self.sort_cells_with_fragments(*right, replace_fragments)?),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.sort_cells_with_fragments(*pattern, replace_fragments)?),
                alias: Box::new(self.sort_cells_with_fragments(*alias, replace_fragments)?),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.sort_cells_with_fragments(item, replace_fragments))
                    .collect::<Result<_, _>>()?,
            ),
            Term::Variable { name, sort } => {
                if replace_fragments {
                    self.fragments.get(&name).map_or_else(
                        || Ok(Term::Variable { name, sort }),
                        |info| fragment_replacement(info, self.model),
                    )?
                } else {
                    Term::Variable { name, sort }
                }
            }
            leaf @ (Term::InjectedLabel(_) | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!(),
        };
        Ok(with_metadata(rebuilt, metadata))
    }

    fn order_children(
        &mut self,
        label: Label,
        arguments: Vec<Term>,
        cell: &Cell,
    ) -> Result<Term, String> {
        let mut ordered = BTreeMap::<Sort, Term>::new();
        let mut unknown = Vec::new();
        for item in arguments {
            if let Some(sort) = self.model.sort_for_term(&item) {
                self.insert_child(&mut ordered, sort, item, cell)?;
            } else if matches!(item.unannotated(), Term::Variable { .. }) {
                unknown.push(item);
            } else if let Term::Rewrite { left, right } = item.unannotated() {
                let left = split_side(left, self.model);
                let right = split_side(right, self.model);
                let sorts = left
                    .keys()
                    .chain(right.keys())
                    .cloned()
                    .collect::<BTreeSet<_>>();
                for sort in sorts {
                    let child = cell
                        .children
                        .iter()
                        .find(|child| child.sort == sort)
                        .ok_or_else(|| format!("Unexpected child sort {sort} in {}", label.name))?;
                    let left = left
                        .get(&sort)
                        .cloned()
                        .or_else(|| unit(child))
                        .ok_or_else(|| format!("Cannot rewrite required cell {sort} from unit"))?;
                    let right = right
                        .get(&sort)
                        .cloned()
                        .or_else(|| unit(child))
                        .ok_or_else(|| format!("Cannot rewrite required cell {sort} to unit"))?;
                    self.insert_child(
                        &mut ordered,
                        sort,
                        Term::Rewrite {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                        cell,
                    )?;
                }
            } else {
                return Err(format!(
                    "Unexpected term in parent cell {} during child ordering",
                    label.name
                ));
            }
        }
        for variable in unknown {
            let variable_name = match variable.unannotated() {
                Term::Variable { name, .. } => name,
                _ => unreachable!(),
            };
            if let Some(info) = self.fragments.get(variable_name) {
                for (sort, split) in info.split.clone() {
                    self.insert_child(&mut ordered, sort, split, cell)?;
                }
                continue;
            }
            let candidates = cell
                .children
                .iter()
                .filter(|child| {
                    child.multiplicity == Multiplicity::Star || !ordered.contains_key(&child.sort)
                })
                .collect::<Vec<_>>();
            match candidates.as_slice() {
                [] => {}
                [child] => {
                    let variable = set_variable_sort(variable, child.value_sort.clone());
                    self.insert_child(&mut ordered, child.sort.clone(), variable, cell)?;
                }
                _ => {
                    return Err(format!(
                        "Cell fragment variable is ambiguous under {} across child sorts {}",
                        label.name,
                        candidates
                            .iter()
                            .map(|child| child.sort.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
        }
        let mut result = Vec::with_capacity(cell.children.len());
        for child in &cell.children {
            if let Some(term) = ordered.remove(&child.sort) {
                result.push(term);
            } else if let Some(unit) = unit(child) {
                result.push(unit);
            } else {
                return Err(format!(
                    "Missing cell of multiplicity=\"1\": {}",
                    child.sort
                ));
            }
        }
        Ok(Term::Apply {
            label,
            arguments: result,
        })
    }

    fn insert_child(
        &self,
        ordered: &mut BTreeMap<Sort, Term>,
        sort: Sort,
        item: Term,
        cell: &Cell,
    ) -> Result<(), String> {
        let child = cell
            .children
            .iter()
            .find(|child| child.sort == sort)
            .ok_or_else(|| format!("Unexpected child sort {sort} in {}", cell.label.name))?;
        if let Some(previous) = ordered.remove(&sort) {
            if child.multiplicity != Multiplicity::Star {
                return Err(format!(
                    "Attempting to concatenate cells not of multiplicity=\"*\": {sort}"
                ));
            }
            let concat = child
                .concat
                .as_ref()
                .ok_or_else(|| format!("No concatenation label for repeated cell {sort}"))?;
            ordered.insert(
                sort,
                Term::Apply {
                    label: concat.clone(),
                    arguments: vec![previous, item],
                },
            );
        } else {
            ordered.insert(sort, item);
        }
        Ok(())
    }

    fn fresh_variable(&mut self, sort: Option<Sort>, prefix: &str) -> Term {
        let name = loop {
            let name = format!("{prefix}{}", self.counter);
            self.counter += 1;
            if self.variables.insert(name.clone()) {
                break name;
            }
        };
        Term::Variable { name, sort }
    }
}

fn collect_fragment_observations(
    term: &Term,
    model: &CellModel,
    observations: &mut Vec<(String, Sort, BTreeSet<Sort>)>,
) {
    match term.unannotated() {
        Term::Apply { label, arguments } => {
            if let Some(parent) = model.cell_for_label(label)
                && !parent.children.is_empty()
            {
                let occupied = arguments
                    .iter()
                    .flat_map(flatten_cells)
                    .filter_map(|item| model.sort_for_term(item))
                    .filter(|sort| {
                        parent
                            .children
                            .iter()
                            .find(|child| child.sort == *sort)
                            .is_some_and(|child| child.multiplicity != Multiplicity::Star)
                    })
                    .collect::<BTreeSet<_>>();
                let mut variables = Vec::new();
                for argument in arguments {
                    collect_direct_fragment_variables(argument, &mut variables);
                }
                for (name, annotated_sort) in variables {
                    // Java tracks variables explicitly annotated with a cell sort separately from
                    // cell-fragment variables. They already identify one complete child and must
                    // remain unchanged at non-cell occurrences.
                    if annotated_sort
                        .as_ref()
                        .is_some_and(|sort| model.cells.contains_key(sort))
                    {
                        continue;
                    }
                    let candidates = parent
                        .children
                        .iter()
                        .filter(|child| {
                            child.multiplicity == Multiplicity::Star
                                || !occupied.contains(&child.sort)
                        })
                        .map(|child| child.sort.clone())
                        .collect();
                    observations.push((name, parent.sort.clone(), candidates));
                }
            }
            for argument in arguments {
                collect_fragment_observations(argument, model, observations);
            }
        }
        Term::Rewrite { left, right } => {
            collect_fragment_observations(left, model, observations);
            collect_fragment_observations(right, model, observations);
        }
        Term::As { pattern, alias } => {
            collect_fragment_observations(pattern, model, observations);
            collect_fragment_observations(alias, model, observations);
        }
        Term::Sequence(items) => {
            for item in items {
                collect_fragment_observations(item, model, observations);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn collect_direct_fragment_variables(term: &Term, variables: &mut Vec<(String, Option<Sort>)>) {
    for item in flatten_cells(term) {
        match item.unannotated() {
            Term::Variable { name, sort } => variables.push((name.clone(), sort.clone())),
            Term::Rewrite { left, right } => {
                collect_direct_fragment_variables(left, variables);
                collect_direct_fragment_variables(right, variables);
            }
            _ => {}
        }
    }
}

fn fragment_replacement(info: &FragmentInfo, model: &CellModel) -> Result<Term, String> {
    let parent = &model.cells[&info.parent];
    let mut arguments = Vec::with_capacity(parent.children.len());
    for child in &parent.children {
        if let Some(term) = info.split.get(&child.sort) {
            arguments.push(term.clone());
        } else if let Some(unit) = unit(child) {
            arguments.push(unit);
        } else {
            arguments.push(Term::apply(format!("no{}", child.sort), Vec::new()));
        }
    }
    if parent.children.is_empty() {
        return Err(format!(
            "Unsupported cell fragment with types under {}",
            parent.label.name
        ));
    }
    Ok(Term::apply(
        format!("{}-fragment", parent.label.name),
        arguments,
    ))
}

fn fragment_predicate(info: &FragmentInfo, model: &CellModel) -> Term {
    let parent = &model.cells[&info.parent];
    info.split
        .iter()
        .map(|(sort, term)| {
            let child = parent
                .children
                .iter()
                .find(|child| &child.sort == sort)
                .expect("fragment split sorts are parent children");
            Term::apply(format!("is{}", child.value_sort), vec![term.clone()])
        })
        .reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
        .unwrap_or_else(|| Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        })
}

fn skip_sentence(sentence: &Sentence) -> bool {
    MACRO_ATTRIBUTES
        .iter()
        .any(|attribute| sentence.attributes().get(attribute).is_some())
        || sentence.attributes().get("anywhere").is_some()
        || sentence.attributes().get("simplification").is_some()
}

fn is_function(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    let label = match term.unannotated() {
        Term::Apply { label, .. } => Some(label),
        Term::Rewrite { left, .. } => match left.unannotated() {
            Term::Apply { label, .. } => Some(label),
            _ => None,
        },
        _ => None,
    };
    label.is_some_and(|label| {
        productions
            .function_labels()
            .contains(&LabelHead::from(label))
    })
}

fn contains_cell(term: &Term, model: &CellModel) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if matches!(term.unannotated(), Term::Apply { label, .. } if model.cell_for_label(label).is_some())
        {
            found = true;
        }
    });
    found
}

fn incomplete_parts(arguments: &[Term]) -> Result<(bool, &Term, bool), String> {
    let [left, body, right] = arguments else {
        return Err(format!(
            "Expected incomplete cell with 3 arguments, found {}",
            arguments.len()
        ));
    };
    Ok((dot_value(left)?, body, dot_value(right)?))
}

fn dot_value(term: &Term) -> Result<bool, String> {
    match term.unannotated() {
        Term::Apply { label, arguments } if arguments.is_empty() && label.name == "#dots" => {
            Ok(true)
        }
        Term::Apply { label, arguments } if arguments.is_empty() && label.name == "#noDots" => {
            Ok(false)
        }
        _ => Err("Expected #dots() or #noDots() in incomplete cell".into()),
    }
}

fn incomplete_cell(label: &Label, open_left: bool, body: Term, open_right: bool) -> Term {
    Term::Apply {
        label: label.clone(),
        arguments: vec![dot(open_left), body, dot(open_right)],
    }
}

fn dot(open: bool) -> Term {
    Term::apply(if open { "#dots" } else { "#noDots" }, Vec::new())
}

fn flatten_cells(term: &Term) -> Vec<&Term> {
    fn flatten<'a>(term: &'a Term, output: &mut Vec<&'a Term>) {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.name == "#cells" => {
                for argument in arguments {
                    flatten(argument, output);
                }
            }
            _ => output.push(term),
        }
    }
    let mut output = Vec::new();
    flatten(term, &mut output);
    output
}

fn make_body(mut items: Vec<Term>) -> Term {
    if items.len() == 1 {
        items.pop().unwrap()
    } else {
        Term::apply("#cells", items)
    }
}

fn split_side(term: &Term, model: &CellModel) -> BTreeMap<Sort, Term> {
    flatten_cells(term)
        .into_iter()
        .filter_map(|item| model.sort_for_term(item).map(|sort| (sort, item.clone())))
        .collect()
}

fn unit(child: &Child) -> Option<Term> {
    match child.multiplicity {
        Multiplicity::One => None,
        Multiplicity::Optional | Multiplicity::Star => {
            child.unit.as_ref().map(|label| Term::Apply {
                label: label.clone(),
                arguments: Vec::new(),
            })
        }
    }
}

fn set_variable_sort(term: Term, sort: Sort) -> Term {
    let metadata = term.metadata().cloned();
    let Term::Variable { name, .. } = term.into_unannotated() else {
        unreachable!()
    };
    with_metadata(
        Term::Variable {
            name,
            sort: Some(sort),
        },
        metadata,
    )
}

fn sentence_roots(sentence: &Sentence) -> Vec<&Term> {
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
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. } => vec![body, requires],
        _ => Vec::new(),
    }
}

fn with_metadata(term: Term, metadata: Option<crate::kast::TermMetadata>) -> Term {
    match metadata {
        Some(metadata) => term.with_metadata(metadata),
        None => term,
    }
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidCellConcretization,
        message: message.into(),
        source: None,
        location: None,
    }
}
