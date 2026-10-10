//! ```toml algorithm
//! id = "kompile.cells.concretize"
//! name = "cell concretization"
//! sites = ["concretize_cells", "concretize_cells_pass", "CellModel::new", "Concretizer::sentence"]
//! variable = "M = modules; P = productions; C = cells; N = term nodes; D = cell depth; |children| = children per cell; r = rewrite items compared pairwise in make_parents; L = repeated cell sorts, of any collection type"
//! counters = []
//! no_counter = "cell concretization has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "cell model construction (CellModel::new)"
//! bound = "O(P + C x |children| + r^2) per module plus the forced views.subsorts, once per module and once more per non-main module on the early-exit check"
//!
//! [[cost]]
//! mode = "sentence concretization"
//! bound = "O(N x D x (|children| + L))"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Complete configuration abstractions into fixed-arity cell applications.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, DefinitionViews, LabelHead, ModuleId, ProductionCatalog,
        ProductionItem, ResolvedDefinition, Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{FrontendSort, GeneratedCell, InternalLabel, Label, Sort, Term, TermParts},
    kompile::fresh_names::{FreshNames, GeneratedVariableIdentity},
    provenance::GeneratingPass,
};

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

/// Concretize one sentence with the cell model visible from a named module.
///
/// The returned identity set contains exactly the `_DotVar` element variables
/// minted while transforming this sentence.
pub fn concretize_cells_in_sentence(
    definition: &ResolvedDefinition,
    module: &str,
    sentence: Sentence,
) -> Result<(Sentence, BTreeSet<GeneratedVariableIdentity>), ConcretizeCellsError> {
    let original = sentence.clone();
    let Some(module_id) = definition.module_id(module) else {
        return Err(sentence_error(
            format!("cell syntax module {module:?} was not found"),
            &original,
        ));
    };
    let main_id = definition.main_module_id();
    let main_modules = definition
        .transitive_imports(main_id)
        .into_iter()
        .chain(std::iter::once(main_id))
        .collect::<BTreeSet<_>>();
    let model_module = if main_modules.contains(&module_id) {
        main_id
    } else {
        module_id
    };
    let views = definition.views();
    let model = CellModel::new(&views, model_module)
        .map_err(|message| sentence_error(message, &original))?;
    let productions = views.production_catalog(module_id);
    let mut concretizer = Concretizer::new(&model, productions);
    let transformed = concretizer
        .sentence(sentence)
        .map_err(|message| sentence_error(message, &original))?;
    Ok((transformed, concretizer.generated))
}

/// Complete the configuration abstractions of rules, claims and contexts into fixed-arity cell
/// applications.
pub fn concretize_cells(definition: &Definition) -> Result<Definition, ConcretizeCellsError> {
    super::super::pipeline::run_standalone(
        definition,
        concretize_cells_pass,
        Some(GeneratingPass::ConcretizeCells),
    )
}

pub(crate) fn concretize_cells_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ConcretizeCellsError> {
    let resolved = input.resolved_raw().map_err(|error| ConcretizeCellsError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let main_id = resolved.main_module_id();
    let views = resolved.views();
    let main_modules = resolved
        .transitive_imports(main_id)
        .into_iter()
        .chain(std::iter::once(main_id))
        .collect::<BTreeSet<_>>();
    let main_model = CellModel::new(&views, main_id).map_err(|message| ConcretizeCellsError {
        diagnostics: vec![plain_error(message)],
    })?;
    if main_model.cells.is_empty()
        && resolved.modules().all(|(module_id, _)| {
            main_modules.contains(&module_id)
                || CellModel::new(&views, module_id).is_ok_and(|model| model.cells.is_empty())
        })
    {
        return Ok(input.definition.clone());
    }

    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let local_model;
        let model = if main_modules.contains(&module_id) {
            &main_model
        } else {
            local_model =
                CellModel::new(&views, module_id).map_err(|message| ConcretizeCellsError {
                    diagnostics: vec![plain_error(message)],
                })?;
            &local_model
        };
        // The first sentence of the module whose fragment test became a conjunction, which the
        // module's `BOOL` import is for; it locates the error when the definition has no `BOOL`.
        let mut first_conjunction = None;
        for sentence in &mut module.local_sentences {
            let original = (**sentence).clone();
            let mut concretizer = Concretizer::new(model, productions);
            match concretizer.sentence(original) {
                Ok(transformed) => {
                    if concretizer.conjoins_fragment && first_conjunction.is_none() {
                        first_conjunction = Some(Diagnostic::error(
                            DiagnosticCode::InvalidCellConcretization,
                            super::missing_bool_message("A cell fragment test"),
                            &transformed,
                        ));
                    }
                    *crate::definition::sentence_mut(sentence) = transformed;
                }
                Err(message) => diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidCellConcretization,
                    message,
                    sentence,
                )),
            }
        }
        if let Some(missing_bool) = first_conjunction
            && !super::import_bool(module, resolved)
        {
            diagnostics.push(missing_bool);
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
    /// Whether the instances of a repeated child are ordered: its collection's concatenation is
    /// not commutative (`type="List"`).
    ordered: bool,
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
    initializer_sort: BTreeMap<LabelHead, Sort>,
    collection_members: BTreeMap<Sort, BTreeSet<Sort>>,
    parents: BTreeMap<Sort, Sort>,
    levels: BTreeMap<Sort, usize>,
    root: Sort,
    close_operators: BTreeMap<Sort, (Label, bool, bool)>,
    /// The cell sorts that are the instances of an ordered (`type="List"`) repeated child.
    lists: Vec<Sort>,
}

impl CellModel {
    fn new(views: &DefinitionViews<'_>, module: ModuleId) -> Result<Self, String> {
        let productions = views.production_catalog(module);
        let subsorts = views.subsorts(module).map_err(|error| error.to_string())?;
        let raw_cells = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    items,
                    attributes,
                    ..
                } if attributes.has(AttributeKey::Cell)
                    && !attributes.has(AttributeKey::Internal) =>
                {
                    Some((
                        sort.clone(),
                        label.clone(),
                        items.clone(),
                        attributes.clone(),
                    ))
                }
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            })
            .collect::<Vec<_>>();
        if raw_cells.is_empty() {
            return Ok(Self {
                cells: BTreeMap::new(),
                by_label: BTreeMap::new(),
                cell_term_sort: BTreeMap::new(),
                collection_member: BTreeMap::new(),
                initializer_sort: BTreeMap::new(),
                collection_members: BTreeMap::new(),
                parents: BTreeMap::new(),
                levels: BTreeMap::new(),
                root: Sort::builtin(BuiltinSort::GeneratedTopCell),
                close_operators: BTreeMap::new(),
                lists: Vec::new(),
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
                } if attributes.has(AttributeKey::CellCollection) => Some((
                    sort.clone(),
                    label.clone(),
                    attributes.string(AttributeKey::Unit).map(Label::new),
                    !attributes.has(AttributeKey::Comm),
                )),
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            })
            .collect::<Vec<_>>();
        let initializer_productions = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    items,
                    attributes,
                    ..
                } if attributes.has(AttributeKey::Initializer) => Some((
                    sort.clone(),
                    label.clone(),
                    items
                        .iter()
                        .all(|item| !matches!(item, ProductionItem::NonTerminal { .. })),
                )),
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            })
            .collect::<Vec<_>>();
        let initializers = initializer_productions
            .iter()
            .filter(|(_, _, nullary)| *nullary)
            .map(|(sort, label, _)| (sort.clone(), label.clone()))
            .collect::<BTreeMap<_, _>>();
        let initializer_sort = initializer_productions
            .into_iter()
            .map(|(sort, label, _)| (LabelHead::from(&label), sort))
            .collect();

        let mut cells = BTreeMap::new();
        let mut by_label = BTreeMap::new();
        let mut collection_member = BTreeMap::new();
        let mut collection_members = BTreeMap::<Sort, BTreeSet<Sort>>::new();
        for (sort, label, items, _attributes) in raw_cells {
            if cells.contains_key(&sort) {
                return Err(format!("Too many productions for cell sort: {sort}"));
            }
            let mut children = Vec::new();
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "ProductionItem is syntax; only the listed variants are special here"
            )]
            let nonterminals = items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                _ => None,
            });
            // Invariant: `children` holds one entry for every cell sort and every collection member among the nonterminals before `child_sort`; a non-cell `child_sort` scans `collections` once, so the loop costs O(|nonterminals| * |collections|).
            for child_sort in nonterminals {
                if cell_sorts.contains(&child_sort) {
                    let child_attributes = &cell_attributes[&child_sort];
                    let multiplicity = if child_attributes.string(AttributeKey::Unit).is_some() {
                        Multiplicity::Optional
                    } else {
                        Multiplicity::One
                    };
                    children.push(Child {
                        sort: child_sort.clone(),
                        multiplicity,
                        ordered: false,
                        value_sort: child_sort.clone(),
                        unit: child_attributes.string(AttributeKey::Unit).map(Label::new),
                        concat: None,
                        default: initializers.get(&child_sort).cloned(),
                    });
                    continue;
                }
                if let Some((collection_sort, concat, unit, ordered)) = collections
                    .iter()
                    .find(|(collection_sort, ..)| collection_sort == &child_sort)
                {
                    let mut members = cell_sorts
                        .iter()
                        .filter(|cell| subsorts.directly_less_than(cell, collection_sort))
                        .cloned()
                        .collect::<Vec<_>>();
                    members.sort();
                    // Invariant: `children` and `collection_members[collection_sort]` contain every entry of the sorted `members` before `member`; each member is visited once.
                    for member in members {
                        collection_members
                            .entry(collection_sort.clone())
                            .or_default()
                            .insert(member.clone());
                        children.push(Child {
                            sort: member.clone(),
                            multiplicity: Multiplicity::Star,
                            ordered: *ordered,
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
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "ProductionItem is syntax; only the listed variants are special here"
            )]
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
        // Invariant: `parents` maps every child sort of the cells before `parent_sort` to that cell's sort, and no child seen so far has two parents; each entry of `cells` and each of its `children` is visited once.
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
        // Rules are completed under the generated top cell when the forest has one, whatever
        // roots separately callable configuration initializers add. A unique root is required
        // only where fresh-constant resolution must synthesize that wrapper
        // (`resolve_fresh_constants`), not for this cell forest.
        let root = if let Some(root) = roots
            .iter()
            .find(|sort| cells[*sort].label.name == GeneratedCell::Top.label())
        {
            root.clone()
        } else {
            match roots.as_slice() {
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
            }
        };
        // Every top cell is at level zero, including auxiliary roots whose initializers still
        // need their own children concretized.
        let mut levels = roots
            .into_iter()
            .map(|root| (root, 0))
            .collect::<BTreeMap<_, _>>();
        let mut changed = true;
        // Invariant: every entry of `levels` is a top cell at level zero or a child one level below a parent that had a level; `parents` gives each child one parent, so a pass sets `changed` only while it reaches a deeper level of the `parents` forest, and the loop stops after at most its height plus one passes.
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
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
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
            if !attributes.has(AttributeKey::Assoc)
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
                attributes.has(AttributeKey::Comm),
            ));
        }
        let lists = cells
            .values()
            .flat_map(|cell: &Cell| &cell.children)
            .filter(|child| child.multiplicity == Multiplicity::Star && child.ordered)
            .map(|child| child.sort.clone())
            .collect();
        Ok(Self {
            cells,
            by_label,
            cell_term_sort,
            collection_member,
            initializer_sort,
            collection_members,
            parents,
            levels,
            root,
            close_operators,
            lists,
        })
    }

    /// Whether the configuration places cells of sort `sort` strictly below cells of sort
    /// `ancestor`.
    fn is_strictly_below(&self, sort: &Sort, ancestor: &Sort) -> bool {
        let mut current = sort;
        // Invariant: `current` is `sort` or one of its ancestors, reached by at most `self.cells.len()` parent links; a well-formed configuration is a forest, whose chains are shorter than that, and the bound stops a cyclic parent chain.
        for _ in 0..self.cells.len() {
            match self.parents.get(current) {
                Some(parent) if parent == ancestor => return true,
                Some(parent) => current = parent,
                None => return false,
            }
        }
        false
    }

    /// Whether cells of sort `sort` are a `multiplicity="*"` child of their configured parent.
    fn is_repeated(&self, sort: &Sort) -> bool {
        self.parents.get(sort).is_some_and(|parent| {
            self.cells[parent]
                .children
                .iter()
                .any(|child| child.sort == *sort && child.multiplicity == Multiplicity::Star)
        })
    }

    fn cell_for_label(&self, label: &Label) -> Option<&Cell> {
        self.by_label
            .get(&LabelHead::from(label))
            .and_then(|sort| self.cells.get(sort))
    }

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn sort_for_term(&self, term: &Term) -> Option<Sort> {
        match term.unannotated() {
            Term::Apply { label, .. } => self
                .cell_term_sort
                .get(&LabelHead::from(label))
                .or_else(|| self.collection_member.get(&LabelHead::from(label)))
                .cloned()
                .or_else(|| {
                    let result_sort = self.initializer_sort.get(&LabelHead::from(label))?;
                    if self.cells.contains_key(result_sort) {
                        return Some(result_sort.clone());
                    }
                    let members = self.collection_members.get(result_sort)?;
                    (members.len() == 1).then(|| members.first().unwrap().clone())
                }),
            Term::Variable { sort, .. } => sort
                .clone()
                .or_else(|| term.metadata().and_then(|metadata| metadata.sort.clone()))
                .filter(|sort| self.cells.contains_key(sort)),
            Term::Rewrite { left, right } => {
                let left = self.sort_for_side(left);
                let right = self.sort_for_side(right);
                match (left, right) {
                    (Some(left), Some(right)) if left == right => Some(left),
                    (Some(sort), None) | (None, Some(sort)) => Some(sort),
                    _ => None,
                }
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

struct Concretizer<'use_, 'definition> {
    model: &'use_ CellModel,
    productions: &'use_ ProductionCatalog<'definition>,
    fresh: FreshNames,
    generated: BTreeSet<GeneratedVariableIdentity>,
    fragments: BTreeMap<String, FragmentInfo>,
    /// Whether a fragment test of the last sentence became a conjunction (`_andBool_`) of the
    /// sort predicates of two or more cells.
    conjoins_fragment: bool,
    /// The cells of the last sentence moved out of the parent they were written in, as
    /// "`<cell>` written inside `<parent>`", named in an error of that sentence.
    moved_cells: RefCell<Vec<String>>,
    /// The number of incomplete parent cells completed so far in the last sentence, which
    /// identifies the written parent a lifted cell comes from ([`MovedCell::origin`]).
    completed_parents: std::cell::Cell<usize>,
}

/// A cell written inside a parent cell that the configuration does not place it under, lifted
/// out of that parent. It rides with the subterm it was moved out of (its anchor) until the
/// completion of an enclosing cell reaches the instance of its configured parent that holds the
/// anchor, and is inserted there (see [`Concretizer::complete_parent`]).
struct MovedCell {
    term: Term,
    /// The sort of the moved cell.
    sort: Sort,
    /// The configured parent sort of the moved cell, a strict ancestor of its written parent's
    /// sort.
    parent: Sort,
    /// The label of the moved cell.
    cell: String,
    /// The label of the cell it was written in.
    written_in: String,
    /// The cells moved out of this one, which ride with it.
    riders: Vec<MovedCell>,
    /// Which written parent cell it was lifted out of: cells lifted out of one written parent
    /// share it, and were written as siblings there.
    origin: usize,
}

impl MovedCell {
    fn describe(&self) -> String {
        format!(
            "Cell {} written inside {} belongs outside {} in the configuration",
            self.cell, self.written_in, self.written_in
        )
    }
}

#[derive(Clone)]
struct FragmentInfo {
    parent: Sort,
    candidates: BTreeSet<Sort>,
    split: BTreeMap<Sort, Term>,
}

impl<'use_, 'definition> Concretizer<'use_, 'definition> {
    fn new(model: &'use_ CellModel, productions: &'use_ ProductionCatalog<'definition>) -> Self {
        Self {
            model,
            productions,
            fresh: FreshNames::default(),
            generated: BTreeSet::new(),
            fragments: BTreeMap::new(),
            conjoins_fragment: false,
            moved_cells: RefCell::new(Vec::new()),
            completed_parents: std::cell::Cell::new(0),
        }
    }

    fn sentence(&mut self, sentence: Sentence) -> Result<Sentence, String> {
        if matches!(&sentence, Sentence::Claim { body, .. } if !contains_cell(body, self.model)) {
            return Ok(sentence);
        }
        self.fresh = FreshNames::for_sentence(&sentence);
        self.generated.clear();
        self.fragments.clear();
        self.conjoins_fragment = false;
        self.moved_cells.borrow_mut().clear();
        self.concretize_sentence(sentence).map_err(|message| {
            let moved = self.moved_cells.borrow();
            // A placement error already names the moved cell it is about.
            if moved.is_empty() || moved.iter().any(|moved| message.contains(moved.as_str())) {
                message
            } else {
                format!(
                    "{message} (after moving {} to where the configuration declares it)",
                    moved.join(", ")
                )
            }
        })
    }

    fn concretize_sentence(&mut self, sentence: Sentence) -> Result<Sentence, String> {
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.concretize_body(body, skip_root_wrapping(&attributes))?;
                let requires = self.close(requires, false)?;
                let ensures = self.close(ensures, false)?;
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
                let body = self.concretize_body(body, skip_root_wrapping(&attributes))?;
                let requires = self.close(requires, false)?;
                let ensures = self.close(ensures, false)?;
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
                let body = self.concretize_body(body, skip_root_wrapping(&attributes))?;
                let requires = self.close(requires, false)?;
                self.analyze_fragments([&body, &requires])?;
                Ok(Sentence::Context {
                    body: self.sort_cells(body)?,
                    requires: self.sort_cells(requires)?,
                    attributes,
                })
            }
            Sentence::ContextAlias {
                body,
                requires,
                attributes,
            } => {
                let body = self.concretize_body(body, skip_root_wrapping(&attributes))?;
                let requires = self.close(requires, false)?;
                self.analyze_fragments([&body, &requires])?;
                Ok(Sentence::ContextAlias {
                    body: self.sort_cells(body)?,
                    requires: self.sort_cells(requires)?,
                    attributes,
                })
            }
            sentence @ Sentence::SyntaxSort { .. }
            | sentence @ Sentence::SortSynonym { .. }
            | sentence @ Sentence::SyntaxLexical { .. }
            | sentence @ Sentence::Production { .. }
            | sentence @ Sentence::SyntaxAssociativity { .. }
            | sentence @ Sentence::SyntaxPriority { .. }
            | sentence @ Sentence::Configuration { .. }
            | sentence @ Sentence::Bubble { .. } => Ok(sentence),
        }
    }

    fn concretize_body(&mut self, body: Term, skip_root: bool) -> Result<Term, String> {
        let body = if skip_root || is_function(&body, self.productions) {
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
                    self.fresh_variable(Some(child.value_sort.clone()), "_Gen")
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
        if let Term::Apply { label, arguments } = term.unannotated() {
            if is_matching_logic_builtin(&label.name)
                && let Some(recurse) =
                    self.ml_result_sort_children(&term, label, arguments.len())?
            {
                if recurse.iter().any(|recurse| *recurse) {
                    let metadata = term.metadata().cloned();
                    let TermParts::Apply { label, arguments } =
                        term.into_unannotated().into_parts()
                    else {
                        unreachable!()
                    };
                    let arguments = arguments
                        .into_iter()
                        .zip(recurse)
                        .map(|(argument, recurse)| {
                            if recurse {
                                self.add_root(argument)
                            } else {
                                Ok(argument)
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let rebuilt = Term::Apply { label, arguments };
                    return Ok(with_metadata(rebuilt, metadata));
                }
                return Ok(term);
            }
            if label.name == root.label.name {
                return Ok(term);
            }
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

    fn ml_result_sort_children(
        &self,
        term: &Term,
        label: &Label,
        argument_count: usize,
    ) -> Result<Option<Vec<bool>>, String> {
        let resolved = term
            .metadata()
            .and_then(|metadata| metadata.production)
            .and_then(|resolved| self.productions.lookup(&resolved))
            .map(|resolved| self.productions.production(resolved))
            .filter(|production| {
                matches!(
                    production,
                    Sentence::Production {
                        label: Some(production_label),
                        ..
                    } if production_label.name == label.name
                )
            });
        let production = resolved.or_else(|| {
            let ids = self.productions.productions_for(&LabelHead::from(label));
            (ids.len() == 1).then(|| self.productions.production(ids[0]))
        });
        let Some(Sentence::Production {
            parameters,
            sort,
            items,
            ..
        }) = production
        else {
            return Ok(None);
        };
        let Some(result_parameter) = parameters.iter().find(|parameter| *parameter == sort) else {
            return Ok(Some(vec![false; argument_count]));
        };
        let recurse = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort == result_parameter),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect::<Vec<_>>();
        if recurse.len() != argument_count {
            return Err(format!(
                "KLabel {:?} has {} arguments but its production has {} nonterminals",
                label.name,
                argument_count,
                recurse.len()
            ));
        }
        Ok(Some(recurse))
    }

    /// Complete every incomplete parent cell of `term` with its missing intermediate cells.
    ///
    /// A cell written inside a parent cell whose sort is not an ancestor of the cell's sort in
    /// the configuration is lifted out of that parent and placed in the instance of its
    /// configured parent that holds the written parent, when that configured parent is an
    /// ancestor of the written one (see [`Self::complete_parent`]); otherwise the rule is
    /// rejected. A lifted cell that would have to leave the body of an enclosing cell (through a
    /// rewrite, an alias, a sequence, a non-cell symbol or the top of `term`) has no place in the
    /// rule, which is rejected.
    fn add_parents(&self, term: Term) -> Result<Term, String> {
        let (term, moved) = self.place_cells(term)?;
        match moved.first() {
            None => Ok(term),
            Some(moved) => Err(format!(
                "{}, and the rule has no enclosing cell to hold it",
                moved.describe()
            )),
        }
    }

    /// [`Self::add_parents`] on one subterm, returning the cells moved out of it that the
    /// enclosing cell bag must place.
    fn place_cells(&self, term: Term) -> Result<(Term, Vec<MovedCell>), String> {
        let metadata = term.metadata().cloned();
        let (rebuilt, moved) = match term.into_unannotated().into_parts() {
            TermParts::Apply { label, arguments } => {
                let parent = self
                    .model
                    .cell_for_label(&label)
                    .filter(|cell| !cell.children.is_empty());
                if let Some(cell) = parent
                    && let Ok((open_left, body, open_right)) = incomplete_parts(&arguments)
                {
                    // Each item of the body keeps the cells lifted out of it, so that its
                    // completion can place them in the instances that hold it.
                    let items = flatten_cells(body)
                        .into_iter()
                        .map(|item| self.place_cells(item.clone()))
                        .collect::<Result<Vec<_>, _>>()?;
                    let (completed, moved) =
                        self.complete_parent(&label, cell, open_left, open_right, items)?;
                    return Ok((with_metadata(completed, metadata), moved));
                }
                let mut moved = Vec::new();
                let mut placed = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    let (argument, argument_moved) = self.place_cells(argument)?;
                    placed.push(argument);
                    moved.extend(argument_moved);
                }
                if label.is(InternalLabel::Cells) {
                    // A cell concatenation is transparent: the moved cells become siblings of
                    // its items in the same enclosing bag.
                    (
                        Term::Apply {
                            label,
                            arguments: placed,
                        },
                        moved,
                    )
                } else if let Some(cell) = parent {
                    // Not an incomplete cell (handled above): a complete cell, whose arguments
                    // are its children in declared order, or a malformed one.
                    if let Some(first) = moved.first() {
                        return Err(format!(
                            "{}, and moving it there would cross the complete cell {}",
                            first.describe(),
                            label.name
                        ));
                    }
                    if !self.complete_cell_arguments(&placed, cell) {
                        incomplete_parts(&placed)?;
                        unreachable!("an incomplete cell is completed above");
                    }
                    (
                        Term::Apply {
                            label,
                            arguments: placed,
                        },
                        Vec::new(),
                    )
                } else if let Some(moved) = moved.first() {
                    return Err(format!(
                        "{}, and moving it there would cross {}",
                        moved.describe(),
                        if self.model.cell_for_label(&label).is_some() {
                            format!("the contents of the leaf cell {}", label.name)
                        } else {
                            format!("the symbol {}", label.name)
                        }
                    ));
                } else {
                    (
                        Term::Apply {
                            label,
                            arguments: placed,
                        },
                        Vec::new(),
                    )
                }
            }
            TermParts::Rewrite { left, right } => {
                let (left, left_moved) = self.place_cells(*left)?;
                let (right, right_moved) = self.place_cells(*right)?;
                if let Some(moved) = left_moved.first().or(right_moved.first()) {
                    return Err(format!(
                        "{}, and moving it there would take it across a rewrite",
                        moved.describe()
                    ));
                }
                (
                    Term::Rewrite {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    Vec::new(),
                )
            }
            TermParts::As { pattern, alias } => {
                let (pattern, pattern_moved) = self.place_cells(*pattern)?;
                let (alias, alias_moved) = self.place_cells(*alias)?;
                if let Some(moved) = pattern_moved.first().or(alias_moved.first()) {
                    return Err(format!(
                        "{}, and moving it there would take it out of an alias pattern (#as)",
                        moved.describe()
                    ));
                }
                (
                    Term::As {
                        pattern: Box::new(pattern),
                        alias: Box::new(alias),
                    },
                    Vec::new(),
                )
            }
            TermParts::Sequence(items) => {
                let mut placed = Vec::with_capacity(items.len());
                for item in items {
                    let (item, moved) = self.place_cells(item)?;
                    if let Some(moved) = moved.first() {
                        return Err(format!(
                            "{}, and moving it there would take it out of a K sequence",
                            moved.describe()
                        ));
                    }
                    placed.push(item);
                }
                (Term::Sequence(placed), Vec::new())
            }
            leaf @ (TermParts::InjectedLabel(_)
            | TermParts::Variable { .. }
            | TermParts::Token { .. }) => (Term::from(leaf), Vec::new()),
            TermParts::Annotated { .. } => unreachable!(),
        };
        Ok((with_metadata(rebuilt, metadata), moved))
    }

    /// Complete an incomplete parent `cell` (written with label `label`) whose body items,
    /// already placed, are `items`, each with the cells lifted out of it.
    ///
    /// Each cell item whose sort the configuration places below `cell` is wrapped in its missing
    /// intermediate cells, grouped with its siblings by [`Self::make_parents`]. A cell lifted out
    /// of an item is inserted into the instance of its configured parent that holds the item:
    /// the wrapper of that sort built around the item, or `cell` itself.
    ///
    /// Each other cell item `C` is lifted out of `cell` and returned, to be placed the same way
    /// by an enclosing cell. Lifting keeps every containment the rule states about `C` except
    /// the ones the configuration makes impossible (`C` inside `cell`, and inside any written
    /// cell below `C`'s configured parent), and adds none: every cell that holds `C` in the
    /// compiled rule also holds `cell`. It is therefore allowed only when `C`'s configured
    /// parent is a strict ancestor of `cell`; a `C` of `cell`'s own sort or an ancestor sort
    /// (an inverted nesting) or one whose place is in another branch of the configuration (a
    /// relocation into cells the rule does not write) is rejected.
    ///
    /// A cell item below `cell` written beside the only instance of one of its ancestors that
    /// `cell` can hold is placed inside that instance (see [`Self::place_in_written_ancestors`]).
    fn complete_parent(
        &self,
        label: &Label,
        cell: &Cell,
        open_left: bool,
        open_right: bool,
        items: Vec<(Term, Vec<MovedCell>)>,
    ) -> Result<(Term, Vec<MovedCell>), String> {
        let origin = self.completed_parents.get();
        self.completed_parents.set(origin + 1);
        let mut completion = Vec::new();
        let mut others = Vec::new();
        let mut riders = Vec::new();
        let mut moved = Vec::new();
        // Invariant: the items before `item` are split into rewrites of one cell sort each where
        // they are rewrites of cells of several known sorts, in written order; each item is
        // visited once and split by one walk of its two sides.
        let items = items.into_iter().flat_map(|(item, item_riders)| {
            match self.split_by_sort(&item) {
                // A rewrite carries no moved cells: `place_cells` rejects moving one across it.
                Some(parts) => parts
                    .into_iter()
                    .map(|part| (part, Vec::new()))
                    .collect::<Vec<_>>(),
                None => vec![(item, item_riders)],
            }
        });
        for (item, item_riders) in items {
            match self.model.sort_for_term(&item) {
                Some(sort) if self.model.is_strictly_below(&sort, &cell.sort) => {
                    completion.push((item, item_riders));
                }
                Some(sort) => {
                    moved.push(self.lift(item, sort, label, cell, item_riders, origin)?);
                }
                None => {
                    others.push(item);
                    riders.extend(item_riders);
                }
            }
        }
        let mut completion = self.place_in_written_ancestors(cell, completion)?;
        let target_level = self.model.levels[&cell.sort] + 1;
        let level = |(item, _): &(Term, Vec<MovedCell>)| {
            self.model
                .sort_for_term(item)
                .and_then(|sort| self.model.levels.get(&sort).copied())
        };
        // Invariant: `completion` holds the terms still to be placed under `cell`, all of sorts strictly below `cell.sort`, each with the lifted cells whose configured parent is an ancestor of its sort; each iteration replaces every item at the `deepest` level by `make_parents` cells one level up, so the deepest level above `target_level` decreases, and the loop ends with every item a child of `cell`.
        while completion
            .iter()
            .any(|item| level(item).is_some_and(|level| level > target_level))
        {
            let deepest = completion
                .iter()
                .filter_map(level)
                .max()
                .expect("completion terms have levels");
            let mut grouped = BTreeMap::<Sort, Vec<(Term, Vec<MovedCell>)>>::new();
            let mut retained = Vec::new();
            for item in completion {
                let Some(sort) = self.model.sort_for_term(&item.0) else {
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
                retained.extend(self.make_parents(parent, open_left || open_right, items)?);
            }
            completion = retained;
        }
        for (item, item_riders) in completion {
            others.push(item);
            riders.extend(item_riders);
        }
        for rider in self.insert_lifted(cell, &mut others, riders)? {
            if !self.model.is_strictly_below(&cell.sort, &rider.parent) {
                // Unreachable for a lifted cell: its configured parent is an ancestor of the cell
                // it was lifted out of, so it is `cell`, a wrapper built above, or above `cell`.
                return Err(format!(
                    "Cell {} written inside {} has no place under {}",
                    rider.cell, rider.written_in, label.name
                ));
            }
            moved.push(rider);
        }
        Ok((
            Term::Apply {
                label: label.clone(),
                arguments: vec![dot(open_left), make_body(others), dot(open_right)],
            },
            moved,
        ))
    }

    /// The rewrites of one cell sort each that `item` denotes, when it is a rewrite of cells of
    /// several known sorts; `None` otherwise (it is not a rewrite, its cells are of one sort, or
    /// a side holds a term of unknown cell sort).
    ///
    /// A rule with local rewrites means its two projections: its left side with every rewrite
    /// replaced by that rewrite's left side, and likewise for the right. Within a cell bag the
    /// place of a rewrite is immaterial, so `(L => R)` denotes the same rule as one rewrite
    /// `(L_s => R_s)` per cell sort `s` of its sides, `L_s` and `R_s` being its cells of sort `s`
    /// in written order (the empty bag when there are none). Completion then places each part by
    /// its one sort, as it places a rewrite written that way, whether the rewrite's cells belong
    /// in the cell it is written in, below it, or (lifted) elsewhere.
    fn split_by_sort(&self, item: &Term) -> Option<Vec<Term>> {
        let Term::Rewrite { left, right } = item.unannotated() else {
            return None;
        };
        let mut parts = Vec::<(Sort, Vec<Term>, Vec<Term>)>::new();
        // Invariant: `parts` holds, in order of first occurrence, every cell sort of the items of
        // the sides before `side` and of the items of `side` before `part`, with those items per
        // side in written order; each item is visited once and placed by a scan of `parts`,
        // O(|items| x |sorts|).
        for (right_side, side) in [(false, left), (true, right)] {
            for part in flatten_cells(side) {
                if is_empty_cell_bag(part) {
                    continue;
                }
                let sort = self.model.sort_for_term(part)?;
                let index = match parts.iter().position(|(known, ..)| *known == sort) {
                    Some(index) => index,
                    None => {
                        parts.push((sort, Vec::new(), Vec::new()));
                        parts.len() - 1
                    }
                };
                let (_, lefts, rights) = &mut parts[index];
                if right_side {
                    rights.push(part.clone());
                } else {
                    lefts.push(part.clone());
                }
            }
        }
        if parts.len() < 2 {
            return None;
        }
        let metadata = item.metadata().cloned();
        Some(
            parts
                .into_iter()
                .map(|(_, lefts, rights)| {
                    with_metadata(
                        Term::Rewrite {
                            left: Box::new(cell_bag(lefts)),
                            right: Box::new(cell_bag(rights)),
                        },
                        metadata.clone(),
                    )
                })
                .collect(),
        )
    }

    /// Move each of `items`, the cell items written in one instance of `cell` and below it,
    /// into the item of an ancestor sort written beside it, when that instance of `cell` holds
    /// only one cell of each sort on the configuration's path from `cell` down to that ancestor
    /// (no cell on that path is `multiplicity="*"`) and only one item of the ancestor's sort is
    /// written: the configuration then makes that written cell the one that holds the item. The
    /// closest such ancestor is used, and it is completed again with the items moved into it.
    ///
    /// Without this, completion would wrap the item in a fresh instance of the ancestor, a second
    /// instance where the configuration allows one. An ancestor written closed (no `...`) or not
    /// as a cell body cannot take the item, and the rule is rejected.
    ///
    /// The move does not depend on what lies below the ancestor: the item written beside the one
    /// instance of its ancestor and the item written inside it state the same rule, so both are
    /// completed inside the ancestor, by one reading, whether or not a `multiplicity="*"` cell
    /// lies between them. When a `multiplicity="*"` cell lies above the ancestor, an instance of
    /// `cell` may hold many instances of the ancestor, the written one is not the one that holds
    /// the item, and the item is left where it is written.
    fn place_in_written_ancestors(
        &self,
        cell: &Cell,
        items: Vec<(Term, Vec<MovedCell>)>,
    ) -> Result<Vec<(Term, Vec<MovedCell>)>, String> {
        let sorts = items
            .iter()
            .map(|(item, _)| self.model.sort_for_term(item))
            .collect::<Vec<_>>();
        let mut written = BTreeMap::<&Sort, Vec<usize>>::new();
        // Invariant: `written` maps each sort to the indices of the items before `index` of that sort; each item is visited once.
        for (index, sort) in sorts.iter().enumerate() {
            if let Some(sort) = sort {
                written.entry(sort).or_default().push(index);
            }
        }
        let holder = |sort: &Sort| {
            let mut ancestors = Vec::new();
            let mut current = sort;
            // Invariant: `ancestors` holds the strict ancestors of `sort` below `cell.sort`, closest first, reached by at most `self.model.cells.len()` parent links (the bound of `is_strictly_below`).
            for _ in 0..self.model.cells.len() {
                match self.model.parents.get(current) {
                    Some(parent) if *parent != cell.sort => {
                        ancestors.push(parent);
                        current = parent;
                    }
                    _ => break,
                }
            }
            let mut holder = None;
            // Invariant: `holder` is the index of the written item of the closest ancestor so far (from `cell` down) of which the rule writes one item, and no ancestor visited so far is repeated; each ancestor is visited once.
            for ancestor in ancestors.into_iter().rev() {
                if self.model.is_repeated(ancestor) {
                    // An instance of `cell` may hold many instances of `ancestor`: only a holder
                    // written above it is the one instance that holds the item.
                    break;
                }
                if let Some([index]) = written.get(ancestor).map(Vec::as_slice) {
                    holder = Some(*index);
                }
            }
            holder
        };
        let mut incoming = vec![Vec::new(); items.len()];
        let mut any = false;
        // Invariant: `incoming[holder]` lists, in written order, the items before `index` that move into item `holder`; each item is visited once, O(D) each.
        for (index, sort) in sorts.iter().enumerate() {
            if let Some(into) = sort.as_ref().and_then(holder) {
                incoming[into].push(index);
                any = true;
            }
        }
        if !any {
            return Ok(items);
        }
        let mut order = (0..items.len()).collect::<Vec<_>>();
        order.sort_by_key(|index| {
            std::cmp::Reverse(
                sorts[*index]
                    .as_ref()
                    .map_or(0, |sort| self.model.levels[sort]),
            )
        });
        let mut slots = items.into_iter().map(Some).collect::<Vec<_>>();
        // Invariant: the items deeper than `into` are complete with everything moved into them; an item moves only into a strictly shallower one, so it is taken from its slot after its own turn and before its holder is completed again.
        for into in order {
            if incoming[into].is_empty() {
                continue;
            }
            let added = incoming[into]
                .iter()
                .map(|index| slots[*index].take().expect("an item moves into one holder"))
                .collect();
            let ancestor = slots[into].take().expect("a holder is completed once");
            slots[into] = Some(self.place_in_written_cell(ancestor, added)?);
        }
        Ok(slots.into_iter().flatten().collect())
    }

    /// Complete the written cell `ancestor` again with `added`, cell items written beside it
    /// (as siblings in one body) that belong inside it.
    ///
    /// An added instance of an ordered (`type="List"`) repeated cell, or an added term that may
    /// hold one, has a stated position only among the items written with it, so it is added only
    /// when nothing in `ancestor` may be part of the same list ([`Self::body_may_hold`]); the rule
    /// is rejected otherwise.
    fn place_in_written_cell(
        &self,
        (ancestor, mut ancestor_riders): (Term, Vec<MovedCell>),
        added: Vec<(Term, Vec<MovedCell>)>,
    ) -> Result<(Term, Vec<MovedCell>), String> {
        let name = |sort: &Sort| self.model.cells[sort].label.name.clone();
        let holder = self
            .model
            .sort_for_term(&ancestor)
            .map(|sort| name(&sort))
            .unwrap_or_default();
        let item = added
            .first()
            .and_then(|(item, _)| self.model.sort_for_term(item))
            .map(|sort| name(&sort))
            .unwrap_or_default();
        let reason = |item: &str| {
            format!(
                "Cell {item} written beside {holder} belongs inside it: the configuration allows only one {holder} there"
            )
        };
        let incomplete = match ancestor.unannotated() {
            Term::Apply { label, arguments } => self
                .model
                .cell_for_label(label)
                .filter(|cell| !cell.children.is_empty())
                .zip(incomplete_parts(arguments).ok()),
            Term::Variable { .. }
            | Term::Token { .. }
            | Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => None,
        };
        let Some((cell, (open_left, body, open_right))) = incomplete else {
            return Err(format!(
                "{}, and that {holder} is not written as a cell body {item} can be added to",
                reason(&item)
            ));
        };
        if !open_left && !open_right {
            return Err(format!(
                "{}, and it is written closed (without ...), so it has no other children",
                reason(&item)
            ));
        }
        let body_items = flatten_cells(body);
        let beside = body_items
            .iter()
            .copied()
            .chain(added.iter().map(|(term, _)| term))
            .collect::<Vec<_>>();
        // Invariant: for every ordered sort below `cell` before `list`, the added items or the items of `body_items` hold no item of that list; each ordered sort is visited once, with one walk of the added items and one of `ancestor`'s body (with the added items, for the path child).
        for list in self
            .model
            .lists
            .iter()
            .filter(|list| self.model.is_strictly_below(list, &cell.sort))
        {
            let holds_path_child = self.holds_path_child(&cell.sort, list, &beside);
            // An added cell above `list` brings its own instance of the list's parent.
            let joining = added.iter().find(|(term, _)| {
                self.model
                    .sort_for_term(term)
                    .is_none_or(|sort| !self.model.is_strictly_below(list, &sort))
                    && self.moved_may_hold(term, list, holds_path_child)
            });
            if let Some((term, _)) = joining
                && self.body_may_hold(&body_items, list)
            {
                let item = self
                    .model
                    .sort_for_term(term)
                    .map(|sort| name(&sort))
                    .unwrap_or_default();
                return Err(format!(
                    "{}, the {} cells in it form a list, and the rule does not state its position among the other items of that list",
                    reason(&item),
                    name(list)
                ));
            }
        }
        let Term::Apply { label, .. } = ancestor.unannotated() else {
            unreachable!("an incomplete cell is an application")
        };
        let items = body_items
            .into_iter()
            .map(|child| (child.clone(), Vec::new()))
            .chain(added)
            .collect();
        let (completed, moved) = self.complete_parent(label, cell, open_left, open_right, items)?;
        ancestor_riders.extend(moved);
        Ok((
            with_metadata(completed, ancestor.metadata().cloned()),
            ancestor_riders,
        ))
    }

    /// The `...` markers and the body of `term` when it is a cell written as a cell body (an
    /// incomplete cell), or `None`.
    fn cell_body<'t>(&self, term: &'t Term) -> Option<(bool, &'t Term, bool)> {
        match term.unannotated() {
            Term::Apply { label, arguments } => self
                .model
                .cell_for_label(label)
                .filter(|cell| !cell.children.is_empty())
                .and_then(|_| incomplete_parts(arguments).ok()),
            Term::Variable { .. }
            | Term::Token { .. }
            | Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => None,
        }
    }

    /// Whether `term`, an item of a cell body, may be or hold an instance of the cell sort
    /// `sort`. The answer follows the cell sorts `term` may have, item by item, never the one
    /// sort [`CellModel::sort_for_term`] gives a whole rewrite (which drops the items of unknown
    /// sort):
    /// - a rewrite may if either side may, and an `#as` pattern if its pattern or alias may;
    /// - an empty cell bag may not;
    /// - a term of cell sort `sort` may;
    /// - a term of a cell sort above `sort` may when it is not written as a cell body (a variable,
    ///   a complete cell, a function result), when its `...` frame is open (the frame stands for
    ///   its unwritten children), or when an item of its body may;
    /// - a term of another cell sort may not, whatever its body: after completion a cell holds
    ///   only the cells the configuration places in it (a misplaced cell has been lifted out of
    ///   it), and none of those is `sort` or above it;
    /// - every other term (a variable of `Bag`, of a cell collection sort or of no cell sort, a
    ///   function of `Bag` sort, a matching-logic connective) has no known cell sort, and may.
    fn may_hold_instance(&self, term: &Term, sort: &Sort) -> bool {
        self.item_may_hold(term, sort, true)
    }

    /// [`Self::may_hold_instance`], where `unknown` is the answer for a term of unknown cell
    /// sort that is `term` or a part of a rewrite or an alias `term` is (not one inside a cell
    /// body of `term`, which is always `true`).
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only rewrites and aliases are looked into structurally"
    )]
    fn item_may_hold(&self, term: &Term, sort: &Sort, unknown: bool) -> bool {
        let any_item = |bag: &Term, unknown: bool| {
            flatten_cells(bag)
                .into_iter()
                .any(|item| self.item_may_hold(item, sort, unknown))
        };
        match term.unannotated() {
            Term::Rewrite { left, right } => any_item(left, unknown) || any_item(right, unknown),
            Term::As { pattern, alias } => any_item(pattern, unknown) || any_item(alias, unknown),
            _ if is_empty_cell_bag(term) => false,
            _ => match self.model.sort_for_term(term) {
                None => unknown,
                Some(term_sort) if term_sort == *sort => true,
                // After completion a cell holds only cells the configuration places in it (a
                // misplaced one has been lifted out), so one not above `sort` holds none.
                Some(term_sort) if !self.model.is_strictly_below(sort, &term_sort) => false,
                Some(_) => match self.cell_body(term) {
                    Some((open_left, body, open_right)) => {
                        open_left || open_right || any_item(body, true)
                    }
                    None => true,
                },
            },
        }
    }

    /// Whether `term`, a cell item written beside a written cell `H` and moved into it, may be
    /// or hold an instance of `list` there; `holds_path_child` tells whether `H` already holds
    /// the one cell of the child sort `D` of `H` on the path to `list`
    /// ([`Self::holds_path_child`]).
    ///
    /// A term of unknown cell sort in `term` is a sibling of `term`'s cells, so it stands for
    /// children of an instance of their parent `P`: it may hold instances of `list` only when
    /// `list` is below `P` and `H` does not hold that one `D`. When `P` is `H`, the written `D`
    /// is the only one, and the term cannot stand for another. When `P` is below `H`, `term`
    /// continues into the written `D` and is decided again there, as `D`'s added item.
    fn moved_may_hold(&self, term: &Term, list: &Sort, holds_path_child: bool) -> bool {
        let unknown = !holds_path_child
            && self
                .model
                .sort_for_term(term)
                .and_then(|sort| self.model.parents.get(&sort))
                .is_none_or(|parent| self.model.is_strictly_below(list, parent));
        self.item_may_hold(term, list, unknown)
    }

    /// Whether `items` (the body of a written cell of sort `holder` and the items moved into
    /// it) hold the one cell of the child sort `D` of `holder` on the path to `list`: `D` is not
    /// `multiplicity="*"` and an item is a cell of sort `D`.
    fn holds_path_child(&self, holder: &Sort, list: &Sort, items: &[&Term]) -> bool {
        self.child_toward(holder, list).is_some_and(|child| {
            !self.model.is_repeated(&child)
                && items.iter().any(|item| self.is_written_cell(item, &child))
        })
    }

    /// The child sort of `ancestor` on the configured path down to `sort` (`sort` itself when
    /// it is a child of `ancestor`), or `None` when `sort` is not below `ancestor`.
    fn child_toward(&self, ancestor: &Sort, sort: &Sort) -> Option<Sort> {
        let mut current = sort;
        // Invariant: `current` is `sort` or one of its ancestors below `ancestor`, reached by at most `self.model.cells.len()` parent links (the bound of `is_strictly_below`).
        for _ in 0..self.model.cells.len() {
            match self.model.parents.get(current) {
                Some(parent) if parent == ancestor => return Some(current.clone()),
                Some(parent) => current = parent,
                None => return None,
            }
        }
        None
    }

    /// Whether `item`, an item of a cell body, is a cell of sort `sort` on every side: a term of
    /// that sort, a rewrite each side of which holds one, or an alias that does.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only rewrites and aliases are looked into structurally"
    )]
    fn is_written_cell(&self, item: &Term, sort: &Sort) -> bool {
        let side = |bag: &Term| {
            flatten_cells(bag)
                .into_iter()
                .any(|item| self.is_written_cell(item, sort))
        };
        match item.unannotated() {
            Term::Rewrite { left, right } => side(left) && side(right),
            Term::As { pattern, alias } => side(pattern) || side(alias),
            _ => self.model.sort_for_term(item).as_ref() == Some(sort),
        }
    }

    /// The items of `term` when it is a cell that cells placed beside it continue into on their
    /// way to an instance of `sort`: a cell written as a cell body, of a sort strictly above
    /// `sort` that is not `multiplicity="*"`, hence the only cell of its sort where it is
    /// written. The placed cells go inside it, beside its `...` frame, as cells written there do.
    fn continuation<'t>(&self, term: &'t Term, sort: &Sort) -> Option<Vec<&'t Term>> {
        let term_sort = self.model.sort_for_term(term)?;
        if !self.model.is_strictly_below(sort, &term_sort) || self.model.is_repeated(&term_sort) {
            return None;
        }
        self.cell_body(term).map(|(_, body, _)| flatten_cells(body))
    }

    /// Whether an item of `items`, the body of a written cell that cells written elsewhere are
    /// placed into, may be or hold an instance of `sort` in the collection those cells join:
    /// a cell they continue into ([`Self::continuation`]) is looked into, without its frame,
    /// which is the rest of that collection, after the placed cells; every other item is decided
    /// by [`Self::may_hold_instance`].
    fn body_may_hold(&self, items: &[&Term], sort: &Sort) -> bool {
        items
            .iter()
            .any(|item| match self.continuation(item, sort) {
                Some(body) => self.body_may_hold(&body, sort),
                None => self.may_hold_instance(item, sort),
            })
    }

    /// Lift the cell `item` of sort `sort`, written inside `cell` (labelled `label`) with the
    /// cells `riders` lifted out of it, out of `cell`, or reject it. `origin` identifies that
    /// written `cell`.
    fn lift(
        &self,
        item: Term,
        sort: Sort,
        label: &Label,
        cell: &Cell,
        riders: Vec<MovedCell>,
        origin: usize,
    ) -> Result<MovedCell, String> {
        let name = &self.model.cells[&sort].label.name;
        if sort == cell.sort {
            return Err(format!(
                "Cell {name} written inside another {}: the configuration never nests a cell in a cell of its own sort",
                label.name
            ));
        }
        if self.model.is_strictly_below(&cell.sort, &sort) {
            return Err(format!(
                "Cell {name} written inside {}: the configuration places {} inside {name}",
                label.name, label.name
            ));
        }
        let parent =
            self.model.parents.get(&sort).ok_or_else(|| {
                format!("Cell {name} written inside {} has no parent", label.name)
            })?;
        if !self.model.is_strictly_below(&cell.sort, parent) {
            return Err(format!(
                "Cell {name} written inside {} belongs in {} in the configuration, which does not contain {}",
                label.name, self.model.cells[parent].label.name, label.name
            ));
        }
        self.moved_cells
            .borrow_mut()
            .push(format!("{name} written inside {}", label.name));
        Ok(MovedCell {
            term: item,
            parent: parent.clone(),
            sort,
            cell: name.clone(),
            written_in: label.name.clone(),
            riders,
            origin,
        })
    }

    /// Insert into `body`, the children of one instance of `holder`, each lifted cell of
    /// `riders` whose configured parent is `holder`, with the cells riding with it in turn, and
    /// return the others. A lifted cell of a sort that is not `multiplicity="*"` whose place in
    /// that instance is already taken is rejected: the rule gives it no other instance.
    ///
    /// The instances of an ordered (`type="List"`) repeated cell are concatenated in body order,
    /// and the rule states that order only among instances written as siblings in one cell body.
    /// A lifted cell that may be or hold an instance of such a list ([`Self::may_hold_instance`])
    /// is therefore inserted only when every other item of `body` that may is a cell lifted out of
    /// the same written parent (inserted in written order); it is rejected otherwise.
    fn insert_lifted(
        &self,
        holder: &Cell,
        body: &mut Vec<Term>,
        riders: Vec<MovedCell>,
    ) -> Result<Vec<MovedCell>, String> {
        let mut pending = std::collections::VecDeque::from(riders);
        let mut remaining = Vec::new();
        let lists = holder
            .children
            .iter()
            .filter(|child| child.multiplicity == Multiplicity::Star && child.ordered)
            .collect::<Vec<_>>();
        // The written parent of the lifted cells inserted so far that may hold items of each list.
        let mut ordered_origins = BTreeMap::<Sort, usize>::new();
        // Invariant: every lifted cell seen so far is in `body` or `remaining`, or still in `pending`; each cell is dequeued once, and a rider is enqueued only when the cell it rides with is inserted.
        while let Some(rider) = pending.pop_front() {
            if rider.parent != holder.sort {
                remaining.push(rider);
                continue;
            }
            // Invariant: for each list before `list` that `rider` may hold items of, every other item of `body` that may hold one came out of `rider`'s written parent; each list is visited once, with at most one walk of `body`.
            for list in &lists {
                if !self.may_hold_instance(&rider.term, &list.sort) {
                    continue;
                }
                let stated = match ordered_origins.get(&list.sort) {
                    Some(origin) => *origin == rider.origin,
                    None => !body
                        .iter()
                        .any(|item| self.may_hold_instance(item, &list.sort)),
                };
                if !stated {
                    return Err(format!(
                        "Cell {} written inside {} belongs in the {} that holds {}, whose {} cells form a list, and the rule does not state its position among the other items of that list",
                        rider.cell,
                        rider.written_in,
                        holder.label.name,
                        rider.written_in,
                        self.model.cells[&list.sort].label.name
                    ));
                }
                ordered_origins.insert(list.sort.clone(), rider.origin);
            }
            let child = holder
                .children
                .iter()
                .find(|child| child.sort == rider.sort);
            let repeatable = child.is_some_and(|child| child.multiplicity == Multiplicity::Star);
            if !repeatable
                && body
                    .iter()
                    .any(|item| self.model.sort_for_term(item).as_ref() == Some(&rider.sort))
            {
                return Err(format!(
                    "Cell {} written inside {} belongs in the {} that holds {}, which already has a {}",
                    rider.cell, rider.written_in, holder.label.name, rider.written_in, rider.cell
                ));
            }
            body.push(rider.term);
            pending.extend(rider.riders);
        }
        Ok(remaining)
    }

    /// Wrap `items`, cells whose configured parent is `parent`, in instances of `parent`, each
    /// with the cells lifted out of its items that belong in it; return the wrappers with the
    /// lifted cells that belong higher. The instances are the classes of
    /// [`Self::instance_classes`], in the order of their first items.
    fn make_parents(
        &self,
        parent: &Cell,
        open: bool,
        items: Vec<(Term, Vec<MovedCell>)>,
    ) -> Result<Vec<(Term, Vec<MovedCell>)>, String> {
        let classes = self.instance_classes(
            parent,
            &items.iter().map(|(item, _)| item).collect::<Vec<_>>(),
        )?;
        let mut slots = items.into_iter().map(Some).collect::<Vec<_>>();
        classes
            .into_iter()
            .map(|class| {
                let (mut body, riders): (Vec<_>, Vec<_>) = class
                    .into_iter()
                    .map(|index| slots[index].take().expect("an item is in one class"))
                    .unzip();
                let riders =
                    self.insert_lifted(parent, &mut body, riders.into_iter().flatten().collect())?;
                Ok((
                    incomplete_cell(&parent.label, open, make_body(body), open),
                    riders,
                ))
            })
            .collect()
    }

    /// The non-`multiplicity="*"` children of `parent` that `item`, an item written in an
    /// instance of `parent`, occupies on `side`: the sorts of the cells of that side of it.
    fn nonrepeated_slots(&self, parent: &Cell, item: &Term, side: Side) -> BTreeSet<Sort> {
        side_parts(item, side)
            .into_iter()
            .filter_map(|part| self.model.sort_for_term(part))
            // Invariant: each sort is tested against `parent.children` once, O(|parts| x |parent.children|).
            .filter(|sort| {
                parent
                    .children
                    .iter()
                    .any(|child| child.sort == *sort && child.multiplicity != Multiplicity::Star)
            })
            .collect()
    }

    /// The instances of `parent` that hold `items`, cells written outside every instance of
    /// `parent` whose configured parent is `parent`, as classes of item indices.
    ///
    /// Two items *can share* an instance when they occupy no common non-`multiplicity="*"`
    /// child on the same side of the rule (an item outside a rewrite is on both sides). Which
    /// items share is a fact about the cell structure, which both sides of every rewrite share,
    /// so this never reads the direction of a rewrite. Loose cells that can share are in one
    /// instance, a convention (`docs/compatibility.md`, "Cells written inside another cell"):
    /// the instances are the classes of "can share" when that relation is an equivalence, in
    /// the order of their first items. Otherwise an item can share with two items that cannot
    /// share with each other, the rule does not state which instance holds it, and it is
    /// rejected.
    fn instance_classes(&self, parent: &Cell, items: &[&Term]) -> Result<Vec<Vec<usize>>, String> {
        let slots = items
            .iter()
            .map(|item| {
                [Side::Left, Side::Right].map(|side| self.nonrepeated_slots(parent, item, side))
            })
            .collect::<Vec<_>>();
        let share = |first: usize, second: usize| {
            (0..2).all(|side| slots[first][side].is_disjoint(&slots[second][side]))
        };
        let mut classes = Vec::<Vec<usize>>::new();
        // Invariant: `classes` partitions the items before `index` into classes of "can share",
        // each class sharing with no item of another; each item is compared with every earlier
        // item once, O(|items|^2) comparisons.
        for index in 0..items.len() {
            let mut joined = None::<(usize, usize)>;
            for (class_index, class) in classes.iter().enumerate() {
                let (sharing, apart): (Vec<usize>, Vec<usize>) =
                    class.iter().partition(|other| share(index, **other));
                let Some(&with) = sharing.first() else {
                    continue;
                };
                if let Some(&without) = apart.first() {
                    return Err(format!(
                        "Ambiguous completion: {}: {} can share one {} with {} but not with {}, which can share one with {}, so the rule does not state which {} holds it",
                        parent.label.name,
                        self.describe_cells(items[index]),
                        parent.label.name,
                        self.describe_cells(items[with]),
                        self.describe_cells(items[without]),
                        self.describe_cells(items[with]),
                        parent.label.name,
                    ));
                }
                if let Some((_, first)) = joined {
                    return Err(format!(
                        "Ambiguous completion: {}: {} can share one {} with {} and with {}, which cannot share one, so the rule does not state which {} holds it",
                        parent.label.name,
                        self.describe_cells(items[index]),
                        parent.label.name,
                        self.describe_cells(items[first]),
                        self.describe_cells(items[with]),
                        parent.label.name,
                    ));
                }
                joined = Some((class_index, with));
            }
            match joined {
                Some((class_index, _)) => classes[class_index].push(index),
                None => classes.push(vec![index]),
            }
        }
        Ok(classes)
    }

    /// The cells of `item` (both sides of a rewrite) by label, each cell written as a cell body
    /// with the cells written in it, for a message.
    fn describe_cells(&self, item: &Term) -> String {
        let mut names = Vec::new();
        // Invariant: `names` describes each cell of the sides before `side`, without repeats; each part is visited once, with one walk of its body.
        for side in [Side::Left, Side::Right] {
            for part in side_parts(item, side) {
                let Some(sort) = self.model.sort_for_term(part) else {
                    continue;
                };
                let mut name = self.model.cells[&sort].label.name.clone();
                if let Some((_, body, _)) = self.cell_body(part) {
                    let inner = flatten_cells(body)
                        .into_iter()
                        .filter(|inner| !is_empty_cell_bag(inner))
                        .map(|inner| self.describe_cells(inner))
                        .collect::<Vec<_>>();
                    if !inner.is_empty() {
                        name = format!("{name} (holding {})", inner.join(" "));
                    }
                }
                if !names.contains(&name) {
                    names.push(name);
                }
            }
        }
        if names.is_empty() {
            "an item".to_owned()
        } else {
            names.join(" ")
        }
    }

    fn close(&mut self, term: Term, on_rhs: bool) -> Result<Term, String> {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated().into_parts() {
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.close(*left, false)?),
                right: Box::new(self.close(*right, true)?),
            },
            TermParts::Apply { label, arguments } => {
                let mut application = Term::Apply {
                    label: label.clone(),
                    arguments,
                };
                if let Some(cell) = self.model.cell_for_label(&label) {
                    application = self.close_cell(application, cell, on_rhs)?;
                }
                let TermParts::Apply { label, arguments } = application.into_parts() else {
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
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(self.close(*pattern, on_rhs)?),
                alias: Box::new(self.close(*alias, on_rhs)?),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.close(item, on_rhs))
                    .collect::<Result<_, _>>()?,
            ),
            leaf @ (TermParts::InjectedLabel(_)
            | TermParts::Variable { .. }
            | TermParts::Token { .. }) => Term::from(leaf),
            TermParts::Annotated { .. } => unreachable!(),
        };
        Ok(with_metadata(rebuilt, metadata))
    }

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn close_cell(&mut self, application: Term, cell: &Cell, on_rhs: bool) -> Result<Term, String> {
        let TermParts::Apply { label, arguments } = application.into_parts() else {
            unreachable!()
        };
        if self.complete_cell_arguments(&arguments, cell) {
            return Ok(Term::Apply { label, arguments });
        }
        let (open_left, body, open_right) = incomplete_parts(&arguments)?;
        let contents = flatten_cells(body).into_iter().cloned().collect::<Vec<_>>();
        if !cell.children.is_empty() {
            let required = |side_right: bool| {
                let mut required = cell
                    .children
                    .iter()
                    .filter(|child| child.multiplicity == Multiplicity::One)
                    .map(|child| child.sort.clone())
                    .collect::<BTreeSet<_>>();
                for item in &contents {
                    #[expect(
                        clippy::wildcard_enum_match_arm,
                        reason = "Term is syntax; only the listed variants are special here"
                    )]
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
                    // Invariant: `contents` has gained the default initializer of every sort of `required_left` before `sort`; each `sort` scans `cell.children` once, O(|required_left| * |cell.children|).
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
        let cell_sort = cell
            .leaf_sort
            .clone()
            .unwrap_or_else(|| Sort::builtin(BuiltinSort::K));
        if cell_sort.name == BuiltinSort::K.k_name() {
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

    // A structured producer may supply a cell that already matches its expanded
    // production: the declared single body for a leaf, or every declared child
    // sort in declared order for a parent. The parser-shaped representation can
    // never satisfy this check because its outer arguments are the reserved
    // nullary #dots/#noDots markers, which have no cell sort.
    fn complete_cell_arguments(&self, arguments: &[Term], cell: &Cell) -> bool {
        if cell.children.is_empty() {
            return arguments.len() == 1;
        }
        arguments.len() == cell.children.len()
            && arguments
                .iter()
                .zip(&cell.children)
                .all(|(argument, child)| {
                    self.model.sort_for_term(argument).as_ref() == Some(&child.sort)
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
        crate::stack::guarded(|| self.sort_cells_level(term, replace_fragments))
    }

    /// One level of [`Self::sort_cells_with_fragments`], which runs it with stack for one more
    /// level.
    fn sort_cells_level(&mut self, term: Term, replace_fragments: bool) -> Result<Term, String> {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated().into_parts() {
            TermParts::Apply { label, arguments } => {
                if let [argument] = arguments.as_slice()
                    && let Term::Variable { name, .. } = argument.unannotated()
                    && let Some(info) = self.fragments.get(name)
                    && (label.name
                        == Label::sort_predicate(&Sort::new(format!("{}Fragment", info.parent)))
                            .name
                        || label.name
                            == Label::sort_predicate(&Sort::frontend(FrontendSort::Bag)).name)
                {
                    self.conjoins_fragment |= info.split.len() > 1;
                    fragment_predicate(info, self.model)
                } else if let Some(cell) = self.model.cell_for_label(&label)
                    && !cell.children.is_empty()
                {
                    let ordered = self.order_children(label, arguments, cell)?;
                    let TermParts::Apply { label, arguments } = ordered.into_parts() else {
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
                    // Ordered parent slots contain projected fragment variables. A leaf's
                    // contents are ordinary terms, where source fragments must be rebuilt.
                    let replace_fragments = replace_fragments
                        || self
                            .model
                            .cell_for_label(&label)
                            .is_some_and(|cell| cell.children.is_empty());
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
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.sort_cells_with_fragments(*left, replace_fragments)?),
                right: Box::new(self.sort_cells_with_fragments(*right, replace_fragments)?),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(self.sort_cells_with_fragments(*pattern, replace_fragments)?),
                alias: Box::new(self.sort_cells_with_fragments(*alias, replace_fragments)?),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.sort_cells_with_fragments(item, replace_fragments))
                    .collect::<Result<_, _>>()?,
            ),
            TermParts::Variable { name, sort } => {
                if replace_fragments {
                    self.fragments.get(&name).map_or_else(
                        || Ok(Term::Variable { name, sort }),
                        |info| fragment_replacement(info, self.model),
                    )?
                } else {
                    Term::Variable { name, sort }
                }
            }
            leaf @ (TermParts::InjectedLabel(_) | TermParts::Token { .. }) => Term::from(leaf),
            TermParts::Annotated { .. } => unreachable!(),
        };
        Ok(with_metadata(rebuilt, metadata))
    }

    fn order_children(
        &mut self,
        label: Label,
        arguments: Vec<Term>,
        cell: &Cell,
    ) -> Result<Term, String> {
        let arguments = self.merge_one_sided_rewrites(arguments, cell);
        let mut ordered = BTreeMap::<Sort, Term>::new();
        let mut unknown = Vec::new();
        // Invariant: `ordered` holds the child terms placed for the items of `arguments` before `item`, concatenated per sort by `insert_child`, and `unknown` holds the bare variables among them; each item is visited once.
        for item in arguments {
            if let Term::Rewrite { left, right } = item.unannotated() {
                let left_side = left.as_ref();
                let right_side = right.as_ref();
                let left = self.split_rewrite_side(left_side, false, cell)?;
                let right = self.split_rewrite_side(right_side, true, cell)?;
                let mut sorts = left
                    .keys()
                    .chain(right.keys())
                    .cloned()
                    .collect::<BTreeSet<_>>();
                if sorts.is_empty()
                    && ((matches!(left_side.unannotated(), Term::Variable { .. })
                        && is_empty_cell_bag(right_side))
                        || (is_empty_cell_bag(left_side)
                            && matches!(right_side.unannotated(), Term::Variable { .. })))
                {
                    let candidates = cell
                        .children
                        .iter()
                        .filter(|child| child.multiplicity == Multiplicity::Star)
                        .collect::<Vec<_>>();
                    if let [child] = candidates.as_slice() {
                        sorts.insert(child.sort.clone());
                    }
                }
                let singleton_sort = sorts.len() == 1;
                for sort in sorts {
                    // Invariant: `ordered` holds a rewrite for every entry of `sorts` before `sort`; each `sort` scans `cell.children` once, O(|sorts| * |cell.children|).
                    let child = cell
                        .children
                        .iter()
                        .find(|child| child.sort == sort)
                        .ok_or_else(|| format!("Unexpected child sort {sort} in {}", label.name))?;
                    let left = left
                        .get(&sort)
                        .cloned()
                        .or_else(|| {
                            singleton_sort
                                .then(|| rewrite_side_variable(item.unannotated(), false, child))
                                .flatten()
                        })
                        .or_else(|| unit(child))
                        .ok_or_else(|| format!("Cannot rewrite required cell {sort} from unit"))?;
                    let right = right
                        .get(&sort)
                        .cloned()
                        .or_else(|| {
                            singleton_sort
                                .then(|| rewrite_side_variable(item.unannotated(), true, child))
                                .flatten()
                        })
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
            } else if let Some(sort) = self.model.sort_for_term(&item) {
                self.insert_child(&mut ordered, sort, item, cell)?;
            } else if matches!(item.unannotated(), Term::Variable { .. }) {
                unknown.push(item);
            } else {
                return Err(format!(
                    "Unexpected term in parent cell {} during child ordering",
                    label.name
                ));
            }
        }
        // Invariant: `ordered` holds the children placed for the variables of `unknown` before `variable`; each variable without a fragment split scans `cell.children` once, O(|unknown| * |cell.children|).
        for variable in unknown {
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "Term is syntax; only the listed variants are special here"
            )]
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

    /// `arguments`, the children of an instance of `cell`, with each removal `(X => .Bag)` and
    /// addition `(.Bag => Y)` of one non-`multiplicity="*"` child sort merged into the one
    /// rewrite `(X => Y)` of that child, when they are the only items that write it.
    ///
    /// A rule means its two projections, and the place of a rewrite in a bag is immaterial: the
    /// child is `X` in the left projection and `Y` in the right one, which is what `(X => Y)`
    /// states. Written apart, each would otherwise be completed with the child's unit on its
    /// empty side, and the instance would hold the child twice.
    fn merge_one_sided_rewrites(&self, mut arguments: Vec<Term>, cell: &Cell) -> Vec<Term> {
        // The sort and side of an item that is a rewrite writing cells of one sort on one side
        // only.
        let one_sided = |item: &Term| -> Option<(Sort, Side)> {
            let Term::Rewrite { .. } = item.unannotated() else {
                return None;
            };
            let [left, right] = [Side::Left, Side::Right].map(|side| side_parts(item, side));
            let (side, parts) = match (left.is_empty(), right.is_empty()) {
                (false, true) => (Side::Left, left),
                (true, false) => (Side::Right, right),
                (true, true) | (false, false) => return None,
            };
            let mut sorts = parts.iter().map(|part| self.model.sort_for_term(part));
            let sort = sorts.next()??;
            sorts
                .all(|other| other.as_ref() == Some(&sort))
                .then_some((sort, side))
        };
        let shapes = arguments.iter().map(one_sided).collect::<Vec<_>>();
        let mut merged = Vec::new();
        // Invariant: `merged` holds the (removal, addition) index pairs of the non-repeated children before `child` that two one-sided rewrites alone write; each child scans `arguments` once, O(|cell.children| x |arguments|).
        for child in cell
            .children
            .iter()
            .filter(|child| child.multiplicity != Multiplicity::Star)
        {
            let of_side = |side: Side| {
                shapes
                    .iter()
                    .enumerate()
                    .filter(|(_, shape)| {
                        shape
                            .as_ref()
                            .is_some_and(|(sort, written)| *sort == child.sort && *written == side)
                    })
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>()
            };
            let (removals, additions) = (of_side(Side::Left), of_side(Side::Right));
            let ([removal], [addition]) = (removals.as_slice(), additions.as_slice()) else {
                continue;
            };
            let written_elsewhere = arguments.iter().enumerate().any(|(index, item)| {
                index != *removal
                    && index != *addition
                    && [Side::Left, Side::Right].iter().any(|side| {
                        side_parts(item, *side).into_iter().any(|part| {
                            self.model.sort_for_term(part).as_ref() == Some(&child.sort)
                        })
                    })
            });
            if !written_elsewhere {
                merged.push((*removal, *addition));
            }
        }
        if merged.is_empty() {
            return arguments;
        }
        let mut dropped = BTreeSet::new();
        // Invariant: each pair before `pair` has its rewrite at the earlier of its two indices and the later index in `dropped`; each pair is visited once.
        for (removal, addition) in merged {
            let side = |index: usize, right: bool| match arguments[index].unannotated() {
                Term::Rewrite { left, right: rhs } => {
                    if right {
                        (**rhs).clone()
                    } else {
                        (**left).clone()
                    }
                }
                Term::Apply { .. }
                | Term::Variable { .. }
                | Term::Token { .. }
                | Term::InjectedLabel(_)
                | Term::As { .. }
                | Term::Sequence(_)
                | Term::Annotated { .. } => unreachable!("a one-sided item is a rewrite"),
            };
            let rewrite = Term::Rewrite {
                left: Box::new(side(removal, false)),
                right: Box::new(side(addition, true)),
            };
            let (first, second) = (removal.min(addition), removal.max(addition));
            arguments[first] = rewrite;
            dropped.insert(second);
        }
        arguments
            .into_iter()
            .enumerate()
            .filter(|(index, _)| !dropped.contains(index))
            .map(|(_, item)| item)
            .collect()
    }

    /// The children of `parent` that `term`, the left (`right` false) or right side of a rewrite
    /// in `parent`'s body, writes, by child sort.
    ///
    /// Every item of `term` is accounted for: a cell is placed by its sort, a variable by its
    /// fragment split or its cell sort, the empty bag occupies no child, and any other item is
    /// rejected. Such an item (a `Bag`-sorted function application, an alias) is a term of the
    /// rule that no child of `parent` holds, so skipping it would compile a rule without it, and
    /// that rule denotes a different relation.
    fn split_rewrite_side(
        &self,
        term: &Term,
        right: bool,
        parent: &Cell,
    ) -> Result<BTreeMap<Sort, Term>, String> {
        let mut split = BTreeMap::new();
        // Invariant: `split` holds the child terms of the flattened items of `term` before `item`, concatenated per sort by `insert_child`; each item is visited once.
        for item in flatten_cells(term) {
            if let Some(sort) = self.model.sort_for_term(item) {
                self.insert_child(&mut split, sort, item.clone(), parent)?;
                continue;
            }
            let Term::Variable { name, sort } = item.unannotated() else {
                if is_empty_cell_bag(item) {
                    continue;
                }
                return Err(self.unplaceable_rewrite_item(item, right, parent));
            };
            if let Some(fragment) = self.fragments.get(name) {
                for (sort, term) in &fragment.split {
                    self.insert_child(&mut split, sort.clone(), term.clone(), parent)?;
                }
            } else if let Some(sort) = sort
                && self.model.cells.contains_key(sort)
            {
                self.insert_child(&mut split, sort.clone(), item.clone(), parent)?;
            }
        }
        Ok(split)
    }

    /// The error for `item`, an item of the left (`right` false) or right side of a rewrite in
    /// `parent`'s body that is neither a cell, a variable nor the empty bag. It names the item:
    /// a symbol by its label (and sort, when one production declares it), an alias by its
    /// variable.
    fn unplaceable_rewrite_item(&self, item: &Term, right: bool, parent: &Cell) -> String {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only applications and aliases are named specially"
        )]
        let item = match item.unannotated() {
            Term::Apply { label, .. } => {
                let head = LabelHead::from(label);
                let kind = if self.productions.function_labels().contains(&head) {
                    "function"
                } else {
                    "symbol"
                };
                let sort = match self.productions.productions_for(&head) {
                    [production] => match self.productions.production(*production) {
                        Sentence::Production { sort, .. } => format!(" of sort {sort}"),
                        Sentence::SyntaxSort { .. }
                        | Sentence::SortSynonym { .. }
                        | Sentence::SyntaxLexical { .. }
                        | Sentence::SyntaxAssociativity { .. }
                        | Sentence::SyntaxPriority { .. }
                        | Sentence::ContextAlias { .. }
                        | Sentence::Context { .. }
                        | Sentence::Rule { .. }
                        | Sentence::Claim { .. }
                        | Sentence::Configuration { .. }
                        | Sentence::Bubble { .. } => String::new(),
                    },
                    _ => String::new(),
                };
                format!("the {kind} `{}`{sort}", label.name)
            }
            Term::As { alias, .. } => format!("the alias `{alias}`"),
            other => format!("`{other}`"),
        };
        format!(
            "Cell completion cannot place {item}, written on the {} side of a rewrite in {}: \
             only cells, variables and the empty bag `.Bag` stand among a cell's children, and \
             the rule compiled without it would not be the rule written",
            if right { "right" } else { "left" },
            parent.label.name
        )
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
        let name = self.fresh.mint(prefix);
        if prefix == "_DotVar" {
            self.generated
                .insert(GeneratedVariableIdentity::element(name.clone()));
        }
        Term::Variable { name, sort }
    }
}

// Invariant: each call visits one node of `term` and recurses only into its direct subterms, so the finite `term` bounds the calls; `observations` holds one entry for every non-cell-annotated variable found directly under a cell parent in the nodes already visited.
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
                // Invariant: `observations` has one entry for every variable of `variables` before `name` that carries no cell-sort annotation; each such variable scans `parent.children` once, O(|variables| * |parent.children|).
                for (name, annotated_sort) in variables {
                    // A variable annotated with a cell sort is not a cell-fragment variable: it
                    // already denotes one complete child and remains unchanged at non-cell
                    // occurrences.
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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
            // Invariant: each entry of `info.split` scans `parent.children` once for its sort, O(|info.split| * |parent.children|), and the `reduce` conjoins one sort predicate per entry.
            let child = parent
                .children
                .iter()
                .find(|child| &child.sort == sort)
                .expect("fragment split sorts are parent children");
            Term::Apply {
                label: Label::sort_predicate(&child.value_sort),
                arguments: vec![term.clone()],
            }
        })
        .reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
        .unwrap_or_else(|| Term::Token {
            token: "true".into(),
            sort: Sort::builtin(BuiltinSort::Bool),
        })
}

fn skip_root_wrapping(attributes: &Attributes) -> bool {
    attributes.has_any(&AttributeKey::MACRO_LIKE)
        || attributes.has_any(&[AttributeKey::Anywhere, AttributeKey::Simplification])
}

fn is_matching_logic_builtin(label: &str) -> bool {
    InternalLabel::of(label).is_some_and(|label| InternalLabel::MATCHING_LOGIC.contains(&label))
}

fn rewrite_side_variable(term: &Term, right: bool, child: &Child) -> Option<Term> {
    let Term::Rewrite { left, right: rhs } = term else {
        return None;
    };
    let side = if right { rhs.as_ref() } else { left.as_ref() };
    matches!(side.unannotated(), Term::Variable { .. })
        .then(|| set_variable_sort(side.clone(), child.value_sort.clone()))
}

fn is_empty_cell_bag(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, arguments }
            if arguments.is_empty()
                && [InternalLabel::Cells, InternalLabel::DotBag]
                    .iter()
                    .any(|l| label.is(*l))
    )
}

fn is_function(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn dot_value(term: &Term) -> Result<bool, String> {
    match term.unannotated() {
        Term::Apply { label, arguments }
            if arguments.is_empty() && label.is(InternalLabel::Dots) =>
        {
            Ok(true)
        }
        Term::Apply { label, arguments }
            if arguments.is_empty() && label.is(InternalLabel::NoDots) =>
        {
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
    Term::apply(
        if open {
            InternalLabel::Dots
        } else {
            InternalLabel::NoDots
        }
        .as_str(),
        Vec::new(),
    )
}

fn flatten_cells(term: &Term) -> Vec<&Term> {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn flatten<'a>(term: &'a Term, output: &mut Vec<&'a Term>) {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.is(InternalLabel::Cells) => {
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

/// A side of a rule: its left projection (every rewrite replaced by its left side) or its right
/// projection.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side {
    Left,
    Right,
}

/// What `item`, an item of a cell body, writes in the `side` projection of the rule: the items of
/// that side of a rewrite, or `item` itself (on both sides), without empty bags.
fn side_parts(item: &Term, side: Side) -> Vec<&Term> {
    let written = match item.unannotated() {
        Term::Rewrite { left, right } => match side {
            Side::Left => flatten_cells(left),
            Side::Right => flatten_cells(right),
        },
        Term::Apply { .. }
        | Term::Variable { .. }
        | Term::Token { .. }
        | Term::InjectedLabel(_)
        | Term::As { .. }
        | Term::Sequence(_)
        | Term::Annotated { .. } => flatten_cells(item),
    };
    written
        .into_iter()
        .filter(|part| !is_empty_cell_bag(part))
        .collect()
}

/// The cell bag of `items`: the empty bag, the one item, or their concatenation.
fn cell_bag(items: Vec<Term>) -> Term {
    if items.is_empty() {
        Term::apply(InternalLabel::Cells.as_str(), Vec::new())
    } else {
        make_body(items)
    }
}

fn make_body(mut items: Vec<Term>) -> Term {
    if items.len() == 1 {
        items.pop().unwrap()
    } else {
        Term::apply(InternalLabel::Cells.as_str(), items)
    }
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
    let TermParts::Variable { name, .. } = term.into_unannotated().into_parts() else {
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
        input_addresses: Vec::new(),
    }
}

fn sentence_error(message: impl Into<String>, sentence: &Sentence) -> ConcretizeCellsError {
    ConcretizeCellsError {
        diagnostics: vec![Diagnostic::error(
            DiagnosticCode::InvalidCellConcretization,
            message,
            sentence,
        )],
    }
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::{
        definition::Sentence,
        kast::Term,
        kompile::stage_harness::{labelled, render, run_to_stage},
    };

    /// A rule mentions only the cells it reads or writes; it applies to the whole
    /// configuration, whose other cells it leaves as they are. Concretization states this:
    /// the rule is placed under every ancestor cell up to the generated top cell (which the
    /// fresh-constant stage put above the user's top cell, beside the counter), each cell is a
    /// fixed-arity application of its production, and a cell the rule does not mention is
    /// matched by a variable and rebuilt unchanged. No cell-bag abstraction (`#cells`,
    /// `#dots`, `#noDots`) remains in any sentence.
    #[test]
    fn rules_are_completed_to_the_whole_configuration_with_unmentioned_cells_kept() {
        let run = run_to_stage(
            r#"
module INT
endmodule
module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
  syntax Id ::= r"[a-z]+" [token]
              | freshId(Int) [function, freshGenerator, symbol(freshId)]
  syntax Exp ::= Int | Id | "go" [symbol(go)] | done(Id) [symbol(done)]
  configuration <t> <k> go </k> <s> 0 </s> </t>
  rule <k> go => done(!X:Id) </k> [label(fresh)]
  rule <s> 0 => 1 </s> [label(state)]
endmodule
"#,
            "concretize cells",
        );
        let output = run.output();
        assert_eq!(
            render(labelled(output, "MAIN", "fresh")[0]),
            r#"rule `<generatedTop>`(`<t>`(`<k>`(go(.KList)=>done(freshId(`_+Int_`(#Fresh,#token("0","Int"))))),_DotVar1),`<generatedCounter>`(#Fresh=>`_+Int_`(#Fresh,#token("1","Int")))) requires #token("true","Bool") ensures #token("true","Bool")"#
        );
        assert_eq!(
            render(labelled(output, "MAIN", "state")[0]),
            r#"rule `<generatedTop>`(`<t>`(_DotVar1,`<s>`(#token("0","Int")=>#token("1","Int"))),_DotVar0) requires #token("true","Bool") ensures #token("true","Bool")"#
        );

        fn abstractions(term: &Term, found: &mut Vec<String>) {
            match term {
                Term::Apply { label, arguments } => {
                    if matches!(label.name.as_str(), "#cells" | "#dots" | "#noDots") {
                        found.push(label.name.clone());
                    }
                    arguments
                        .iter()
                        .for_each(|argument| abstractions(argument, found));
                }
                Term::Annotated { term, .. } => abstractions(term, found),
                Term::Rewrite { left, right } => {
                    abstractions(left, found);
                    abstractions(right, found);
                }
                Term::As { pattern, alias } => {
                    abstractions(pattern, found);
                    abstractions(alias, found);
                }
                Term::Sequence(items) => items.iter().for_each(|item| abstractions(item, found)),
                Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            }
        }
        for module in &output.modules {
            for sentence in &module.local_sentences {
                if let Sentence::Rule { .. } | Sentence::Claim { .. } = &**sentence {
                    let mut found = Vec::new();
                    for (_, term) in sentence.terms() {
                        abstractions(term, &mut found);
                    }
                    assert!(found.is_empty(), "{found:?} in {}", render(sentence));
                }
            }
        }
    }
}
