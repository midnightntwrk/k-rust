//! ```toml algorithm-site
//! id = "kompile.sort_injections.insert"
//! role = "variant"
//! sites = ["SentenceTyper::typing", "SentenceTyper::typing_of", "Walk::visit", "Walk::injected", "Walk::projected"]
//! ```
//!
//! A read-only typing view of a loaded rule-like sentence, computed by the sort injector on the
//! sentence as compilation hands it to injection: semantic casts resolved, and a body with a
//! rewrite projected into its left and right branches.
//!
//! Cost: the body is walked at most four times (a sort walk and a placement walk per branch of a
//! body with a rewrite, one of each otherwise), the conditions once, and a `#withConfig`
//! context once. At every node the walk
//! names the node's path by its node in a trie the walks share (`PathTrie`, constant time per
//! step), types the resolved subterm there in place, and asks the injector for the node's sort
//! and placement as injection does, the injector inferring each node's sort once per expected
//! sort over the whole typing (`NaturalSorts`). Only a node above a rewrite (or, in the right
//! branch, above an as-pattern) is typed on a projected copy of its subterm
//! (`Walk::projected`). For N nodes, k of them above a rewrite, of height h, that is
//! O(N x (P + S) + k x h) with the injector's P and S, plus the parametric instance searches
//! and one semantic-cast resolution of the sentence; reading every path back out of the typing
//! (`PathMap::iter`) costs O(N x h).
//! A sentence with a variable in the body of a cell with children also costs its cell
//! completion's analysis (`typing/cell_content.rs`), and the typer builds the cell model once
//! per model module. `kompile.macros.expand` computes this view once per rewrite of a
//! sentence when some macro rule has a parametric head.
//!
//! Building a typer computes the productions compilation adds to the module's closure, one scan
//! of the closure's V sentences and its sort universe (O(V log V)), and builds its own
//! production catalog over the closure and the added productions (O(P log P) for P
//! productions) in place of the module's cached one: no definition declares the rule-language
//! constructs, so something is always added. Typing the local functions of a module's sentences
//! builds, once per such module, that module's lambda injector: its sort helpers over its
//! closure (O(V log V)) and one more production catalog over the closure and the helpers
//! (O(P log P), `kompile::passes::lambda_productions`).

use std::borrow::Cow;
use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use crate::definition::{
    AttributeKey, Attributes, LabelHead, ModuleId, PartialOrder, ProductionCatalog, ProductionItem,
    ResolvedDefinition, Sentence,
};
use crate::kast::{InternalLabel, Sort, Term};
use crate::kompile::passes::{
    CellCompletion, FunctionRuleWithContext, LambdaSorts, LocalFunction, ResolveSemanticCastsError,
    resolve_semantic_casts_in_sentence, semantic_cast_variable_sorts, with_kitem_subsorts,
};
use crate::kompile::view::View;
use crate::names::BuiltinSort;

use super::{
    SortInjectionError, SortInjector, SortMismatch, has_rewrite, render_term, rewrite_projection,
};

mod cell_content;
mod local_functions;

#[cfg(test)]
thread_local! {
    /// The equations typed on this thread, which the unit tests read to bound the work.
    static EQUATION_TYPINGS: Cell<usize> = const { Cell::new(0) };
}

use local_functions::{Locals, LoweredLocal};

/// The sorts at one position of a sentence.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PositionTyping {
    /// The sort compilation places the term at the position at, or `None` for syntax that has no
    /// sort (the `#cells` wrapper, `#dots`, `#noDots`) and for a variable nothing types.
    pub sort: Option<Sort>,
    /// The sort the position requires of its term, or `None` where compilation places no sort
    /// requirement (a body without a rewrite, a child of a syntax-only term).
    /// A cast's operand reports the cast's sort, a bound on the operand rather than a placement;
    /// a cell-fragment variable's cast is not in the compiled term, and its operand reports the
    /// requirement of the cast's position.
    pub required: Option<Sort>,
}

/// The typing of a position in the two branches compilation types a body with a rewrite in:
/// the left branch has every rewrite replaced by its left side, the right branch by its right side
/// (and every as-pattern by its alias).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BranchTyping {
    pub left: PositionTyping,
    pub right: PositionTyping,
}

/// The typing of one rule-like sentence, as compilation computes it.
///
/// Paths are those of [`crate::provenance::DestinationAnchor::path`]: the first step selects the
/// sentence field (0 body, 1 requires, 2 ensures), and each further step selects a child: the
/// left (0) or right (1) side of a rewrite, the pattern (0) or alias (1) of an as-pattern, an
/// application's argument (semantic casts included), or a sequence item. Annotations are
/// transparent.
///
/// A path typed identically wherever compilation types it is in `positions`. A path of a body
/// with a rewrite that lies above a rewrite, or is a rewrite, is typed once per branch; when the
/// two typings differ (the rewrite's own node, an application whose instantiation depends on the
/// side), the path is in `branches` instead. A path inside one side of a rewrite, or the pattern
/// of an as-pattern, exists in one branch only and is in `positions`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceTyping {
    pub positions: PathMap<PositionTyping>,
    pub branches: PathMap<BranchTyping>,
    /// The sort of each named variable that semantic-cast resolution determines: in the
    /// enclosing sentence, and for a name only a local function's equation casts, in the first
    /// such equation (each equation is a scope of its own, which may cast a shadowing variable
    /// differently).
    /// A cell-fragment variable has the sort cell concretization gives it instead: the value
    /// sort of the one child it stands for, which it has in the compiled sentence; it has no
    /// entry when it stands for none or several, since concretization replaces it by a fresh
    /// variable per child.
    /// The variable `V` of an alias `P #as V` of one cell has that cell's sort.
    pub variables: BTreeMap<String, Sort>,
    /// The instance injection gives the label of each application of a parametric production,
    /// one entry per sort parameter (`None` where it leaves the parameter open). A path typed
    /// with different instances in the two branches of a rewrite has no entry.
    pub(crate) instances: PathMap<Vec<Option<Sort>>>,
}

/// The paths of one sentence's positions, interned as a trie: node 0 is the empty path, and each
/// other node is its parent's path extended by one step. A walk that descends one step at a
/// time names each position by its node in constant time, so a typing of N positions takes
/// O(N) memory rather than one path, as long as its depth, per position.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PathTrie {
    /// The parent and the last step of each node but the root.
    parents: Vec<(usize, u32)>,
    /// The children of each node, by step, in ascending order of step.
    children: Vec<Vec<(u32, usize)>>,
}

impl PathTrie {
    fn new() -> Self {
        Self {
            parents: vec![(0, 0)],
            children: vec![Vec::new()],
        }
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    /// The node of `node`'s path extended by `step`, added when it is new.
    fn child(&mut self, node: usize, step: u32) -> usize {
        match self.children[node].binary_search_by_key(&step, |(step, _)| *step) {
            Ok(index) => self.children[node][index].1,
            Err(index) => {
                let child = self.children.len();
                self.children.push(Vec::new());
                self.parents.push((node, step));
                self.children[node].insert(index, (step, child));
                child
            }
        }
    }

    fn find_child(&self, node: usize, step: u32) -> Option<usize> {
        self.children[node]
            .binary_search_by_key(&step, |(step, _)| *step)
            .ok()
            .map(|index| self.children[node][index].1)
    }

    fn find(&self, path: &[u32]) -> Option<usize> {
        path.iter()
            .try_fold(0, |node, step| self.find_child(node, *step))
    }

    fn path(&self, mut node: usize) -> Vec<u32> {
        let mut path = Vec::new();
        while node != 0 {
            let (parent, step) = self.parents[node];
            path.push(step);
            node = parent;
        }
        path.reverse();
        path
    }

    /// Every node, each before its descendants and children in ascending order of step: the
    /// order of their paths.
    fn preorder(&self) -> Vec<usize> {
        let mut order = Vec::with_capacity(self.len());
        let mut pending = vec![0];
        while let Some(node) = pending.pop() {
            order.push(node);
            pending.extend(self.children[node].iter().rev().map(|(_, child)| *child));
        }
        order
    }
}

/// A map from the paths of a sentence's positions to values, over a [`PathTrie`] the maps of
/// one typing share. Paths are compared and ordered as the step sequences they are.
#[derive(Clone)]
pub struct PathMap<V> {
    trie: std::sync::Arc<PathTrie>,
    values: Vec<Option<V>>,
    len: usize,
}

impl<V> Default for PathMap<V> {
    fn default() -> Self {
        Self::over(std::sync::Arc::new(PathTrie::new()), Vec::new())
    }
}

impl<V> PathMap<V> {
    /// The map of `values`, indexed by the nodes of `trie`.
    fn over(trie: std::sync::Arc<PathTrie>, mut values: Vec<Option<V>>) -> Self {
        values.resize_with(trie.len(), || None);
        let len = values.iter().filter(|value| value.is_some()).count();
        Self { trie, values, len }
    }

    pub fn get(&self, path: &[u32]) -> Option<&V> {
        self.trie
            .find(path)
            .and_then(|node| self.values[node].as_ref())
    }

    pub fn get_mut(&mut self, path: &[u32]) -> Option<&mut V> {
        self.trie
            .find(path)
            .and_then(|node| self.values[node].as_mut())
    }

    pub fn contains_key(&self, path: &[u32]) -> bool {
        self.get(path).is_some()
    }

    pub fn insert(&mut self, path: Vec<u32>, value: V) -> Option<V> {
        let trie = std::sync::Arc::make_mut(&mut self.trie);
        let node = path.iter().fold(0, |node, step| trie.child(node, *step));
        self.values.resize_with(trie.len(), || None);
        let previous = self.values[node].replace(value);
        self.len += usize::from(previous.is_none());
        previous
    }

    pub fn remove(&mut self, path: &[u32]) -> Option<V> {
        let removed = self
            .trie
            .find(path)
            .and_then(|node| self.values[node].take());
        self.len -= usize::from(removed.is_some());
        removed
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Every path with its value, in the order of the paths.
    pub fn iter(&self) -> impl Iterator<Item = (Vec<u32>, &V)> + '_ {
        self.trie.preorder().into_iter().filter_map(|node| {
            self.values[node]
                .as_ref()
                .map(|value| (self.trie.path(node), value))
        })
    }

    pub fn keys(&self) -> impl Iterator<Item = Vec<u32>> + '_ {
        self.iter().map(|(path, _)| path)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> + '_ {
        self.iter().map(|(_, value)| value)
    }
}

impl<V> Extend<(Vec<u32>, V)> for PathMap<V> {
    fn extend<I: IntoIterator<Item = (Vec<u32>, V)>>(&mut self, entries: I) {
        for (path, value) in entries {
            self.insert(path, value);
        }
    }
}

impl<V> FromIterator<(Vec<u32>, V)> for PathMap<V> {
    fn from_iter<I: IntoIterator<Item = (Vec<u32>, V)>>(entries: I) -> Self {
        let mut map = Self::default();
        map.extend(entries);
        map
    }
}

impl<'a, V> IntoIterator for &'a PathMap<V> {
    type Item = (Vec<u32>, &'a V);
    type IntoIter = Box<dyn Iterator<Item = (Vec<u32>, &'a V)> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}

impl<V: PartialEq> PartialEq for PathMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<V: Eq> Eq for PathMap<V> {}

impl<V: fmt::Debug> fmt::Debug for PathMap<V> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

impl SentenceTyping {
    /// The typing at `path` when it is the same in every branch.
    pub fn at(&self, path: &[u32]) -> Option<&PositionTyping> {
        self.positions.get(path)
    }
}

/// Why a sentence has no typing: the same errors compilation reports for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SentenceTypingError {
    /// The sentence is not a rule or claim.
    NotRuleLike,
    /// The module is not in the definition.
    MissingModule(String),
    /// The variables' sort annotations and casts disagree.
    SemanticCasts(ResolveSemanticCastsError),
    /// A term is ill-sorted at its position, a cast is incomparable with its operand, or a
    /// production cannot be instantiated; `location` is the sentence's `source:line` when known.
    Sort {
        location: Option<String>,
        error: SortInjectionError,
    },
    /// Cell completion rejects the sentence, or completes it in a way the view does not type;
    /// `location` is the sentence's `source:line` when known.
    CellCompletion {
        location: Option<String>,
        message: String,
    },
}

impl fmt::Display for SentenceTypingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotRuleLike => write!(formatter, "only rules and claims have a typing view"),
            Self::MissingModule(module) => write!(formatter, "module {module:?} was not found"),
            Self::SemanticCasts(error) => error.fmt(formatter),
            Self::Sort { location, error } => {
                if let Some(location) = location {
                    write!(formatter, "{location}: ")?;
                }
                error.fmt(formatter)
            }
            Self::CellCompletion { location, message } => {
                if let Some(location) = location {
                    write!(formatter, "{location}: ")?;
                }
                formatter.write_str(message)
            }
        }
    }
}

impl std::error::Error for SentenceTypingError {}

/// The typing of `sentence`, a rule or claim of `module`'s import closure, at the loaded layer,
/// in `module`'s view.
///
/// Equivalent to `SentenceTyper::new(definition, module)?.typing(sentence)`; build a
/// [`SentenceTyper`] once to type several sentences. Compilation's typing of a sentence is its
/// typing in the main module's view ([`SentenceTyper::for_compilation`]).
pub fn sentence_typing(
    definition: &ResolvedDefinition,
    module: &str,
    sentence: &Sentence,
) -> Result<SentenceTyping, SentenceTypingError> {
    SentenceTyper::new(definition, module)?.typing(sentence)
}

/// Types the loaded rule-like sentences of one module's import closure in that module's view.
///
/// Compilation injects every rule-like sentence of the main module's import closure with one
/// injector built for the main module, over the main module's closure. The typer of a module
/// types with the same injector built for that module, over the same closure, and with the
/// productions compilation adds to it before injection for the labels the closure does not
/// declare: the sort predicates and sort and field projections compilation declares over the
/// closure, from the constructors it declares them with, and the rule-language constructs a
/// loaded rule may name (local functions, `:=K` and `:/=K`, the ML connectives, the RULE-CELLS
/// cells). So the typer of the main module ([`SentenceTyper::for_compilation`]) is compilation's
/// typing of every rule and claim of that closure: if compilation accepts the definition, every
/// such sentence the source declares types, and a typing error is an error compilation stops at.
/// A sentence's own module may see fewer sorts, overloads or helpers than the main module, so
/// its typer is not compilation's typing of the sentence.
///
/// A local function (`#fun2`, `#fun3`, `#let`, `:=K`, `:/=K`) is typed as compilation lowers
/// it before it resolves semantic casts and injects: an application, at the generated lambda's
/// result sort, to the value, which is placed at the lambda's parameter sort, plus the lambda's
/// equation, a scope of its own with its own semantic casts, typed as the rule compilation
/// generates. Compilation computes a lambda's sorts with the injector of the module that
/// declares the sentence; [`SentenceTyper::typing_in`] computes them in the module it is given,
/// so `typing_in` with the declaring module is compilation's typing of the sentence, and
/// [`SentenceTyper::typing`] computes them in the typer's module, which is compilation's for the
/// sentences of that module. A typing error that renders the application of a lambda names it
/// `#localFunctionN`, the typer's stand-in for it, where compilation's error names the
/// generated `#lambda…` symbol; the two are the same application.
///
/// The typing is a read of compilation's own computation. Semantic casts are resolved by the
/// resolution pass (its variable sorts and errors), a body with a rewrite is projected into its
/// branches as injection projects it, and every sort and requirement comes from the injector on
/// that resolved and projected term: the sort it places a term at (an upcast's operand sort),
/// a production's instantiated argument sorts (the selected overload,
/// the joint parametric solver), the least upper bound of a rewrite's branches, the sort of an
/// as-pattern's sides, sequence items at `KItem` or `K`, and conditions at `Bool`. Each term is
/// checked at its position with the injector's decision (one injection, the `K` sequence, the
/// sequence injected above `K`, or a collection or user-list wrapper), so a sentence compilation
/// rejects for an ill-sorted term, a cast that is not an upcast, an ambiguous instantiation, or
/// disagreeing variable annotations returns that error here.
///
/// The injector runs after cell concretization, which a loaded sentence has not had; the view
/// keeps the loaded shapes: `#cells`, `#dots` and `#noDots` have no sort and place no
/// requirement, an authored cell `L(#dots|#noDots, body, #dots|#noDots)` has its production's
/// sort and places its body at the cell's single content sort (a body of its child's cell sort
/// at that sort, which concretization places it in, as an instance for a collection).
/// Cell concretization rewrites every occurrence of a cell-fragment variable (a variable
/// without a cell sort written in the body of a cell with children), and the view types each
/// as the term it builds there (`cell_content`): an occurrence in a cell body at the value sort
/// of the one child the variable stands for, and without a sort when it stands for none or
/// several; every other occurrence at the cell's fragment sort (`AccountsCellFragment`).
/// The variable of an alias of one cell has that cell's sort everywhere, as concretization
/// gives it. A sentence with a variable in the body of a cell with children returns the error
/// concretization's analysis stops it at; a sentence with such a cell in a local function's
/// equation, which compilation completes as a rule of its own, is refused, although
/// compilation may accept it. Macro expansion reads instances from the view without these
/// re-sortings (`SentenceTyper::for_macro_expansion`).
/// A function rule with configuration context, `#withConfig(F, C)`, which compilation lowers to
/// `F` with the context as the function's last argument, is typed as that rule: `F` is the rule
/// body, the context `C` is a cell fragment of the left side typed as above, and the construct
/// has no sort and places no requirement. It types in the order injection runs in, where every
/// non-parser sort is declared below `KItem`.
///
/// The view does not infer: a variable nothing types reports no sort, though its position still
/// reports its requirement. A cast's operand reports the cast's sort as its requirement, except
/// a cell-fragment variable's, which compilation replaces with no cast above it: it reports the
/// requirement of the cast's position.
pub struct SentenceTyper<'a> {
    injector: SortInjector<'a, 'a>,
    declared: PartialOrder<Sort>,
    definition: &'a ResolvedDefinition,
    module: ModuleId,
    /// The injector of each module whose sentences' local functions were typed, as
    /// `kompile::passes::resolve_fun` builds it to compute their lambdas' sorts.
    lambda_injectors: std::cell::RefCell<BTreeMap<ModuleId, SortInjector<'a, 'a>>>,
    /// The cell model of each module whose cell model completed a typed sentence
    /// (`kompile::passes::cell_model_module`), or the error building it.
    cell_completions: std::cell::RefCell<BTreeMap<ModuleId, Result<Arc<CellCompletion>, String>>>,
    /// Whether the typings re-sort cell-fragment variables as cell completion builds them
    /// (`cell_content`). Compilation's own typer ([`Self::for_macro_expansion`]) does not, so
    /// the instances macro expansion reads are those of the typing without that step.
    completes_cells: bool,
}

/// The production catalog compilation injects the sentences of `module`'s import closure with,
/// as far as a loaded sentence can name it: the closure's productions, plus the productions of
/// the labels a loaded rule may name that compilation declares or lowers before it injects
/// ([`crate::inner::rule_language_productions`]), each only when the closure has no production
/// of its label.
///
/// The label filter also keeps a typer built on a definition that already declares the sort
/// helpers (macro expansion runs one after the generating passes) from meeting a second one.
fn compilation_catalog<'a>(
    definition: &'a ResolvedDefinition,
    module: ModuleId,
) -> View<'a, ProductionCatalog<'a>> {
    let base = definition.production_catalog(module);
    let added = crate::inner::rule_language_productions(definition, module)
        .into_iter()
        .filter(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => base.productions_for(&LabelHead::from(label)).is_empty(),
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
            | Sentence::Bubble { .. } => false,
        })
        .map(Arc::new)
        .collect::<Vec<_>>();
    let mut sentences = definition.sentence_arcs(module);
    sentences.extend(added);
    View::Owned(ProductionCatalog::from_deduplicated_arcs(
        sentences,
        definition.local_sentence_arcs(module),
    ))
}

impl<'a> SentenceTyper<'a> {
    pub fn new(
        definition: &'a ResolvedDefinition,
        module: &str,
    ) -> Result<Self, SentenceTypingError> {
        let module_id = definition
            .module_id(module)
            .ok_or_else(|| SentenceTypingError::MissingModule(module.to_owned()))?;
        let cycle = |cycle: crate::definition::PartialOrderCycle<Sort>| SentenceTypingError::Sort {
            location: None,
            error: SortInjectionError::CircularSubsort(cycle.path),
        };
        let sorts = definition.sort_catalog(module_id);
        let declared = definition.subsorts(module_id).map_err(cycle)?;
        let subsorts = with_kitem_subsorts(&declared, sorts.all_sorts()).map_err(cycle)?;
        Ok(Self {
            injector: SortInjector {
                productions: compilation_catalog(definition, module_id),
                sorts: View::Owned(sorts),
                subsorts: View::Owned(subsorts),
                next_sort_parameter: Cell::new(0),
                natural_sorts: std::cell::RefCell::default(),
                variable_names: std::cell::RefCell::default(),
                left_aliases: std::cell::RefCell::default(),
            },
            declared,
            definition,
            module: module_id,
            lambda_injectors: std::cell::RefCell::default(),
            cell_completions: std::cell::RefCell::default(),
            completes_cells: true,
        })
    }

    /// The typer macro expansion reads instances from during compilation: [`Self::new`]'s,
    /// without the re-sorting of cell-fragment variables, so that what compilation accepts and
    /// emits does not depend on that view.
    pub(crate) fn for_macro_expansion(
        definition: &'a ResolvedDefinition,
        module: &str,
    ) -> Result<Self, SentenceTypingError> {
        Ok(Self {
            completes_cells: false,
            ..Self::new(definition, module)?
        })
    }

    /// The typer of the definition's main module: compilation's typing of every rule and claim
    /// of the main module's import closure.
    pub fn for_compilation(
        definition: &'a ResolvedDefinition,
    ) -> Result<Self, SentenceTypingError> {
        Self::new(definition, &definition.main_module().name)
    }

    /// The typing of `sentence`, a rule or claim of the typer's module's import closure, with
    /// the lambdas of its local functions computed in the typer's module.
    pub fn typing(&self, sentence: &Sentence) -> Result<SentenceTyping, SentenceTypingError> {
        self.typing_at(sentence, None, self.module)
    }

    /// The typing of `sentence`, a rule or claim of the typer's module's import closure that
    /// `module` declares (or that a caller places there), with the lambdas of its local
    /// functions computed in `module`, as compilation computes them.
    ///
    /// Everything else is typed as [`Self::typing`] types it; the two differ only inside local
    /// functions of a sentence of another module than the typer's.
    pub fn typing_in(
        &self,
        sentence: &Sentence,
        module: &str,
    ) -> Result<SentenceTyping, SentenceTypingError> {
        let module = self
            .definition
            .module_id(module)
            .ok_or_else(|| SentenceTypingError::MissingModule(module.to_owned()))?;
        self.typing_at(sentence, None, module)
    }

    /// `work` with the injector `kompile::passes::resolve_fun` computes the lambdas of
    /// `module`'s local functions with: the productions it types them over
    /// (`kompile::passes::lambda_productions`: the module's import closure and the sort helpers
    /// compilation declares over it), the module's sorts and its declared subsorts; built once
    /// and kept by value, so the typer stays `Send`. `work` must not type a sentence (it holds
    /// the cache borrowed).
    fn with_lambda_injector<T>(
        &self,
        module: ModuleId,
        work: impl FnOnce(&SortInjector<'a, 'a>) -> T,
    ) -> Result<T, SortInjectionError> {
        if !self.lambda_injectors.borrow().contains_key(&module) {
            let subsorts = self
                .definition
                .subsorts(module)
                .map_err(|cycle| SortInjectionError::CircularSubsort(cycle.path))?;
            // The productions `resolve_fun` types the module's lambdas over.
            let productions =
                match crate::kompile::passes::lambda_productions(self.definition, module) {
                    Some(productions) => View::Owned(productions),
                    None => View::Shared(self.definition.production_catalog(module)),
                };
            let injector = SortInjector {
                productions,
                sorts: View::Owned(self.definition.sort_catalog(module)),
                subsorts: View::Owned(subsorts),
                next_sort_parameter: Cell::new(0),
                natural_sorts: std::cell::RefCell::default(),
                variable_names: std::cell::RefCell::default(),
                left_aliases: std::cell::RefCell::default(),
            };
            self.lambda_injectors.borrow_mut().insert(module, injector);
        }
        let injectors = self.lambda_injectors.borrow();
        Ok(work(&injectors[&module]))
    }

    /// Type a ground value at the position from which its emitted instance is inferred.
    pub(crate) fn ground_typing(
        &self,
        term: &Term,
        position: &Sort,
    ) -> Result<SentenceTyping, SentenceTypingError> {
        self.typing_at(
            &Sentence::Rule {
                body: term.clone(),
                requires: Term::Token {
                    token: "true".into(),
                    sort: Sort::builtin(BuiltinSort::Bool),
                },
                ensures: Term::Token {
                    token: "true".into(),
                    sort: Sort::builtin(BuiltinSort::Bool),
                },
                attributes: Attributes::default(),
            },
            Some(position),
            self.module,
        )
    }

    fn typing_at(
        &self,
        sentence: &Sentence,
        top: Option<&Sort>,
        module: ModuleId,
    ) -> Result<SentenceTyping, SentenceTypingError> {
        let (Sentence::Rule {
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
        }) = sentence
        else {
            return Err(SentenceTypingError::NotRuleLike);
        };
        let location =
            sentence
                .attributes()
                .source()
                .map(|source| match sentence.attributes().location() {
                    Some(location) => format!("{source}:{}", location.start_line),
                    None => source.to_owned(),
                });
        crate::definition::checks::reject_label_parameters(sentence).map_err(|error| {
            SentenceTypingError::Sort {
                location: location.clone(),
                error: SortInjectionError::label_parameters(error),
            }
        })?;
        // Compilation lowers local functions before it resolves semantic casts; a sentence with
        // one is split into the scopes the lowering creates, each resolved apart.
        let (variables, resolved, locals) =
            if local_functions::has_local_function([body, requires, ensures]) {
                let lowered = self
                    .with_lambda_injector(module, |injector| {
                        local_functions::lower(sentence, injector, &self.declared)
                    })
                    .map_err(|error| SentenceTypingError::Sort {
                        location: location.clone(),
                        error,
                    })?
                    .map_err(|error| match error {
                        local_functions::LoweringError::Sort(error) => SentenceTypingError::Sort {
                            location: location.clone(),
                            error,
                        },
                        local_functions::LoweringError::Casts(error) => {
                            SentenceTypingError::SemanticCasts(error)
                        }
                    })?;
                (lowered.variables, lowered.sentence, lowered.locals)
            } else {
                let variables = semantic_cast_variable_sorts(sentence, &self.declared)
                    .map_err(SentenceTypingError::SemanticCasts)?;
                let resolved = resolve_semantic_casts_in_sentence(&self.declared, sentence.clone())
                    .map_err(SentenceTypingError::SemanticCasts)?;
                (variables, resolved, Locals::new())
            };
        // Cell completion rewrites the occurrences of each cell-fragment variable; the injector
        // types each as the term completion builds there.
        let (mut variables, mut resolved, mut locals) = (variables, resolved, locals);
        let completed = if self.completes_cells {
            self.complete_cells(&mut resolved, module, &mut locals, location.as_ref())?
        } else {
            cell_content::Completed::default()
        };
        for (name, sort) in &completed.aliases {
            variables.insert(name.clone(), sort.clone());
        }
        for (name, variable) in &completed.variables {
            match variable.parts.as_slice() {
                [part] => {
                    variables.insert(name.clone(), part.clone());
                }
                _ => {
                    variables.remove(name);
                }
            }
        }
        let (Sentence::Rule {
            body: resolved_body,
            requires: resolved_requires,
            ensures: resolved_ensures,
            ..
        }
        | Sentence::Claim {
            body: resolved_body,
            requires: resolved_requires,
            ensures: resolved_ensures,
            ..
        }) = &resolved
        else {
            unreachable!("resolution keeps the sentence kind")
        };
        let typing = self
            .typing_of(
                [body, requires, ensures],
                [resolved_body, resolved_requires, resolved_ensures],
                &locals,
                &completed,
                variables,
                top,
            )
            .map_err(|error| SentenceTypingError::Sort { location, error })?;
        completed.assert_all_looked_up();
        Ok(typing)
    }

    /// Give each occurrence of a cell-fragment or one-cell alias variable of `resolved`, a
    /// resolved sentence of `module`, and of the values its `locals` are applied to, the sort of
    /// the term cell completion builds there ([`cell_content`]); or the error compilation stops
    /// the sentence at there.
    ///
    /// A local function's closure variables are passed to its lambda in the sentence's scope,
    /// so a cell-fragment variable among them is passed as its fragment term, at the lambda's
    /// parameter sort for it: a sort that does not take the fragment sort is the error
    /// injection reports.
    /// Two shapes are refused (`SentenceTypingError::CellCompletion`): a local function written
    /// as an item of a cell body, and a cell with a variable in its body inside a local
    /// function's equation, which compilation completes as a rule of its own and the view does
    /// not.
    fn complete_cells(
        &self,
        resolved: &mut Sentence,
        module: ModuleId,
        locals: &mut Locals,
        location: Option<&String>,
    ) -> Result<cell_content::Completed, SentenceTypingError> {
        let refused = |message: String| SentenceTypingError::CellCompletion {
            location: location.cloned(),
            message,
        };
        let (Sentence::Rule {
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
        }) = &*resolved
        else {
            return Ok(cell_content::Completed::without_cells());
        };
        let mut has_cell = false;
        for root in [body, requires, ensures]
            .into_iter()
            .chain(locals.values().map(|local| &local.argument))
        {
            root.visit_preorder(&mut |term| {
                if let Term::Apply { label, arguments } = term.unannotated() {
                    has_cell |= self.injector.has_production(term, label)
                        && is_authored_cell(&self.injector, term, label, arguments)
                            .unwrap_or(false);
                }
            });
        }
        if !has_cell {
            return Ok(cell_content::Completed::without_cells());
        }
        let model_module = crate::kompile::passes::cell_model_module(self.definition, module);
        let completion = self
            .cell_completions
            .borrow_mut()
            .entry(model_module)
            .or_insert_with(|| CellCompletion::new(self.definition, model_module).map(Arc::new))
            .clone()
            .map_err(refused)?;
        let completed = cell_content::complete(
            resolved,
            locals,
            Arc::clone(&completion),
            self.definition,
            module,
            &self.injector,
        )
        .map_err(refused)?;
        if completed.local_in_body {
            return Err(refused(
                "cell completion cannot place a local function written as an item of the body of a cell with children, where it places only cells and variables"
                    .to_owned(),
            ));
        }
        // The local functions applied in the sentence's own scope: in the sentence, or in the
        // value of one applied there.
        let mut enclosing = std::collections::BTreeSet::new();
        let mut pending = Vec::new();
        for root in cell_content::roots(resolved) {
            root.visit_preorder(&mut |term| {
                if let Term::Variable { name, .. } = term.unannotated()
                    && locals.contains_key(name)
                {
                    pending.push(name.clone());
                }
            });
        }
        // Invariant: `enclosing` holds the stand-ins met so far, and `pending` those whose
        // value is not walked yet; each stand-in enters `enclosing` once.
        while let Some(stand_in) = pending.pop() {
            if !enclosing.insert(stand_in.clone()) {
                continue;
            }
            locals[&stand_in].argument.visit_preorder(&mut |term| {
                if let Term::Variable { name, .. } = term.unannotated()
                    && locals.contains_key(name)
                {
                    pending.push(name.clone());
                }
            });
        }
        for (stand_in, local) in locals.iter() {
            let equation = match &local.equation {
                local_functions::Equation::Split { pattern, body } => vec![pattern, body],
                local_functions::Equation::Whole(term) => vec![term],
            };
            if equation
                .iter()
                .any(|term| cell_content::has_body_variable(term, &completion))
            {
                return Err(refused(
                    "the typing view does not type a cell with a variable in its body inside the equation of a local function, which compilation completes as a rule of its own"
                        .to_owned(),
                ));
            }
            if !enclosing.contains(stand_in.as_str()) {
                continue;
            }
            for closure in &local.closure {
                let Term::Variable { name, sort } = closure.unannotated() else {
                    continue;
                };
                // The term compilation passes for the closure variable, and its sort: a
                // fragment variable's fragment term, or an alias variable at its cell's sort.
                let (term, found) = match (
                    completed.fragment_sorts.get(name),
                    completed.variables.get(name),
                    completed.aliases.get(name),
                ) {
                    (Some(fragment), Some(variable), _) => {
                        (format!("`{}`({name})", variable.fragment.name), fragment)
                    }
                    (_, _, Some(alias)) => (name.clone(), alias),
                    _ => continue,
                };
                let parameter = sort
                    .clone()
                    .unwrap_or_else(|| Sort::builtin(BuiltinSort::K));
                let placed = self
                    .injector
                    .places(closure, found, &parameter)
                    .map_err(|error| SentenceTypingError::Sort {
                        location: location.cloned(),
                        error,
                    })?;
                if !placed {
                    return Err(SentenceTypingError::Sort {
                        location: location.cloned(),
                        error: SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                            term,
                            found: found.clone(),
                            required: parameter,
                        })),
                    });
                }
            }
        }
        Ok(completed)
    }

    fn typing_of(
        &self,
        loaded: [&Term; 3],
        resolved: [&Term; 3],
        locals: &Locals,
        completed: &cell_content::Completed,
        variables: BTreeMap<String, Sort>,
        top: Option<&Sort>,
    ) -> Result<SentenceTyping, SortInjectionError> {
        let injector = &self.injector;
        injector.next_sort_parameter.set(0);
        // Every term the walks type is a node of `resolved` or of a local function's parts in
        // `locals`, or a projection built for one and typed outside the memo, so the injector's
        // sort memo holds for the whole typing.
        injector
            .memoized(|| self.typing_with_memo(loaded, resolved, locals, completed, variables, top))
    }

    fn typing_with_memo(
        &self,
        loaded: [&Term; 3],
        resolved: [&Term; 3],
        locals: &Locals,
        completed: &cell_content::Completed,
        variables: BTreeMap<String, Sort>,
        top: Option<&Sort>,
    ) -> Result<SentenceTyping, SortInjectionError> {
        let injector = &self.injector;
        let top = top
            .cloned()
            .unwrap_or_else(|| injector.fresh_sort_parameter());
        let boolean = Sort::builtin(BuiltinSort::Bool);
        let mut trie = PathTrie::new();
        let projections = Projections::of(resolved[0]);
        // A function rule with configuration context, `#withConfig(F, C)`, is rule structure:
        // the function rule `F` is the rule body compilation injects (the lowering only adds the
        // context as the function's last argument), and the context `C` is a cell fragment of
        // the left side.
        let with_config = match (
            FunctionRuleWithContext::of(loaded[0]),
            FunctionRuleWithContext::of(resolved[0]),
        ) {
            (Some(Ok(loaded)), Some(Ok(resolved))) => Some((loaded, resolved)),
            _ => None,
        };
        let (body_loaded, body_resolved) = match &with_config {
            Some((loaded, resolved)) => (loaded.rule, resolved.rule),
            None => (loaded[0], resolved[0]),
        };

        let mut conditions = Walk::new(
            injector,
            Branch::Only,
            &mut trie,
            &projections,
            locals,
            completed,
        );
        for (field, loaded, resolved) in
            [(1u32, loaded[1], resolved[1]), (2, loaded[2], resolved[2])]
        {
            let mut path = Cursor::root();
            path.push(conditions.trie, field);
            let slot = conditions.visit(loaded, resolved, &mut path, &boolean)?;
            conditions.place(&path, &slot, &boolean)?;
        }
        if let Some((loaded, resolved)) = &with_config {
            // The construct has no sort and places no requirement. The context is typed as an
            // authored cell or `#cells` fragment is, as a pattern, so a single cell reports its
            // cell's sort and a `#cells` fragment none.
            let mut path = Cursor::root();
            path.push(conditions.trie, 0);
            conditions.record(&path, None);
            conditions.child_with(
                (false, true),
                loaded.context,
                resolved.context,
                &mut path,
                1,
                &Sort::builtin(BuiltinSort::KItem),
            )?;
        }
        let (mut positions, mut instances, mut walk_branches) = conditions.finish();
        // As `inject_rule_body`: a body with a rewrite is the rewrite of its two projections,
        // typed at their least upper bound below the top hint, and each projection is
        // injected at that bound; a body without one is typed below the top hint and
        // injected at its own sort. The body's sort comes from a first walk (the injector's
        // `term_sort` cannot type loaded cell fragments), and the second walk types the body at
        // the position injection places it at.
        let branches: &[Branch] = if has_rewrite(body_resolved) {
            &[Branch::Left, Branch::Right]
        } else {
            &[Branch::Only]
        };
        let body = |trie: &mut PathTrie| {
            let mut path = Cursor::root();
            path.push(trie, 0);
            if with_config.is_some() {
                path.push(trie, 0);
            }
            path
        };
        let mut sorts = Vec::new();
        for branch in branches {
            let mut walk = Walk::new(
                injector,
                *branch,
                &mut trie,
                &projections,
                locals,
                completed,
            );
            walk.types_equations = false;
            let mut path = body(walk.trie);
            sorts.extend(
                walk.visit(body_loaded, body_resolved, &mut path, &top)?
                    .sort,
            );
        }
        let position = match branches {
            [Branch::Only] => sorts.first().cloned(),
            _ if sorts.is_empty() => None,
            _ => Some(injector.least_upper_bound(&sorts, Some(&top))?),
        };
        let mut maps = Vec::new();
        let mut branch_instances = Vec::new();
        for branch in branches {
            let mut walk = Walk::new(
                injector,
                *branch,
                &mut trie,
                &projections,
                locals,
                completed,
            );
            let mut path = body(walk.trie);
            let hint = position.clone().unwrap_or_else(|| top.clone());
            let slot = walk.visit(body_loaded, body_resolved, &mut path, &hint)?;
            if *branch != Branch::Only
                && let Some(position) = &position
            {
                walk.place(&path, &slot, position)?;
            }
            let (positions, instances, branches) = walk.finish();
            maps.push(positions);
            branch_instances.push(instances);
            merge_into(&mut walk_branches, branches);
        }
        // The walks name positions by the nodes of one trie, so the branches' typings of a
        // position are merged by node.
        let mut branches = walk_branches;
        let first = maps.remove(0);
        match maps.pop() {
            None => merge_into(&mut positions, first),
            Some(right) => merge_sides(first, right, &mut positions, &mut branches),
        }
        let first = branch_instances.remove(0);
        match branch_instances.pop() {
            None => merge_into(&mut instances, first),
            Some(right) => {
                let mut left = first;
                for (node, right) in right.into_iter().enumerate() {
                    let Some(right) = right else {
                        continue;
                    };
                    match left.get_mut(node).and_then(Option::take) {
                        Some(left) if left != right => {}
                        _ => set(&mut instances, node, right),
                    }
                }
                merge_into(&mut instances, left);
            }
        }
        let trie = std::sync::Arc::new(trie);
        Ok(SentenceTyping {
            positions: PathMap::over(std::sync::Arc::clone(&trie), positions),
            branches: PathMap::over(std::sync::Arc::clone(&trie), branches),
            variables,
            instances: PathMap::over(trie, instances),
        })
    }
}

/// Values by trie node.
type NodeValues<V> = Vec<Option<V>>;

/// What a walk types: positions, instances, and the equation positions typed per side.
type WalkTyping = (
    NodeValues<PositionTyping>,
    NodeValues<Vec<Option<Sort>>>,
    NodeValues<BranchTyping>,
);

fn set<V>(values: &mut NodeValues<V>, node: usize, value: V) {
    if values.len() <= node {
        values.resize_with(node + 1, || None);
    }
    values[node] = Some(value);
}

/// Merge the typings of two walks of one term, a left and a right side, into `positions` where
/// they agree and into `branches` where they differ.
fn merge_sides(
    mut left: NodeValues<PositionTyping>,
    right: NodeValues<PositionTyping>,
    positions: &mut NodeValues<PositionTyping>,
    branches: &mut NodeValues<BranchTyping>,
) {
    // Invariant: every node before `node` that the right walk typed is in `positions` or
    // `branches`, and taken from `left`; each iteration consumes one node.
    for (node, right) in right.into_iter().enumerate() {
        let Some(right) = right else {
            continue;
        };
        match left.get_mut(node).and_then(Option::take) {
            Some(left) if left == right => set(positions, node, left),
            Some(left) => set(branches, node, BranchTyping { left, right }),
            None => set(positions, node, right),
        }
    }
    merge_into(positions, left);
}

/// Add each value of `from` to `into` at its node.
fn merge_into<V>(into: &mut NodeValues<V>, from: NodeValues<V>) {
    for (node, value) in from.into_iter().enumerate() {
        if let Some(value) = value {
            set(into, node, value);
        }
    }
}

/// The current path of a walk, as the trie nodes of its prefixes.
#[derive(Clone)]
struct Cursor {
    nodes: Vec<usize>,
}

impl Cursor {
    fn root() -> Self {
        Self { nodes: vec![0] }
    }

    fn node(&self) -> usize {
        *self.nodes.last().expect("a cursor holds the root")
    }

    fn push(&mut self, trie: &mut PathTrie, step: u32) {
        let node = trie.child(self.node(), step);
        self.nodes.push(node);
    }

    fn pop(&mut self) {
        self.nodes.pop();
    }
}

/// The nodes of a rule body under which the rewrite projection changes something: those that
/// are or contain a rewrite (both branches), and those that are or contain an as-pattern (the
/// right branch, which keeps an as-pattern's alias). A node outside them is its own projection,
/// so the walk types it in place rather than on a copy. Nodes are named by address; the body is
/// borrowed for the whole typing.
struct Projections {
    rewrites: std::collections::HashSet<usize>,
    rewrites_or_aliases: std::collections::HashSet<usize>,
}

impl Projections {
    fn of(body: &Term) -> Self {
        let mut rewrites = std::collections::HashSet::new();
        let mut rewrites_or_aliases = std::collections::HashSet::new();
        // Post-order with an explicit stack: a node is visited after its children.
        let mut pending = vec![(body, false)];
        let mut flags: Vec<(bool, bool)> = Vec::new();
        // Invariant: `flags` holds, for each child of a node whose children were all visited,
        // whether it contains a rewrite and whether it contains a rewrite or an as-pattern.
        while let Some((term, visited)) = pending.pop() {
            let children = immediate_children(term);
            if !visited {
                pending.push((term, true));
                pending.extend(children.iter().rev().map(|child| (*child, false)));
                continue;
            }
            let mut rewrite = matches!(term, Term::Rewrite { .. });
            let mut either = rewrite || matches!(term, Term::As { .. });
            for (child_rewrite, child_either) in flags.split_off(flags.len() - children.len()) {
                rewrite |= child_rewrite;
                either |= child_either;
            }
            let address = std::ptr::from_ref(term) as usize;
            if rewrite {
                rewrites.insert(address);
            }
            if either {
                rewrites_or_aliases.insert(address);
            }
            flags.push((rewrite, either));
        }
        Self {
            rewrites,
            rewrites_or_aliases,
        }
    }

    /// Whether projecting `term`, a node of the body, for the branch `right` selects changes it.
    fn changes(&self, term: &Term, right: bool) -> bool {
        let address = std::ptr::from_ref(term) as usize;
        if right {
            self.rewrites_or_aliases.contains(&address)
        } else {
            self.rewrites.contains(&address)
        }
    }
}

/// The direct subterms of `term`, an annotation's term included.
fn immediate_children(term: &Term) -> Vec<&Term> {
    match term {
        Term::Annotated { term, .. } => vec![term],
        Term::Rewrite { left, right } => vec![left, right],
        Term::As { pattern, alias } => vec![pattern, alias],
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
    }
}

/// Which projection of the body a walk types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Branch {
    /// A condition, or a body without a rewrite.
    Only,
    Left,
    Right,
}

/// The term occupying a position in compilation, and the sort injection places it at.
struct Slot<'r> {
    /// The resolved and projected term at the position: the resolved node itself where the
    /// projection leaves it unchanged, else its projection.
    term: Cow<'r, Term>,
    /// The sort injection places it at; `None` for syntax without a sort.
    sort: Option<Sort>,
}

struct Walk<'a, 'view, 'definition, 't> {
    injector: &'a SortInjector<'view, 'definition>,
    branch: Branch,
    /// The paths of the typing's positions; the walk's values are indexed by its nodes.
    trie: &'t mut PathTrie,
    projections: &'t Projections,
    /// The sentence's local functions, by the stand-in variable that replaces each in the
    /// resolved terms.
    locals: &'t Locals,
    /// The occurrences of cell-fragment variables cell completion re-sorts.
    completed: &'t cell_content::Completed,
    positions: NodeValues<PositionTyping>,
    instances: NodeValues<Vec<Option<Sort>>>,
    /// The positions of a local function's equation that its two sides type differently.
    branches: NodeValues<BranchTyping>,
    /// Whether the local functions the walk meets have their equations typed; a walk whose
    /// positions are discarded (it computes a sort) skips them.
    types_equations: bool,
    /// Positions whose term occupies an enclosing position's slot (a rewrite's side in a branch,
    /// an as-pattern's alias in the right branch, the operand of a cast the projection drops):
    /// the enclosing requirement applies to them. Inner pairs come first.
    delegates: Vec<(usize, usize)>,
    /// Whether the terms being visited are still projected. `rewrite_projection` copies the
    /// left side of a rewrite as it is, so inside a left side nothing is projected; it projects
    /// a right side recursively.
    projecting: bool,
    /// Whether the terms being visited are injected as a left-hand side, as `visit_children`
    /// tracks it (sequence items then take `KItem` as their context).
    is_lhs: bool,
}

impl<'a, 'view, 'definition, 't> Walk<'a, 'view, 'definition, 't> {
    fn new(
        injector: &'a SortInjector<'view, 'definition>,
        branch: Branch,
        trie: &'t mut PathTrie,
        projections: &'t Projections,
        locals: &'t Locals,
        completed: &'t cell_content::Completed,
    ) -> Self {
        Self {
            injector,
            branch,
            trie,
            projections,
            locals,
            completed,
            positions: Vec::new(),
            instances: Vec::new(),
            branches: Vec::new(),
            types_equations: true,
            delegates: Vec::new(),
            projecting: branch != Branch::Only,
            is_lhs: branch == Branch::Left,
        }
    }

    /// Visit a child with `(projecting, is_lhs)` set to `mode` for it, restoring them afterwards.
    fn child_with<'r>(
        &mut self,
        mode: (bool, bool),
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        index: usize,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let saved = (self.projecting, self.is_lhs);
        (self.projecting, self.is_lhs) = mode;
        let slot = self.child(loaded, resolved, path, index, hint);
        (self.projecting, self.is_lhs) = saved;
        slot
    }

    fn finish(mut self) -> WalkTyping {
        for (from, to) in std::mem::take(&mut self.delegates).into_iter().rev() {
            let required = self
                .position(from)
                .and_then(|position| position.required.clone());
            if let Some(position) = self.position_mut(to) {
                position.required = required;
            }
        }
        (self.positions, self.instances, self.branches)
    }

    /// A local function, whose resolved form is the stand-in variable `resolved` of
    /// `lowered`, typed as compilation lowers it: an application of the lambda, at the lambda's
    /// result sort, to the value, placed at the lambda's parameter sort; and the lambda's
    /// equation, typed as the rule compilation generates.
    fn local_function<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        hint: &Sort,
        lowered: &'t LoweredLocal,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let Term::Apply { arguments, .. } = loaded.unannotated() else {
            unreachable!("a local function is an application")
        };
        let LambdaSorts { parameter, result } = &lowered.sorts;
        // A semantic cast on the construct annotates its stand-in, a term of the lambda's result
        // sort: the injector checks the cast against that sort, as it checks a cast on the
        // lambda's application.
        let injector = self.injector;
        self.infer(&Cow::Borrowed(resolved), |term| {
            injector.term_sort(term, Some(hint))
        })?;
        self.record(path, reported(result));
        let index = lowered.local.argument_index();
        let slot = self.child(&arguments[index], &lowered.argument, path, index, parameter)?;
        self.place_child(path, index, &slot, parameter)?;
        if self.types_equations {
            self.equation(arguments, lowered, path)?;
        }
        Ok(Slot {
            term: Cow::Borrowed(resolved),
            sort: Some(result.clone()),
        })
    }

    /// The generated equation `lambda(P, C1..Cn) => B` of the local function at `path`, whose
    /// arguments are `arguments`, typed as injection types that rule: the left side is the
    /// lambda's application, at its result sort, whose argument `P` is placed at the parameter
    /// sort; the body `B` is typed below the rule's top sort and both sides are placed at their
    /// least upper bound. A `#fun3` or `#let` holds `P` and `B` in arguments of their own; a
    /// `#fun2` holds them as the left and right projections of its first argument, which is
    /// typed by a left and a right walk, its positions reported per side where these differ;
    /// a match's equation is its pattern alone.
    ///
    /// The walks that only compute the body's sort do not type the equations below it, so each
    /// equation is typed once per placement walk that reaches its construct.
    fn equation(
        &mut self,
        arguments: &[Term],
        lowered: &'t LoweredLocal,
        path: &Cursor,
    ) -> Result<(), SortInjectionError> {
        #[cfg(test)]
        EQUATION_TYPINGS.with(|count| count.set(count.get() + 1));
        let injector = self.injector;
        let locals = self.locals;
        let LambdaSorts { parameter, result } = &lowered.sorts;
        let extend = |trie: &mut PathTrie, steps: &[u32]| {
            let mut cursor = path.clone();
            for step in steps {
                cursor.push(trie, *step);
            }
            cursor
        };
        // (loaded pattern, resolved pattern, its steps; the same of the body; the projections
        // and branches the two sides are walked with).
        let (pattern, body, projections, sides) =
            match (&lowered.equation, lowered.local.split_parts(arguments)) {
                (
                    local_functions::Equation::Split { pattern, body },
                    Some(((loaded_pattern, pattern_steps), (loaded_body, body_steps))),
                ) => (
                    (loaded_pattern, pattern, pattern_steps),
                    Some((loaded_body, body, body_steps)),
                    Projections::of(body),
                    (Branch::Only, Branch::Only),
                ),
                (local_functions::Equation::Whole(equation), None) => (
                    (&arguments[0], equation, vec![0]),
                    (!lowered.local.is_predicate()).then(|| (&arguments[0], equation, vec![0])),
                    Projections::of(equation),
                    (Branch::Left, Branch::Right),
                ),
                _ => unreachable!("the lowering and the construct agree on its form"),
            };
        let mut walk = Walk::new(
            injector,
            sides.0,
            &mut *self.trie,
            &projections,
            locals,
            self.completed,
        );
        walk.is_lhs = true;
        let mut cursor = extend(walk.trie, &pattern.2);
        let slot = walk.visit(pattern.0, pattern.1, &mut cursor, parameter)?;
        walk.place(&cursor, &slot, parameter)?;
        let (left, instances, branches) = walk.finish();
        merge_into(&mut self.instances, instances);
        merge_into(&mut self.branches, branches);
        let Some((loaded_body, resolved_body, body_steps)) = body else {
            merge_into(&mut self.positions, left);
            return Ok(());
        };
        let top = injector.fresh_sort_parameter();
        let sort = {
            let mut walk = Walk::new(
                injector,
                sides.1,
                &mut *self.trie,
                &projections,
                locals,
                self.completed,
            );
            walk.types_equations = false;
            let mut cursor = extend(walk.trie, &body_steps);
            walk.visit(loaded_body, resolved_body, &mut cursor, &top)?
                .sort
        };
        let mut sorts = vec![result.clone()];
        sorts.extend(sort);
        let position = injector.least_upper_bound(&sorts, Some(&top))?;
        let mut walk = Walk::new(
            injector,
            sides.1,
            &mut *self.trie,
            &projections,
            locals,
            self.completed,
        );
        let mut cursor = extend(walk.trie, &body_steps);
        let slot = walk.visit(loaded_body, resolved_body, &mut cursor, &position)?;
        walk.place(&cursor, &slot, &position)?;
        let (right, instances, branches) = walk.finish();
        merge_into(&mut self.instances, instances);
        merge_into(&mut self.branches, branches);
        merge_sides(left, right, &mut self.positions, &mut self.branches);
        Ok(())
    }

    fn position(&self, node: usize) -> Option<&PositionTyping> {
        self.positions.get(node).and_then(Option::as_ref)
    }

    fn position_mut(&mut self, node: usize) -> Option<&mut PositionTyping> {
        self.positions.get_mut(node).and_then(Option::as_mut)
    }

    /// Run `work`, an inference of the injector over `term`, with the injector's sort memo
    /// suspended when `term` is a projection built for the walk rather than a node of the
    /// resolved sentence.
    #[expect(
        clippy::ptr_arg,
        reason = "whether the term is borrowed from the sentence decides the memo"
    )]
    fn infer<T>(&self, term: &Cow<'_, Term>, work: impl FnOnce(&Term) -> T) -> T {
        match term {
            Cow::Borrowed(term) => work(term),
            Cow::Owned(term) => self.injector.unmemoized(|| work(term)),
        }
    }

    /// The term compilation sees at a position: `resolved` with the walk's projection applied,
    /// which is `resolved` itself unless a rewrite (or, in the right branch, an as-pattern) lies
    /// within it.
    fn projected<'r>(&self, resolved: &'r Term) -> Cow<'r, Term> {
        let right = self.branch == Branch::Right;
        if self.projecting && self.projections.changes(resolved, right) {
            Cow::Owned(rewrite_projection(resolved, right, &self.injector.subsorts))
        } else {
            Cow::Borrowed(resolved)
        }
    }

    /// Record `required` at `path` and reject the slot's term unless compilation places it there.
    fn place(
        &mut self,
        path: &Cursor,
        slot: &Slot<'_>,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        if let Some(position) = self.position_mut(path.node()) {
            position.required = reported(required);
        }
        let Some(sort) = &slot.sort else {
            return Ok(());
        };
        if self.infer(&slot.term, |term| {
            self.injector.places(term, sort, required)
        })? {
            Ok(())
        } else {
            Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(&slot.term),
                found: sort.clone(),
                required: required.clone(),
            })))
        }
    }

    fn child<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        index: usize,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        path.push(self.trie, step(index));
        let slot = self.visit(loaded, resolved, path, hint);
        path.pop();
        slot
    }

    fn place_child(
        &mut self,
        path: &mut Cursor,
        index: usize,
        slot: &Slot<'_>,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        path.push(self.trie, step(index));
        let placed = self.place(path, slot, required);
        path.pop();
        placed
    }

    fn delegate(&mut self, path: &Cursor, index: usize) {
        let to = self.trie.child(path.node(), step(index));
        self.delegates.push((path.node(), to));
    }

    fn record(&mut self, path: &Cursor, sort: Option<Sort>) {
        let node = path.node();
        if self.positions.len() <= node {
            self.positions.resize_with(node + 1, || None);
        }
        self.positions[node].get_or_insert_default().sort = sort;
    }

    /// Type the loaded term at `path`, whose resolved form (semantic casts replaced by sort
    /// metadata) is `resolved`, at a position of sort `hint`, and every subterm.
    // Invariant: each call records `path` and recurses only into the direct subterms of `loaded` (and the corresponding subterms of `resolved`), extending `path` by one step; the depth of `loaded` bounds the recursion.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    fn visit<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        self.record(path, None);
        // In a debug build, every node is looked up, so a re-sorted node the walk does not meet
        // at its recorded address is caught (`Completed::assert_all_looked_up`).
        #[cfg(debug_assertions)]
        self.completed.contains(resolved);
        if let Term::Variable { name, .. } = resolved.unannotated()
            && let Some(lowered) = self.locals.get(name)
            && let Term::Apply { label, arguments } = loaded.unannotated()
            && matches!(LocalFunction::of(label, arguments.len()), Some(Ok(_)))
        {
            return self.local_function(loaded, resolved, path, hint, lowered);
        }
        match loaded.unannotated() {
            Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
                let target = label.semantic_cast_sort().expect("a semantic cast");
                let [argument] = arguments.as_slice() else {
                    return Err(SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: arguments.len(),
                    });
                };
                // Resolution replaced the cast by its operand, which occupies this position.
                let slot = self.child(argument, resolved, path, 0, hint)?;
                let dropped = self.projecting
                    && matches!(
                        (argument.unannotated(), self.branch),
                        (Term::Rewrite { .. }, _) | (Term::As { .. }, Branch::Right)
                    );
                if dropped || self.completed.contains(resolved) {
                    // The projection removes the rewrite or as-pattern the cast annotates, and
                    // the cast's own position with it (resolution put a rewrite's cast on each
                    // side, which occupies the cast's position). Cell completion replaces a
                    // cell-fragment variable by a term of its own sort, and the compiled term
                    // has no cast there either.
                    self.delegate(path, 0);
                } else if let Some(operand) = self.trie.find_child(path.node(), 0)
                    && let Some(position) = self.position_mut(operand)
                {
                    position.required = reported(&target);
                }
                self.record(path, slot.sort.as_ref().and_then(reported));
                Ok(slot)
            }
            Term::Rewrite { left, right } if self.projecting => {
                let (index, side, resolved_side) = match (self.branch, resolved.unannotated()) {
                    (Branch::Left, Term::Rewrite { left: resolved, .. }) => (0, left, resolved),
                    (
                        _,
                        Term::Rewrite {
                            right: resolved, ..
                        },
                    ) => (1, right, resolved),
                    _ => unreachable!("resolution keeps rewrites"),
                };
                // The projection keeps a left side as it is and projects a right side further.
                let projecting = index == 1;
                let is_lhs = self.is_lhs;
                let slot =
                    self.child_with((projecting, is_lhs), side, resolved_side, path, index, hint)?;
                self.delegate(path, index);
                self.record(path, slot.sort.as_ref().and_then(reported));
                Ok(slot)
            }
            Term::As { alias, .. } if self.projecting && self.branch == Branch::Right => {
                let Term::As {
                    alias: resolved_alias,
                    ..
                } = resolved.unannotated()
                else {
                    unreachable!("resolution keeps as-patterns")
                };
                let slot = self.child(alias, resolved_alias, path, 1, hint)?;
                self.delegate(path, 1);
                self.record(path, slot.sort.as_ref().and_then(reported));
                Ok(slot)
            }
            Term::Apply { label, arguments }
                if label.is(InternalLabel::Cells)
                    || label.is(InternalLabel::Dots)
                    || label.is(InternalLabel::NoDots) =>
            {
                let Term::Apply {
                    arguments: resolved_arguments,
                    ..
                } = resolved.unannotated()
                else {
                    unreachable!("resolution keeps applications")
                };
                let k_item = Sort::builtin(BuiltinSort::KItem);
                for (index, (argument, resolved)) in
                    arguments.iter().zip(resolved_arguments).enumerate()
                {
                    self.child(argument, resolved, path, index, &k_item)?;
                }
                Ok(Slot {
                    term: self.projected(resolved),
                    sort: None,
                })
            }
            Term::Apply { label, arguments }
                if self.injector.has_production(loaded, label)
                    && is_authored_cell(self.injector, loaded, label, arguments)? =>
            {
                self.authored_cell(loaded, resolved, path)
            }
            Term::As { pattern, alias }
                if self.completed.active && self.is_authored_cell(pattern)? =>
            {
                // `<c> .. </c> #as V`: the pattern is typed as an authored cell, and the alias,
                // which completion gives that cell's sort, is placed at it.
                let Term::As {
                    pattern: resolved_pattern,
                    alias: resolved_alias,
                } = resolved.unannotated()
                else {
                    unreachable!("resolution keeps as-patterns")
                };
                let slot = self.child(pattern, resolved_pattern, path, 0, hint)?;
                let sort = slot
                    .sort
                    .clone()
                    .expect("an authored cell has its cell's sort");
                // The left projection keeps an as-pattern's alias as it is.
                let (projecting, is_lhs) =
                    (self.projecting && self.branch != Branch::Left, self.is_lhs);
                let alias_slot =
                    self.child_with((projecting, is_lhs), alias, resolved_alias, path, 1, &sort)?;
                self.place_child(path, 1, &alias_slot, &sort)?;
                self.record(path, reported(&sort));
                Ok(Slot {
                    term: self.projected(resolved),
                    sort: Some(sort),
                })
            }
            _ => self.injected(loaded, resolved, path, hint),
        }
    }

    /// A term the injector types directly: `inject_with_position`'s sort for it at a position of
    /// sort `hint`, and `visit_children`'s placement of its children.
    fn injected<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let injector = self.injector;
        let term = self.projected(resolved);
        if matches!(resolved.unannotated(), Term::Variable { sort: None, .. })
            && self.completed.contains(resolved)
        {
            // Cell completion writes no one term here (the variable's parts, or nothing), so
            // nothing is placed.
            self.record(path, None);
            return Ok(Slot { term, sort: None });
        }
        let sort = self.infer(&term, |term| injector.term_sort(term, Some(hint)))?;
        let (children_of, actual) = (&term, sort.clone());
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is not a sentence kind; only the listed variants are special here"
        )]
        let reported_sort = match term.unannotated() {
            Term::Variable { sort: None, .. } => None,
            _ => reported(&sort),
        };
        self.record(path, reported_sort);
        match (loaded.unannotated(), resolved.unannotated()) {
            (
                Term::Apply { arguments, .. },
                Term::Apply {
                    arguments: resolved_arguments,
                    ..
                },
            ) => {
                let Term::Apply {
                    label,
                    arguments: projected_arguments,
                } = children_of.unannotated()
                else {
                    unreachable!("projection keeps applications")
                };
                let signature = self.infer(children_of, |children_of| {
                    injector.signature(
                        children_of,
                        label,
                        projected_arguments,
                        Some(&actual),
                        false,
                    )
                })?;
                if !signature.label.parameters.is_empty() {
                    set(
                        &mut self.instances,
                        path.node(),
                        signature.label.parameters.iter().map(reported).collect(),
                    );
                }
                for (index, ((argument, resolved), required)) in arguments
                    .iter()
                    .zip(resolved_arguments)
                    .zip(&signature.arguments)
                    .enumerate()
                {
                    let slot = self.child(argument, resolved, path, index, required)?;
                    self.place_child(path, index, &slot, required)?;
                }
            }
            (
                Term::Rewrite { left, right },
                Term::Rewrite {
                    left: resolved_left,
                    right: resolved_right,
                },
            ) => {
                for (index, (side, resolved)) in [(left, resolved_left), (right, resolved_right)]
                    .into_iter()
                    .enumerate()
                {
                    // A rewrite the projection keeps: `visit_children` injects its left side as
                    // a left-hand side and its right side as a right-hand side.
                    let projecting = self.projecting;
                    let slot = self.child_with(
                        (projecting, index == 0),
                        side,
                        resolved,
                        path,
                        index,
                        &actual,
                    )?;
                    self.place_child(path, index, &slot, &actual)?;
                }
            }
            (
                Term::As { pattern, alias },
                Term::As {
                    pattern: resolved_pattern,
                    alias: resolved_alias,
                },
            ) => {
                // Both sides are placed at the as-pattern's sort (a cast on the as-pattern fixes
                // it); a sortless alias takes that sort, a sorted one must fit it.
                let slot = self.child(pattern, resolved_pattern, path, 0, &actual)?;
                self.place_child(path, 0, &slot, &actual)?;
                // The left projection keeps an as-pattern's alias as it is.
                let (projecting, is_lhs) =
                    (self.projecting && self.branch != Branch::Left, self.is_lhs);
                let slot = self.child_with(
                    (projecting, is_lhs),
                    alias,
                    resolved_alias,
                    path,
                    1,
                    &actual,
                )?;
                self.place_child(path, 1, &slot, &actual)?;
            }
            (Term::Sequence(items), Term::Sequence(resolved_items)) => {
                let context = if self.is_lhs {
                    Sort::builtin(BuiltinSort::KItem)
                } else {
                    Sort::builtin(BuiltinSort::K)
                };
                for (index, (item, resolved)) in items.iter().zip(resolved_items).enumerate() {
                    let projected_item = self.projected(resolved);
                    let item_sort = self.infer(&projected_item, |item| {
                        injector.term_sort(item, Some(&context))
                    })?;
                    let required = if item_sort.is_builtin(BuiltinSort::K) {
                        Sort::builtin(BuiltinSort::K)
                    } else {
                        Sort::builtin(BuiltinSort::KItem)
                    };
                    let slot = self.child(item, resolved, path, index, &required)?;
                    self.place_child(path, index, &slot, &required)?;
                }
            }
            _ => {}
        }
        Ok(Slot {
            term,
            sort: Some(sort),
        })
    }

    /// Whether `term`, a loaded term, is an authored cell.
    fn is_authored_cell(&self, term: &Term) -> Result<bool, SortInjectionError> {
        let Term::Apply { label, arguments } = term.unannotated() else {
            return Ok(false);
        };
        Ok(self.injector.has_production(term, label)
            && is_authored_cell(self.injector, term, label, arguments)?)
    }

    /// An authored cell `L(#dots|#noDots, body, #dots|#noDots)`: the markers have no sort, and the
    /// body is placed at the cell's single content sort when it has one, or, when it is a term of
    /// the cell sort of the cell's child, at that sort: completion places it in that child,
    /// building a collection's element for an instance of a `multiplicity="*"` child.
    fn authored_cell<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let injector = self.injector;
        let (
            Term::Apply { label, arguments },
            Term::Apply {
                arguments: resolved_arguments,
                ..
            },
        ) = (loaded.unannotated(), resolved.unannotated())
        else {
            unreachable!("authored cells are applications")
        };
        let Sentence::Production { sort, items, .. } = injector.production(loaded, label)? else {
            unreachable!("the production catalog holds productions")
        };
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
        )]
        let children = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let content = match children.as_slice() {
            [content] => Some(content.clone()),
            _ => None,
        };
        let k_item = Sort::builtin(BuiltinSort::KItem);
        self.child(&arguments[0], &resolved_arguments[0], path, 0, &k_item)?;
        let body_hint = content.clone().unwrap_or_else(|| k_item.clone());
        let body = self.child(&arguments[1], &resolved_arguments[1], path, 1, &body_hint)?;
        if let Some(content) = &content {
            // Completion places a term of a child's cell sort in that child: in a collection's
            // child, as an instance, which it builds the collection's element of.
            let required = match &body.sort {
                Some(sort)
                    if self
                        .completed
                        .completion
                        .as_ref()
                        .is_some_and(|completion| completion.is_child(label, sort)) =>
                {
                    sort
                }
                Some(_) | None => content,
            };
            self.place_child(path, 1, &body, required)?;
        }
        self.child(&arguments[2], &resolved_arguments[2], path, 2, &k_item)?;
        self.record(path, reported(sort));
        Ok(Slot {
            term: self.projected(resolved),
            sort: Some(sort.clone()),
        })
    }
}

impl SortInjector<'_, '_> {
    /// Whether injection places a term of sort `actual` at a position of sort `expected`: the
    /// decision `inject_with_position` makes, wrappers included.
    fn places(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
    ) -> Result<bool, SortInjectionError> {
        if actual == expected || self.below(actual, expected) {
            return Ok(true);
        }
        Ok(self
            .collection_wrapper(term, actual, expected, term.clone(), false)?
            .is_ok()
            || self
                .user_list_wrapper(actual, expected, term.clone())
                .is_ok())
    }
}

fn step(index: usize) -> u32 {
    u32::try_from(index).expect("a term has fewer than 2^32 children")
}

fn is_authored_cell(
    injector: &SortInjector<'_, '_>,
    term: &Term,
    label: &crate::kast::Label,
    arguments: &[Term],
) -> Result<bool, SortInjectionError> {
    let Sentence::Production { attributes, .. } = injector.production(term, label)? else {
        return Ok(false);
    };
    Ok(attributes.has(AttributeKey::Cell)
        && matches!(arguments, [left, _, right] if is_dots_marker(left) && is_dots_marker(right)))
}

fn is_dots_marker(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, arguments }
            if arguments.is_empty()
                && (label.is(InternalLabel::Dots) || label.is(InternalLabel::NoDots))
    )
}

/// A sort as the view reports it: `None` for a sort that mentions a sort variable, the injector's
/// placeholder for a parameter nothing instantiates.
fn reported(sort: &Sort) -> Option<Sort> {
    fn mentions(sort: &Sort) -> bool {
        sort.is_rigid_variable() || sort.parameters.iter().any(mentions)
    }
    (!mentions(sort)).then(|| sort.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn load(source: &str) -> crate::outer::LoadedDefinition {
        let prelude = crate::builtin::embedded("prelude.md").expect("embedded prelude");
        let mut resolver = |_: &str, required: &str| {
            crate::builtin::embedded(required)
                .ok_or_else(|| format!("unexpected require {required}"))
        };
        crate::outer::load_with_options(
            crate::outer::ResolvedSource::new("main.k", source.to_owned()),
            "MAIN",
            &mut resolver,
            &crate::outer::LoadOptions {
                implicit_sources: vec![prelude],
                ..crate::outer::LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("MAIN loads: {error}"))
    }

    /// The equations typed for a chain of `depth` nested `#let`s in a rule's right side.
    fn equations_typed(depth: usize) -> usize {
        let mut body = format!("Y{depth} +Int 1");
        for level in (1..=depth).rev() {
            let value = if level == 1 {
                "X".to_owned()
            } else {
                format!("Y{}", level - 1)
            };
            body = format!("#let Y{level} = {value} #in {body}");
        }
        let loaded = load(&format!(
            "module MAIN\n  imports INT\n  syntax KItem ::= m(Int) | g(K)\n  rule [r]: m(X) => g({body})\nendmodule\n"
        ));
        let sentence = loaded
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| sentence.attributes().string(AttributeKey::Label) == Some("MAIN.r"))
            .unwrap()
            .clone();
        let typer = SentenceTyper::new(loaded.resolved(), "MAIN").unwrap();
        EQUATION_TYPINGS.with(|count| count.set(0));
        typer.typing_in(&sentence, "MAIN").unwrap();
        EQUATION_TYPINGS.with(Cell::get)
    }

    // Each nested equation is typed once: the walks that only compute a sort skip the equations
    // below them, so the work grows linearly with the nesting depth.
    #[test]
    fn nested_local_functions_type_each_equation_once() {
        for depth in [1, 4, 12] {
            assert_eq!(equations_typed(depth), depth, "depth {depth}");
        }
    }
}
