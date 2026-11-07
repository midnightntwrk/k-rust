//! The re-derivation of one sentence of an emitted definition: KRS's own derivation passes run
//! on a pre-derivation sentence, and the result lowered and rendered alone, with the baseline's
//! naming and index.
//!
//! A K mutation of a definition KRS emitted is accepted only when it is a definition some KRS
//! source emits. For a sentence whose authored content the mutation edits, the caller lifts the
//! edited content into the sentence's pre-derivation form `A'` (the semantic sentence before
//! `lift_local_functions` and the definedness tests), and [`Rederivation::rederive`] gives
//! what KRS emits for `A'`: the derivation passes `D` that run after the rule-level checks, the
//! semantic theory's validation of the sentence among the baseline's other sentences, and the
//! lowering and rendering `R` of the sentence alone. The mutant's sentence is emitted by a
//! source exactly when it is `R(D(A'))` for an `A'` that some source lowers to, which the caller
//! decides by comparing the two.
//!
//! The passes re-run read only the sentence and declarations no rule edit changes (the sorts,
//! the catalog of builtin operations), so the sentence derives as it would among a source's
//! other sentences. One pass writes other sentences: `lift_local_functions` lifts a `let` block
//! or `k::matches!` of the sentence into a function of its own, declared beside it with its
//! equations. The sentence is derived only when that function's declaration and equations are
//! exactly the baseline's, so that every other sentence of the emission is as before; otherwise
//! it is not derived here.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{ApplicationRef, BuiltinSort, ModuleId, SemanticId, SourceMapKey, StableItemId};
use krs_ir_levels::definedness::Sorts;
use krs_ir_levels::k_surface::SentenceVariables;
use krs_ir_levels::{
    DefinitionSentence, IrTermKind, RuleBodyRef, RuleSentence, SemanticModule, SemanticRule,
    SemanticSortRef,
};

use crate::emit::{EmitError, RenderedSentence, SentenceRenderer};
use crate::lowering::{LoweredDefinition, LoweringError, RuleLowering};
use crate::semantic::{DescriptorLoweringError, RetainedLowering};

/// The baseline of a re-derivation: one lowering of a definition, kept in process, with what
/// re-derives and renders one of its sentences.
pub struct Rederivation<'a> {
    retained: &'a RetainedLowering,
    lowered: &'a LoweredDefinition,
    lowering: RuleLowering,
    renderer: SentenceRenderer<'a>,
    sorts: Option<Sorts>,
    index: KLabelIndex,
    /// Each Definition IR sentence key of a rule, with its module and place.
    sentences: BTreeMap<SourceMapKey, (usize, usize)>,
    /// Each pre-derivation rule's sentence key (its label's, else its own), with its place.
    pre_rules: BTreeMap<SourceMapKey, (usize, usize)>,
    /// Each derived rule's sentence key, with its place in the theory.
    derived_rules: BTreeMap<SourceMapKey, (usize, usize)>,
    /// The Definition IR nodes of each semantic node.
    definition_keys: BTreeMap<SourceMapKey, Vec<SourceMapKey>>,
    /// The theory's modules with no rules: the declarations a derived sentence is validated
    /// among.
    declarations: Vec<SemanticModule>,
    /// The sentence key of each equation whose head is not its own authored syntax.
    fixed_heads: BTreeSet<SourceMapKey>,
}

/// A sentence of the baseline that a re-derivation can replace.
pub struct Site<'r> {
    /// The baseline's Definition IR sentence.
    pub definition: &'r RuleSentence,
    /// The baseline's pre-derivation sentence `A`.
    pub pre_derivation: &'r SemanticRule,
    /// The baseline's derived sentence `D(A)`.
    pub derived: &'r SemanticRule,
    /// The semantic module holding the sentence.
    pub module: &'r ModuleId,
    /// The K module the sentence is emitted in.
    pub emitted_module: String,
    /// The emitted name of each variable of the baseline sentence.
    pub names: SentenceVariables,
    /// Whether the sentence is an equation whose head application is not authored in the
    /// sentence alone: a function shorthand writes every equation's head at the function's
    /// declaration, and an equation table writes its rows' heads at its header, so an edit of one
    /// sentence's head is no edit of its source. An equation item (`#[k::equation]`) writes its
    /// head in its own pattern, and a simplification its whole left side.
    pub head_fixed: bool,
}

/// What KRS emits for one pre-derivation sentence.
#[derive(Clone, Debug)]
pub struct Rederived {
    /// The pre-derivation sentence `A'`.
    pub pre_derivation: SemanticRule,
    /// The derived sentence `D(A')`.
    pub derived: SemanticRule,
    /// Its Definition IR sentence.
    pub definition: RuleSentence,
    /// Its rendering `R(D(A'))`, from its indentation to its newline, as `emit_k` writes a
    /// sentence.
    pub text: String,
    /// The range of each rendered node within [`Self::text`], by Definition IR key.
    pub ranges: Vec<(SourceMapKey, std::ops::Range<usize>)>,
}

/// Why a pre-derivation sentence has no re-derivation here.
#[derive(Debug)]
#[non_exhaustive]
pub enum RederiveFailure {
    /// `lift_local_functions` lifts a block or test of the sentence into a function whose
    /// declaration or equations differ from the baseline's: they are sentences of their own, and
    /// the derivation would change them, which is not judged.
    LocalFunction,
    /// KRS refuses the sentence: the definedness pass's refusal, or the semantic theory's
    /// validation of the sentence among the baseline's others. Its diagnostic carries KRS's
    /// code.
    Refused(DescriptorLoweringError),
    /// The sentence does not lower to Definition IR.
    Lowering(LoweringError),
    /// The lowered sentence does not render.
    Render(EmitError),
}

impl fmt::Display for RederiveFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LocalFunction => formatter.write_str(
                "the sentence holds a block or test that KRS lifts into a function of its own, and the edit changes that function's declaration or equations, which are sentences of their own",
            ),
            Self::Refused(error) => error.fmt(formatter),
            Self::Lowering(error) => error.fmt(formatter),
            Self::Render(error) => error.fmt(formatter),
        }
    }
}

impl Error for RederiveFailure {}

/// Why a baseline cannot be re-derived from at all, or a sentence key names no rule of it.
#[derive(Debug)]
#[non_exhaustive]
pub enum RederivationError {
    /// The baseline's naming does not lower its own theory.
    Lowering(LoweringError),
    /// The baseline's index does not render its own names.
    Render(EmitError),
    /// The key names no rule sentence of the Definition IR, or one with no pre-derivation
    /// sentence (a sentence a derivation pass added).
    UnknownSentence(SourceMapKey),
}

impl fmt::Display for RederivationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lowering(error) => error.fmt(formatter),
            Self::Render(error) => error.fmt(formatter),
            Self::UnknownSentence(key) => write!(
                formatter,
                "{key} is no rule sentence that a pre-derivation sentence lowers to"
            ),
        }
    }
}

impl Error for RederivationError {}

/// The sentence key of a semantic rule: the key its Definition IR sentence lowers from.
pub(crate) fn sentence_key(rule: &SemanticRule) -> &SourceMapKey {
    rule.label()
        .map_or(rule.origin(), |label| label.origin())
        .key()
}

/// The sentence keys of the equations of `modules` whose head application is not authored in the
/// sentence alone ([`Site::head_fixed`]): its authored range is its function's declaration (a
/// function shorthand), is shared by another equation's head (the shorthand's other branches, an
/// equation table's rows), or is not exact.
fn fixed_heads(modules: &[SemanticModule]) -> BTreeSet<SourceMapKey> {
    let declarations = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .map(|production| {
            (
                production.id(),
                production.origin().origin().exact_authored_range(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let heads = modules
        .iter()
        .flat_map(SemanticModule::rules)
        .filter(|rule| rule.kind() == krs_ir::SentenceKind::Equation)
        .filter_map(|rule| {
            let RuleBodyRef::Term(body) = rule.relational_body() else {
                return None;
            };
            let head = body.local_term().unwrap_or_else(|| body.from());
            let function = match head.kind() {
                IrTermKind::Application {
                    application: ApplicationRef::Declared(id),
                    ..
                } => Some(id),
                _ => None,
            };
            Some((
                sentence_key(rule),
                head.origin().origin().exact_authored_range(),
                function,
            ))
        })
        .collect::<Vec<_>>();
    heads
        .iter()
        .filter(|(key, range, function)| {
            let Some(range) = range else {
                return true;
            };
            function
                .and_then(|function| declarations.get(function))
                .is_some_and(|declared| declared.as_ref() == Some(range))
                || heads
                    .iter()
                    .any(|(other, shared, _)| other != key && shared.as_ref() == Some(range))
        })
        .map(|(key, _, _)| (*key).clone())
        .collect()
}

fn rule_places(modules: &[SemanticModule]) -> BTreeMap<SourceMapKey, (usize, usize)> {
    modules
        .iter()
        .enumerate()
        .flat_map(|(module, semantic)| {
            semantic
                .rules()
                .iter()
                .enumerate()
                .map(move |(rule, sentence)| (sentence_key(sentence).clone(), (module, rule)))
        })
        .collect()
}

impl<'a> Rederivation<'a> {
    /// The baseline `retained`, lowered as `lowered` (from `retained`'s theory).
    ///
    /// # Errors
    ///
    /// [`RederivationError::Lowering`] or [`RederivationError::Render`] when the baseline's own
    /// naming or index fails, which `lowered`'s existence rules out.
    pub fn new(
        retained: &'a RetainedLowering,
        lowered: &'a LoweredDefinition,
    ) -> Result<Self, RederivationError> {
        let lowering = RuleLowering::new(retained.theory()).map_err(RederivationError::Lowering)?;
        let renderer = SentenceRenderer::new(lowered.definition());
        let index = KLabelIndex::new(retained, &lowering, &renderer)?;
        let sentences = lowered
            .definition()
            .modules()
            .iter()
            .enumerate()
            .flat_map(|(module, definition)| {
                definition
                    .sentences()
                    .iter()
                    .enumerate()
                    .filter(|(_, sentence)| matches!(sentence, DefinitionSentence::Rule(_)))
                    .map(move |(place, sentence)| {
                        (sentence.origin().key().clone(), (module, place))
                    })
            })
            .collect();
        let mut definition_keys = BTreeMap::<SourceMapKey, Vec<SourceMapKey>>::new();
        for (definition, semantic) in lowered.semantic_keys() {
            definition_keys
                .entry(semantic.clone())
                .or_default()
                .push(definition.clone());
        }
        Ok(Self {
            retained,
            lowered,
            lowering,
            renderer,
            // The definedness pass reads the declarations after `lift_local_functions`, which
            // are the theory's.
            sorts: Sorts::of_modules(retained.theory().modules()),
            index,
            sentences,
            pre_rules: rule_places(retained.pre_derivation()),
            derived_rules: rule_places(retained.theory().modules()),
            definition_keys,
            declarations: retained
                .theory()
                .modules()
                .iter()
                .map(|module| module.clone().with_rules(Vec::new()))
                .collect(),
            fixed_heads: fixed_heads(retained.pre_derivation()),
        })
    }

    /// The label index of the baseline.
    #[must_use]
    pub const fn index(&self) -> &KLabelIndex {
        &self.index
    }

    /// The baseline's lowering.
    #[must_use]
    pub const fn lowered(&self) -> &'a LoweredDefinition {
        self.lowered
    }

    /// The baseline's semantic lowering, with what the re-derivation keeps of it.
    #[must_use]
    pub const fn retained(&self) -> &'a RetainedLowering {
        self.retained
    }

    /// The Definition IR nodes lowered from the semantic node `key`.
    #[must_use]
    pub fn definition_keys(&self, key: &SourceMapKey) -> &[SourceMapKey] {
        self.definition_keys.get(key).map_or(&[], Vec::as_slice)
    }

    /// The baseline rule sentence whose Definition IR key is `key`.
    ///
    /// # Errors
    ///
    /// [`RederivationError::UnknownSentence`] when `key` names no rule sentence lowered from a
    /// pre-derivation sentence.
    pub fn site(&self, key: &SourceMapKey) -> Result<Site<'_>, RederivationError> {
        let unknown = || RederivationError::UnknownSentence(key.clone());
        let &(module, place) = self.sentences.get(key).ok_or_else(unknown)?;
        let emitted = &self.lowered.definition().modules()[module];
        let DefinitionSentence::Rule(definition) = &emitted.sentences()[place] else {
            return Err(unknown());
        };
        let semantic = self.lowered.semantic_key(key).ok_or_else(unknown)?;
        let &(pre_module, pre_place) = self.pre_rules.get(semantic).ok_or_else(unknown)?;
        let &(derived_module, derived_place) =
            self.derived_rules.get(semantic).ok_or_else(unknown)?;
        let semantic_module = &self.retained.pre_derivation()[pre_module];
        Ok(Site {
            definition,
            pre_derivation: &semantic_module.rules()[pre_place],
            derived: &self.retained.theory().modules()[derived_module].rules()[derived_place],
            module: semantic_module.id(),
            emitted_module: emitted.id().as_str().to_owned(),
            names: self.renderer.naming().rule(definition),
            head_fixed: self.fixed_heads.contains(semantic),
        })
    }

    /// Renders the baseline's Definition IR sentence `key` alone, as `emit_k` writes it at the
    /// sentence's generated range in `definition.k`.
    ///
    /// # Errors
    ///
    /// [`RederivationError::UnknownSentence`] for a key that names no sentence, and the
    /// renderer's failure, which `emit_k`'s success rules out.
    pub fn render_baseline(&self, key: &SourceMapKey) -> Result<String, RederivationError> {
        let sentence = self
            .lowered
            .definition()
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
            .find(|sentence| sentence.origin().key() == key)
            .ok_or_else(|| RederivationError::UnknownSentence(key.clone()))?;
        self.renderer
            .render(sentence)
            .map(|rendered| rendered.text)
            .map_err(RederivationError::Render)
    }

    /// What KRS emits for `pre_derivation` in place of `site`'s sentence: its derivation, its
    /// validation among the baseline's other sentences, and its rendering alone.
    ///
    /// # Errors
    ///
    /// [`RederiveFailure`]: the sentence is not judged here, or KRS refuses it.
    pub fn rederive(
        &self,
        site: &Site<'_>,
        pre_derivation: SemanticRule,
    ) -> Result<Rederived, RederiveFailure> {
        let module = self
            .retained
            .pre_derivation()
            .iter()
            .find(|module| module.id() == site.module)
            .ok_or(RederiveFailure::LocalFunction)?;
        let derivation = crate::semantic::derive_rule(module, &pre_derivation, self.sorts.as_ref())
            .map_err(RederiveFailure::Refused)?;
        // A function lifted out of the sentence is declared, and its equations stated, beside
        // it: the sentence derives here only when they are the baseline sentence's, so that no
        // other sentence of the emission changes.
        let baseline =
            crate::semantic::derive_rule(module, site.pre_derivation, self.sorts.as_ref())
                .map_err(RederiveFailure::Refused)?;
        if derivation.productions != baseline.productions
            || derivation.equations != baseline.equations
        {
            return Err(RederiveFailure::LocalFunction);
        }
        let derived = derivation.rule;
        let key = sentence_key(site.derived);
        // The theory's validation of the derived sentence among the baseline's declarations.
        // The other sentences are left out: each is valid in the baseline, and validation
        // relates two sentences only by the uniqueness of their node keys, which the replaced
        // sentence's keys keep (the baseline's own, or new ones under its keys).
        let modules = self
            .retained
            .theory()
            .modules()
            .iter()
            .zip(&self.declarations)
            .map(|(module, declarations)| {
                if module.rules().iter().any(|rule| sentence_key(rule) == key) {
                    declarations.clone().with_rules(vec![derived.clone()])
                } else {
                    declarations.clone()
                }
            })
            .collect();
        crate::semantic::checked_theory(modules).map_err(RederiveFailure::Refused)?;
        let (definition, _) = self
            .lowering
            .lower(&derived)
            .map_err(RederiveFailure::Lowering)?;
        let RenderedSentence { text, ranges } = self
            .renderer
            .render(&DefinitionSentence::Rule(definition.clone()))
            .map_err(RederiveFailure::Render)?;
        Ok(Rederived {
            pre_derivation,
            derived,
            definition,
            text,
            ranges,
        })
    }
}

/// One production a K label of the baseline names.
#[derive(Clone, Debug)]
pub struct IndexedProduction {
    /// The production's declaration.
    pub id: StableItemId,
    /// Its result sort.
    pub result: SemanticSortRef,
    /// The sort of each nonterminal, in order.
    pub arguments: Vec<SemanticSortRef>,
    /// The number of instance keys a function evaluated in one instance of a Map collection
    /// receives after [`Self::arguments`], one for each Map collection on the path of the cells
    /// its context reads: its K application writes them as further operands, which KRS passes
    /// and no source writes.
    pub keys: usize,
    /// Whether it is a function (else a constructor).
    pub function: bool,
    /// Whether it is parametric.
    pub parametric: bool,
}

/// The names the baseline's K gives its sorts, productions and cells, each with the semantic
/// identity it names: the inverse of the baseline's naming, as `emit_k` spells it. Only what a
/// source can name is indexed: the declarations of the pre-derivation modules, without the
/// functions `lift_local_functions` lifts out of a sentence (`krsLocal_<digest>`), which no
/// source applies.
#[derive(Clone, Debug, Default)]
pub struct KLabelIndex {
    productions: BTreeMap<String, IndexedProduction>,
    sorts: BTreeMap<String, SemanticSortRef>,
    sort_names: BTreeMap<SemanticSortRef, String>,
    cells: BTreeMap<String, SemanticId>,
}

impl KLabelIndex {
    fn new(
        retained: &RetainedLowering,
        lowering: &RuleLowering,
        renderer: &SentenceRenderer<'_>,
    ) -> Result<Self, RederivationError> {
        let mut index = Self::default();
        let mut sort = |sort: SemanticSortRef| -> Result<(), RederivationError> {
            if index.sort_names.contains_key(&sort) {
                return Ok(());
            }
            let lowered = lowering.sort(&sort).map_err(RederivationError::Lowering)?;
            let name = renderer
                .sort_name(&lowered)
                .map_err(RederivationError::Render)?;
            index.sorts.insert(name.clone(), sort.clone());
            index.sort_names.insert(sort, name);
            Ok(())
        };
        for builtin in BuiltinSort::ALL {
            sort(SemanticSortRef::Builtin(builtin))?;
        }
        // The pre-derivation modules declare what authored syntax names; the derivation passes
        // add only functions lifted out of a sentence, which no source applies.
        for module in retained.pre_derivation() {
            for declared in module.sorts() {
                sort(SemanticSortRef::Declared(declared.id().clone()))?;
            }
        }
        for declaration in lowering.group_cells().keys() {
            sort(SemanticSortRef::Cell(declaration.clone()))?;
        }
        for module in retained.pre_derivation() {
            for production in module.productions() {
                let Some(symbol) = lowering.productions().get(production.id()) else {
                    continue;
                };
                index.productions.insert(
                    symbol.emitted_name().to_owned(),
                    IndexedProduction {
                        id: production.id().clone(),
                        result: production.result_sort().clone(),
                        arguments: production
                            .items()
                            .iter()
                            .filter_map(|item| match item.kind() {
                                krs_ir::GrammarProductionItemKind::NonTerminal { sort, .. } => {
                                    Some(sort.clone())
                                }
                                _ => None,
                            })
                            .collect(),
                        keys: lowering.instance_keys(production.id()),
                        function: production.attributes().iter().any(|attribute| {
                            matches!(attribute, krs_ir::ProductionAttribute::Function { .. })
                        }),
                        parametric: !production.parameters().is_empty(),
                    },
                );
            }
        }
        for (cell, symbol) in lowering.fixed_cells() {
            let name = renderer
                .cell_name(symbol)
                .map_err(RederivationError::Render)?;
            index.cells.insert(name, cell.clone());
        }
        Ok(index)
    }

    /// The production whose K label is `label`.
    #[must_use]
    pub fn production(&self, label: &str) -> Option<&IndexedProduction> {
        self.productions.get(label)
    }

    /// The sort the baseline's K names `name`.
    #[must_use]
    pub fn sort(&self, name: &str) -> Option<&SemanticSortRef> {
        self.sorts.get(name)
    }

    /// The K name of `sort`.
    #[must_use]
    pub fn sort_name(&self, sort: &SemanticSortRef) -> Option<&str> {
        self.sort_names.get(sort).map(String::as_str)
    }

    /// The fixed cell the baseline's K names `<name>`.
    #[must_use]
    pub fn cell(&self, name: &str) -> Option<&SemanticId> {
        self.cells.get(name)
    }
}
