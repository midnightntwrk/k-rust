//! Declared ends (`#[k::end(..)]`): what the definition may hold of them, and the table of them.
//!
//! A declared end is a set of states, and the definition states it as a function of the whole
//! configuration: a total `Bool` function that is true exactly on the end's clauses, and for a
//! `refused` end a partial function that gives the reason there. The shared parser lowers an end
//! to those functions and their equations (`krs_syntax::EndDeclaration`), each function marked
//! with [`ProductionAttribute::End`]. This module holds what follows from the functions being
//! functions of the configuration that only tools apply:
//!
//! - no sentence applies one ([`check_ends`]): a rule that asked whether the state is an end
//!   would make the transition system depend on the classes, which are statements about where it
//!   stops, and K has no way for a sentence to pass the configuration it is evaluated in;
//! - an end's pattern reads only cells every state holds exactly once ([`check_ends`]): the
//!   function has one argument, the configuration, so inside an optional cell or a cell
//!   collection it would have no one instance to read;
//! - the module of a package that declares an end imports the configured module
//!   ([`import_configuration`]), whose configuration declares the sort the functions take;
//! - the table of the ends a definition declares ([`declared_ends`]), which `ends.json` writes.

use std::collections::BTreeMap;

use krs_ir::{EndClass, EndForm, EndRole, ProductionAttribute, StableItemId};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, ProductionSentence, SemanticModule, SemanticProduction,
    SemanticRule, SemanticTerm,
};

use crate::semantic::DescriptorLoweringError;

/// The end a function production belongs to, as its mark states it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct EndMark<'a> {
    pub(crate) class: EndClass,
    pub(crate) role: EndRole,
    pub(crate) form: EndForm,
    pub(crate) item: &'a str,
}

/// The mark among a production's attributes.
pub(crate) fn mark_among<S, D>(attributes: &[ProductionAttribute<S, D>]) -> Option<EndMark<'_>> {
    attributes.iter().find_map(|attribute| match attribute {
        ProductionAttribute::End {
            class,
            role,
            form,
            item,
            ..
        } => Some(EndMark {
            class: *class,
            role: *role,
            form: *form,
            item,
        }),
        _ => None,
    })
}

/// The end the semantic production `production` is a function of.
pub(crate) fn semantic_mark(production: &SemanticProduction) -> Option<EndMark<'_>> {
    mark_among(production.attributes())
}

/// The end the Definition IR production `production` is a function of.
pub(crate) fn definition_mark(production: &ProductionSentence) -> Option<EndMark<'_>> {
    mark_among(production.attributes())
}

/// The names of the equations the shared parser lowers the end `item` to: its clause, the
/// equation that makes it `false` elsewhere, and a refused end's reason.
fn lowered_equations(item: &str) -> [String; 3] {
    [
        item.to_owned(),
        format!("{item}_otherwise"),
        format!("{item}_reason"),
    ]
}

/// Makes the module of every package that declares an end import the configured module: an
/// end's functions take the configuration, whose sort the configuration's sentence declares,
/// and a constructor's end names the main computation cell. A module that already reads the
/// configuration imports it already.
pub(crate) fn import_configuration(modules: &mut [SemanticModule]) {
    let Some(configured) = modules
        .iter()
        .find(|module| !module.is_spec() && module.configuration().is_some())
        .map(|module| module.id().clone())
    else {
        return;
    };
    for module in modules.iter_mut().filter(|module| {
        *module.id() != configured
            && module
                .productions()
                .iter()
                .any(|production| semantic_mark(production).is_some())
    }) {
        module.add_imports([configured.clone()]);
    }
}

/// Refuses the first declared end the definition cannot hold.
///
/// # Errors
///
/// [`DescriptorLoweringError::InvalidEnd`] for
///
/// - a sentence other than an end's own lowered equations that applies one of its functions,
///   and the initializer or a context alias that does;
/// - an end whose pattern reads a cell inside an optional cell or a cell collection;
/// - a constructor's end in a definition without a configuration, without one main computation
///   cell, or whose main computation cell lies inside an optional cell or a cell collection.
pub(crate) fn check_ends(modules: &[SemanticModule]) -> Result<(), DescriptorLoweringError> {
    let marks = modules
        .iter()
        .flat_map(|module| {
            module
                .productions()
                .iter()
                .filter_map(|production| Some((production.id(), semantic_mark(production)?)))
        })
        .collect::<BTreeMap<_, _>>();
    if marks.is_empty() {
        return Ok(());
    }
    let ends = Ends {
        marks,
        keys: crate::instance_keys::InstanceKeys::of(modules),
        configuration: modules.iter().find_map(SemanticModule::configuration),
    };
    for module in modules {
        for rule in module.sentences() {
            ends.check_rule(rule)?;
        }
        for alias in module.context_aliases() {
            let mut applied = Vec::new();
            for cell in alias.body().cells() {
                crate::instance_keys::term_applications(cell.pattern(), &mut applied);
            }
            ends.unapplied(
                applied,
                alias.id(),
                &format!("the context alias `{}`", alias.name()),
            )?;
        }
    }
    if let Some(configuration) = ends.configuration {
        let mut applied = Vec::new();
        initializer_applications(configuration.initializer(), &mut applied);
        if let Some((function, _)) = applied
            .iter()
            .find(|(function, _)| ends.marks.contains_key(function))
        {
            ends.unapplied(applied.clone(), function, "the configuration's initializer")?;
        }
    }
    Ok(())
}

/// The end functions of a definition, with what judging them reads.
struct Ends<'a> {
    marks: BTreeMap<&'a StableItemId, EndMark<'a>>,
    keys: crate::instance_keys::InstanceKeys,
    configuration: Option<&'a krs_ir_levels::SemanticConfiguration>,
}

impl Ends<'_> {
    fn refuse(
        item: &StableItemId,
        term: Option<&SemanticTerm>,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidEnd {
            item: Box::new(item.clone()),
            reason,
            range: term
                .and_then(|term| term.origin().origin().exact_authored_range())
                .map(Box::new),
        }
    }

    /// Refuses the first of `applied` that applies an end's function, in the sentence `item`,
    /// which the message names `by`.
    fn unapplied(
        &self,
        applied: Vec<(&StableItemId, &SemanticTerm)>,
        item: &StableItemId,
        by: &str,
    ) -> Result<(), DescriptorLoweringError> {
        match applied
            .into_iter()
            .find(|(function, _)| self.marks.contains_key(function))
        {
            Some((function, application)) => Err(Self::refuse(
                item,
                Some(application),
                self.named(function, by),
            )),
            None => Ok(()),
        }
    }

    /// Why no sentence names `function`, an end's, said of the sentence `by`.
    fn named(&self, function: &StableItemId, by: &str) -> String {
        let mark = self.marks[function];
        format!(
            "{by} names `{}`, the function that {} the end `{}`: an end is a statement about the states where the run is over, which a tool reads by applying the function to a whole configuration, so no sentence of the definition applies it; state what the sentence needs as a condition over the cells it reads",
            function.item_name(),
            match mark.role {
                EndRole::Holds => "says whether a state is in",
                EndRole::Reason => "gives the reason of",
            },
            mark.item,
        )
    }

    /// The K name of the cell `cell` of the configuration.
    fn cell_name(&self, cell: &krs_ir::SemanticId) -> String {
        fn find<'c>(
            cells: &'c [krs_ir::FixedCell<krs_ir_levels::SemanticSortRef, krs_ir::SemanticId>],
            id: &krs_ir::SemanticId,
        ) -> Option<&'c str> {
            cells.iter().find_map(|cell| {
                if cell.id() == id {
                    return Some(cell.name());
                }
                match cell.content() {
                    krs_ir::FixedCellContent::Children { children } => find(children, id),
                    krs_ir::FixedCellContent::Term { .. } => None,
                }
            })
        }
        self.configuration
            .and_then(|configuration| find(configuration.cells(), cell))
            .unwrap_or("?")
            .to_owned()
    }

    /// Judges one sentence: it applies no end's function, and where it is an end's own
    /// equation, the end reads only cells every state holds exactly once.
    fn check_rule(&self, rule: &SemanticRule) -> Result<(), DescriptorLoweringError> {
        let own = own_function(rule, &self.marks);
        // Only an end's lowered equations define its functions.
        if let Some(function) = crate::instance_keys::defined_function(rule)
            .filter(|function| self.marks.contains_key(function))
            && own != Some(function)
        {
            return Err(Self::refuse(
                rule.id(),
                None,
                self.named(
                    function,
                    &format!("the equation `{}`", rule.id().item_name()),
                ),
            ));
        }
        self.unapplied(
            crate::instance_keys::applications(rule),
            rule.id(),
            &format!("`{}`", rule.id().item_name()),
        )?;
        let Some(function) = own else {
            return Ok(());
        };
        let mark = self.marks[function];
        if let Some(context) = rule.function_context()
            && let Some((pattern, holder)) = context.cells().cells().iter().find_map(|pattern| {
                self.keys
                    .enclosing(pattern.cell())
                    .last()
                    .map(|holder| (pattern, holder))
            })
        {
            let holder = self.cell_name(holder);
            return Err(Self::refuse(
                rule.id(),
                Some(pattern.pattern()),
                format!(
                    "the end `{}` reads the cell `{}` inside `{holder}`, an optional cell or a cell collection: an end is a function of the whole configuration, which holds no one instance of `{holder}` for it to read; declare the end over cells every state holds exactly once",
                    mark.item,
                    self.cell_name(pattern.cell()),
                ),
            ));
        }
        if mark.form == EndForm::Constructor
            && let Some(reason) = self.constructor_refusal(mark)
        {
            return Err(Self::refuse(rule.id(), None, reason));
        }
        Ok(())
    }

    /// Why the definition cannot hold the constructor's end `mark`: it has no one main
    /// computation cell that every state holds exactly once.
    fn constructor_refusal(&self, mark: EndMark<'_>) -> Option<String> {
        let declared = format!(
            "the end `{}` is declared on a constructor, for the states whose main computation cell starts with it",
            mark.item
        );
        match self
            .configuration
            .map(krs_ir_levels::k_surface::main_cell)
        {
            None => Some(format!(
                "{declared}, and this definition declares no `#[k::configuration]`: an end is a set of states of a configuration"
            )),
            Some(krs_ir::MainCell::Cell(cell)) => {
                self.keys.enclosing(cell.id()).last().map(|holder| {
                    let holder = self.cell_name(holder);
                    format!(
                        "{declared}, and the main computation cell `{}` lies inside `{holder}`, an optional cell or a cell collection: an end is a function of the whole configuration, which holds no one instance of `{holder}` for it to read",
                        cell.name(),
                    )
                })
            }
            Some(krs_ir::MainCell::NoComputationCell | krs_ir::MainCell::Ambiguous { .. }) => {
                Some(format!(
                    "{declared}, and this definition's configuration has no one main computation cell; declare the end on a `fn`, over the cell it reads"
                ))
            }
        }
    }
}

/// The end function `rule` is a lowered equation of: the function its head applies, where the
/// rule is in the function's module under one of the names the end's lowering gives.
fn own_function<'r>(
    rule: &'r SemanticRule,
    ends: &BTreeMap<&StableItemId, EndMark<'_>>,
) -> Option<&'r StableItemId> {
    let function = crate::instance_keys::defined_function(rule)?;
    let mark = ends.get(function)?;
    (rule.id().package() == function.package()
        && rule.id().module_path() == function.module_path()
        && lowered_equations(mark.item)
            .iter()
            .any(|name| name == rule.id().item_name()))
    .then_some(function)
}

fn initializer_applications<'a>(
    cells: &'a [krs_ir::FixedInitializerCell<krs_ir::SemanticId, SemanticTerm>],
    applied: &mut Vec<(&'a StableItemId, &'a SemanticTerm)>,
) {
    for cell in cells {
        match cell.content() {
            krs_ir::FixedInitializerContent::Term { term } => {
                crate::instance_keys::term_applications(term, applied);
            }
            krs_ir::FixedInitializerContent::Children { children } => {
                initializer_applications(children, applied);
            }
        }
    }
}

/// One function a declared end is emitted as.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EndSymbol {
    /// The Definition IR identity of the function's production.
    pub production: String,
    /// The K label of the function, which the emitted K writes in `symbol(..)`.
    pub label: String,
}

/// One end a definition declares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclaredEnd {
    /// The class.
    pub class: EndClass,
    /// The declaring item's name as a KRS document writes an item: its Rust path with `crate::`
    /// for an item of the definition's root package (the package of its main module), and
    /// with its crate's name for an item of a dependency, such as `cpu::execute::locked`. An end
    /// a cell group's package declares has one name in every definition that holds the group.
    pub item: String,
    /// The declaring item's package, by Cargo name.
    pub package: String,
    /// The declaring item's module path below its crate root.
    pub module: Vec<String>,
    /// The declaring item's name.
    pub name: String,
    /// The spelling the end was declared in.
    pub form: EndForm,
    /// The total `Bool` function of the configuration that is true exactly on the end.
    pub holds: EndSymbol,
    /// A refused end's reason: the partial function of the configuration that gives it where
    /// the end holds, and the K sort of its values.
    pub reason: Option<(EndSymbol, String)>,
    /// The package-relative file and the byte range in it of the item the end is declared on,
    /// where the definition records them.
    pub origin: Option<(String, u32, u32)>,
}

/// The ends `definition` declares, ordered by declaring package, module and item name.
///
/// Each is read from the functions it is emitted as: the production marked as the end's
/// `holds` function, paired with the one marked as its reason by their module and item.
///
/// # Errors
///
/// [`crate::EmitError`] where a reason's sort has no K name, which a validated definition does
/// not hold.
pub fn declared_ends(definition: &DefinitionIr) -> Result<Vec<DeclaredEnd>, crate::EmitError> {
    type Key = (String, Vec<String>, String);
    let renderer = crate::emit::SentenceRenderer::new(definition);
    let mut holds = BTreeMap::<Key, (&ProductionSentence, EndMark<'_>, &StableItemId)>::new();
    let mut reasons = BTreeMap::<Key, &ProductionSentence>::new();
    for sentence in definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
    {
        let DefinitionSentence::Production(production) = sentence else {
            continue;
        };
        let (Some(mark), Some(item)) = (definition_mark(production), sentence.item()) else {
            continue;
        };
        let key = (
            item.package().cargo_name().to_owned(),
            item.module_path().to_vec(),
            mark.item.to_owned(),
        );
        match mark.role {
            EndRole::Holds => {
                holds.insert(key, (production, mark, item));
            }
            EndRole::Reason => {
                reasons.insert(key, production);
            }
        }
    }
    let symbol = |production: &ProductionSentence| EndSymbol {
        production: production.symbol().id().as_str().to_owned(),
        label: production.symbol().emitted_name().to_owned(),
    };
    holds
        .into_iter()
        .map(|(key, (production, mark, item))| {
            let reason = reasons
                .get(&key)
                .map(|reason| -> Result<_, crate::EmitError> {
                    Ok((symbol(reason), renderer.sort_name(reason.result_sort())?))
                })
                .transpose()?;
            let (package, module, name) = key;
            Ok(DeclaredEnd {
                class: mark.class,
                item: std::iter::once(
                    if item.package().k_namespace() == definition.main_module().as_str() {
                        "crate".to_owned()
                    } else {
                        definition.crate_name(item.package())
                    },
                )
                .chain(module.iter().cloned())
                .chain([name.clone()])
                .collect::<Vec<_>>()
                .join("::"),
                package,
                module,
                name,
                form: mark.form,
                holds: symbol(production),
                reason,
                origin: production
                    .origin()
                    .origin()
                    .exact_authored_range()
                    .map(|range| {
                        (
                            range.file.package_relative_path().to_owned(),
                            range.start_byte,
                            range.end_byte,
                        )
                    }),
            })
        })
        .collect()
}

/// The schema of `ends.json`.
pub const ENDS_SCHEMA: &str = "krs-ends/1";

/// `ends.json`: the table of the ends a definition declares, for the tools that evaluate them.
///
/// `kore` gives the KORE symbol a K label compiles to, without sort arguments; the compiler
/// that writes the table knows the backend's encoding, and this crate does not.
#[must_use]
pub fn ends_json(ends: &[DeclaredEnd], kore: &dyn Fn(&str) -> String) -> String {
    let symbol = |symbol: &EndSymbol| {
        serde_json::json!({
            "production": symbol.production,
            "label": symbol.label,
            "kore": kore(&symbol.label),
        })
    };
    let document = serde_json::json!({
        "schema": ENDS_SCHEMA,
        "argument_sort": "GeneratedTopCell",
        "ends": ends.iter().map(|end| {
            let mut entry = serde_json::Map::new();
            entry.insert("class".to_owned(), end.class.word().into());
            entry.insert("item".to_owned(), end.item.clone().into());
            entry.insert("package".to_owned(), end.package.clone().into());
            entry.insert("module".to_owned(), end.module.clone().into());
            entry.insert("name".to_owned(), end.name.clone().into());
            entry.insert(
                "form".to_owned(),
                match end.form {
                    EndForm::Clause => "clause",
                    EndForm::Constructor => "constructor",
                }
                .into(),
            );
            entry.insert("holds".to_owned(), symbol(&end.holds));
            if let Some((reason, sort)) = &end.reason {
                let mut reason = symbol(reason);
                reason["sort"] = sort.clone().into();
                entry.insert("reason".to_owned(), reason);
            }
            if let Some((file, start, end)) = &end.origin {
                entry.insert(
                    "origin".to_owned(),
                    serde_json::json!({"file": file, "start_byte": start, "end_byte": end}),
                );
            }
            serde_json::Value::Object(entry)
        }).collect::<Vec<_>>(),
    });
    // A JSON value prints itself, indented, without an error of its own.
    format!("{document:#}\n")
}
