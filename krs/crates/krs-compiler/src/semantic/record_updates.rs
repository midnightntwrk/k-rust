//! Record updates `Ctor { f: e, ..t }` (F5).
//!
//! K has no field projection on a term: the only way a rule reads a field of
//! a matched term is to bind it in the pattern. A record update is therefore
//! defined by expansion. Its base `t` is an alias `t @ Ctor { f: p, .. }` of
//! one record in the left-hand side; every field an update of `t` leaves
//! out is bound in that pattern, to the binder the pattern already gives it
//! or to a hidden binder, and the update fills it with that binder. A field
//! the pattern leaves out (or writes `_`) is matched by the hidden binder
//! instead of a wildcard; a field it matches with another pattern `p` is
//! matched by `( p #as Hidden )`. Nothing new reaches K: the rule is the one
//! an author would write by naming every field, and an alias used only as a
//! base carries no `#as`.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorIndex, DescriptorTerm, ProductionFieldId,
    ProvenanceKey, SemanticId, StableItemId,
};

use super::catalog::ProductionSignature;
use super::error::DescriptorLoweringError;

/// The record a base alias matched and an update builds.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Record {
    /// A named-field constructor.
    Production(StableItemId),
    /// A nested `#[k::cell]` group.
    Cell(StableItemId),
}

/// How a field an update leaves out is filled.
#[derive(Clone, Debug)]
pub(super) enum Fill {
    /// The binder the alias's pattern gives the field.
    Binder(String),
    /// A hidden binder the alias's pattern binds the field to.
    Hidden(SemanticId),
}

/// One base alias: where it is bound and how its updates are filled.
#[derive(Clone, Debug)]
struct Alias {
    /// The `name @ pattern` provenance, the origin of the hidden binders.
    key: ProvenanceKey,
    fills: BTreeMap<ProductionFieldId, Fill>,
}

/// The record updates of one sentence, read before its terms are inferred.
#[derive(Clone, Debug, Default)]
pub(super) struct RecordUpdates {
    aliases: BTreeMap<String, Alias>,
    /// Aliases that occur only as update bases: their pattern is matched
    /// without `#as`.
    dropped: BTreeSet<String>,
}

impl RecordUpdates {
    /// Reads the updates of a sentence whose terms are `terms`: patterns,
    /// results, and conditions.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorLoweringError::InvalidRecordUpdate`] for a base
    /// that is not the alias of exactly one record of the update's
    /// constructor or cell, outside `|`.
    pub(super) fn scan(
        descriptor: &Descriptor,
        terms: &[&DescriptorTerm],
        catalog: &BTreeMap<StableItemId, ProductionSignature>,
        declarations: Option<&DescriptorIndex<'_>>,
    ) -> Result<Self, DescriptorLoweringError> {
        let mut scan = Scan::default();
        for term in terms {
            scan.walk(term, false);
        }
        if scan.updates.is_empty() {
            return Ok(Self::default());
        }
        let error = |key: &ProvenanceKey, reason: String| invalid(descriptor, key, reason);
        let mut aliases = BTreeMap::new();
        for (base, sites) in &scan.updates {
            let (key, _) = &sites[0];
            let occurrences = scan.aliases.get(base).map_or(&[][..], Vec::as_slice);
            let [found] = occurrences else {
                return Err(error(
                    key,
                    if occurrences.is_empty() {
                        format!(
                            "`..{base}` takes the fields it does not list from a record matched as `{base} @ Ctor {{ .. }}` in the left-hand side, but `{base}` is no such alias; a binder of the whole term names no fields K can read"
                        )
                    } else {
                        format!(
                            "`..{base}` needs one record to take its fields from, but the left-hand side binds `{base}` with `@` more than once"
                        )
                    },
                ));
            };
            if found.alternative {
                return Err(error(
                    key,
                    format!(
                        "`..{base}` needs the one record `{base}` matched, but `{base}` is bound inside a `|` alternative, which may match different records"
                    ),
                ));
            }
            let Some((record, pattern_fields)) =
                pattern_record(found.pattern, catalog, declarations)?
            else {
                return Err(error(
                    &found.key,
                    format!(
                        "`..{base}` updates a record, so `{base}` must alias a record pattern `{base} @ Ctor {{ .. }}` or `{base} @ Group {{ .. }}`"
                    ),
                ));
            };
            let declared = record_fields(&record, catalog, declarations)?;
            let mut needed = BTreeSet::new();
            for (site_key, site) in sites {
                let site_record = &site.record;
                if *site_record != record {
                    return Err(error(
                        site_key,
                        format!(
                            "`..{base}` builds a `{}` from `{base}`, which matched a `{}`; an update keeps the constructor of its base",
                            record_name(site_record),
                            record_name(&record)
                        ),
                    ));
                }
                needed.extend(
                    declared
                        .iter()
                        .filter(|field| !site.listed.contains(*field))
                        .cloned(),
                );
            }
            let mut fills = BTreeMap::new();
            for field in needed {
                let fill = match pattern_fields.get(&field) {
                    Some(DescriptorTerm::Variable { name, .. }) => Fill::Binder(name.clone()),
                    _ => Fill::Hidden(hidden_binder(base, &field)?),
                };
                fills.insert(field, fill);
            }
            aliases.insert(
                base.clone(),
                Alias {
                    key: found.key.clone(),
                    fills,
                },
            );
        }
        let dropped = aliases
            .keys()
            .filter(|name| !scan.whole.contains(*name))
            .cloned()
            .collect();
        Ok(Self { aliases, dropped })
    }

    /// Whether `name` is the alias of a base: its record pattern binds the
    /// fields the updates leave out.
    pub(super) fn is_base(&self, name: &str) -> bool {
        self.aliases.contains_key(name)
    }

    /// Whether the alias `name` occurs only as an update base, so its pattern
    /// is matched without `#as`.
    pub(super) fn is_dropped(&self, name: &str) -> bool {
        self.dropped.contains(name)
    }

    /// How an update of `base` fills `field`, which it leaves out.
    pub(super) fn fill(&self, base: &str, field: &ProductionFieldId) -> Option<&Fill> {
        self.aliases.get(base)?.fills.get(field)
    }

    /// The `name @ pattern` provenance of the base alias `name`.
    pub(super) fn alias_key(&self, name: &str) -> Option<&ProvenanceKey> {
        self.aliases.get(name).map(|alias| &alias.key)
    }
}

/// The hidden binder that matches `field` of the record aliased `base`.
fn hidden_binder(
    base: &str,
    field: &ProductionFieldId,
) -> Result<SemanticId, DescriptorLoweringError> {
    let field = field.as_str();
    let field = field.strip_prefix("r#").unwrap_or(field);
    Ok(SemanticId::new(format!(
        "{}update_{base}_{field}",
        krs_ir::ir::RESERVED_MARKER
    ))?)
}

fn invalid(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
    reason: String,
) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidRecordUpdate {
        item: Box::new(descriptor.id().clone()),
        reason,
        range: descriptor
            .provenance()
            .origin_for(key)
            .and_then(krs_ir::OriginStack::exact_authored_range)
            .map(Box::new),
    }
}

fn record_name(record: &Record) -> &str {
    match record {
        Record::Production(id) | Record::Cell(id) => id.item_name(),
    }
}

/// The term a record pattern gives each field it names.
type PatternFields<'a> = BTreeMap<ProductionFieldId, &'a DescriptorTerm>;

/// The record a pattern matches and the term it gives each field, by
/// position or by name; `None` for a pattern that is not one record.
fn pattern_record<'a>(
    pattern: &'a DescriptorTerm,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<Option<(Record, PatternFields<'a>)>, DescriptorLoweringError> {
    Ok(match pattern {
        DescriptorTerm::Application {
            reference,
            arguments,
            ..
        } => {
            let DescriptorApplicationRef::Declared(id) = &reference.application else {
                return Ok(None);
            };
            let record = Record::Production(id.clone());
            let declared = record_fields(&record, catalog, declarations)?;
            let fields = match arguments {
                krs_ir::Arguments::Positional(values) => declared
                    .into_iter()
                    .zip(values.iter().map(AsRef::as_ref))
                    .collect(),
                krs_ir::Arguments::Named(values) => values
                    .iter()
                    .map(|argument| (argument.field.clone(), argument.value.as_ref()))
                    .collect(),
            };
            Some((record, fields))
        }
        DescriptorTerm::Cell {
            declaration,
            fields,
            ..
        } => Some((
            Record::Cell(declaration.clone()),
            fields
                .iter()
                .map(|field| (field.field.clone(), field.value.as_ref()))
                .collect(),
        )),
        _ => None,
    })
}

/// The declared fields of a record, in declaration order.
fn record_fields(
    record: &Record,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<Vec<ProductionFieldId>, DescriptorLoweringError> {
    match record {
        Record::Production(id) => Ok(catalog
            .get(id)
            .map(|signature| {
                signature
                    .fields
                    .iter()
                    .map(|(field, _)| field.clone())
                    .collect()
            })
            .unwrap_or_default()),
        Record::Cell(id) => {
            let Some(declarations) = declarations else {
                return Ok(Vec::new());
            };
            declarations
                .cell(id)?
                .fields
                .iter()
                .map(|field| Ok(ProductionFieldId::new(&field.rust_field)?))
                .collect()
        }
    }
}

/// One `name @ pattern` occurrence.
struct AliasOccurrence<'a> {
    key: ProvenanceKey,
    pattern: &'a DescriptorTerm,
    /// Whether it lies inside a `|` alternative.
    alternative: bool,
}

/// One update `Record { listed.., ..base }`.
struct UpdateSite {
    record: Record,
    listed: BTreeSet<ProductionFieldId>,
}

#[derive(Default)]
struct Scan<'a> {
    aliases: BTreeMap<String, Vec<AliasOccurrence<'a>>>,
    updates: BTreeMap<String, Vec<(ProvenanceKey, UpdateSite)>>,
    /// Names the sentence reads as whole terms, not as update bases.
    whole: BTreeSet<String>,
}

impl<'a> Scan<'a> {
    fn update(&mut self, base: &DescriptorTerm, site: UpdateSite) {
        if let DescriptorTerm::Variable { key, name, .. } = base {
            self.updates
                .entry(name.clone())
                .or_default()
                .push((key.clone(), site));
        }
    }

    /// Walks a term; `alternative` is whether it lies inside `|`. The
    /// patterns of `k::matches!` and `let` bind local names, which are no
    /// rule binders, so they hold no base alias.
    fn walk(&mut self, term: &'a DescriptorTerm, alternative: bool) {
        match term {
            DescriptorTerm::Variable { name, .. } => {
                self.whole.insert(name.clone());
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                update,
                ..
            } => {
                for argument in arguments {
                    match argument {
                        krs_ir::TermArgumentRef::Positional { value }
                        | krs_ir::TermArgumentRef::Named { value, .. } => {
                            self.walk(value, alternative);
                        }
                    }
                }
                if let (Some(base), DescriptorApplicationRef::Declared(id)) =
                    (update, &reference.application)
                {
                    let listed = arguments
                        .iter()
                        .filter_map(|argument| match argument {
                            krs_ir::TermArgumentRef::Named { field, .. } => Some(field.clone()),
                            krs_ir::TermArgumentRef::Positional { .. } => None,
                        })
                        .collect();
                    self.update(
                        base,
                        UpdateSite {
                            record: Record::Production(id.clone()),
                            listed,
                        },
                    );
                }
            }
            DescriptorTerm::Cell {
                declaration,
                fields,
                update,
                ..
            } => {
                for field in fields {
                    self.walk(&field.value, alternative);
                }
                if let Some(base) = update {
                    self.update(
                        base,
                        UpdateSite {
                            record: Record::Cell(declaration.clone()),
                            listed: fields.iter().map(|field| field.field.clone()).collect(),
                        },
                    );
                }
            }
            DescriptorTerm::OrBool { arguments, .. } => {
                for argument in arguments.iter() {
                    self.walk(argument, alternative);
                }
            }
            DescriptorTerm::SortTest { operand, .. } => self.walk(operand, alternative),
            DescriptorTerm::As {
                key, name, pattern, ..
            } => {
                self.aliases
                    .entry(name.clone())
                    .or_default()
                    .push(AliasOccurrence {
                        key: key.clone(),
                        pattern,
                        alternative,
                    });
                self.walk(pattern, alternative);
            }
            DescriptorTerm::Or { alternatives, .. } => {
                for term in alternatives.iter() {
                    self.walk(term, true);
                }
            }
            DescriptorTerm::Matches { subject, .. } => self.walk(subject, alternative),
            DescriptorTerm::Let { value, body, .. } => {
                self.walk(value, alternative);
                self.walk(body, alternative);
            }
            DescriptorTerm::Closure { body, .. } => self.walk(body, alternative),
            DescriptorTerm::Rewrite { from, to, .. } => {
                self.walk(from, alternative);
                if let Some(to) = to {
                    self.walk(to, alternative);
                }
            }
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::Lexeme { .. } => {}
        }
    }
}

/// A sentence's record updates while its terms are lowered.
#[derive(Default)]
pub(super) struct RecordUpdateState {
    pub(super) updates: RecordUpdates,
    /// The base alias whose record pattern is lowered next.
    pub(super) alias: Option<String>,
    /// Hidden binders already declared as sentence variables.
    pub(super) declared: BTreeSet<SemanticId>,
    /// The next ordinal of a generated term's origin.
    pub(super) ordinal: usize,
}

impl RecordUpdates {
    /// The long form of `term`, which names every field: what `krs expand`
    /// writes (F5). A base alias's record pattern binds the fields its
    /// updates take to their hidden binders, an alias used only as a base
    /// loses its `@`, an update lists every field, and a group pattern's
    /// omitted children are `_`.
    ///
    /// # Errors
    ///
    /// Returns a lookup error for a cell declaration absent from
    /// `declarations`.
    pub(super) fn long_form(
        &self,
        term: &DescriptorTerm,
        catalog: &BTreeMap<StableItemId, ProductionSignature>,
        declarations: Option<&DescriptorIndex<'_>>,
    ) -> Result<DescriptorTerm, DescriptorLoweringError> {
        LongForm {
            updates: self,
            catalog,
            declarations,
        }
        .term(term, None)
    }

    /// The hidden binders the long form names, with the alias each belongs
    /// to, in a stable order.
    pub(super) fn hidden_binders(&self) -> Vec<SemanticId> {
        self.aliases
            .values()
            .flat_map(|alias| alias.fills.values())
            .filter_map(|fill| match fill {
                Fill::Hidden(id) => Some(id.clone()),
                Fill::Binder(_) => None,
            })
            .collect()
    }
}

struct LongForm<'a, 'b> {
    updates: &'a RecordUpdates,
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&'a DescriptorIndex<'b>>,
}

impl LongForm<'_, '_> {
    /// The long form of `term`; `alias` names the base alias whose record
    /// `term` is.
    fn term(
        &self,
        term: &DescriptorTerm,
        alias: Option<&str>,
    ) -> Result<DescriptorTerm, DescriptorLoweringError> {
        let mut term = term.clone();
        match &mut term {
            DescriptorTerm::As { name, pattern, .. } => {
                let base = self.updates.is_base(name).then(|| name.clone());
                let long = self.term(pattern, base.as_deref())?;
                if base.is_some() && self.updates.is_dropped(name) {
                    return Ok(long);
                }
                **pattern = long;
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                update,
                ..
            } => {
                let DescriptorApplicationRef::Declared(id) = &reference.application else {
                    self.children(&mut term)?;
                    return Ok(term);
                };
                let declared = record_fields(&Record::Production(id.clone()), self.catalog, None)?;
                let key = reference.key.clone();
                let mut values = match std::mem::take(arguments) {
                    krs_ir::Arguments::Positional(values) => declared
                        .iter()
                        .cloned()
                        .zip(values.into_iter().map(|value| *value))
                        .collect::<BTreeMap<_, _>>(),
                    krs_ir::Arguments::Named(values) => values
                        .into_iter()
                        .map(|argument| (argument.field, *argument.value))
                        .collect(),
                };
                for value in values.values_mut() {
                    *value = self.term(value, None)?;
                }
                let base = update.take();
                self.fill(&declared, &mut values, alias, base.as_deref(), &key);
                // A pattern's omitted fields are wildcards in the long form,
                // which `krs expand` writes positionally.
                let named = declared
                    .iter()
                    .filter_map(|field| {
                        values.remove(field).map(|value| krs_ir::NamedTermArgument {
                            key: key.clone(),
                            field: field.clone(),
                            value: Box::new(value),
                        })
                    })
                    .collect::<Vec<_>>();
                *arguments = krs_ir::Arguments::named(named);
            }
            DescriptorTerm::Cell {
                key,
                declaration,
                fields,
                open,
                update,
            } => {
                let declared = record_fields(
                    &Record::Cell(declaration.clone()),
                    self.catalog,
                    self.declarations,
                )?;
                let mut values = std::mem::take(fields)
                    .into_iter()
                    .map(|field| (field.field, *field.value))
                    .collect::<BTreeMap<_, _>>();
                for value in values.values_mut() {
                    *value = self.term(value, None)?;
                }
                let base = update.take();
                self.fill(&declared, &mut values, alias, base.as_deref(), key);
                if *open {
                    for field in &declared {
                        values
                            .entry(field.clone())
                            .or_insert_with(|| DescriptorTerm::Wildcard { key: key.clone() });
                    }
                }
                *open = false;
                *fields = declared
                    .iter()
                    .filter_map(|field| {
                        values
                            .remove(field)
                            .map(|value| krs_ir::DescriptorCellTermField {
                                key: key.clone(),
                                field: field.clone(),
                                value: Box::new(value),
                            })
                    })
                    .collect();
            }
            _ => self.children(&mut term)?,
        }
        Ok(term)
    }

    /// Fills the fields an update or a base alias's record pattern takes.
    fn fill(
        &self,
        declared: &[ProductionFieldId],
        values: &mut BTreeMap<ProductionFieldId, DescriptorTerm>,
        alias: Option<&str>,
        base: Option<&DescriptorTerm>,
        key: &ProvenanceKey,
    ) {
        let variable = |name: &str| DescriptorTerm::Variable {
            key: key.clone(),
            path_key: key.clone(),
            name: name.to_owned(),
        };
        for field in declared {
            if let Some(alias) = alias
                && let Some(Fill::Hidden(id)) = self.updates.fill(alias, field)
            {
                let hidden = variable(id.as_str());
                let value = match values.remove(field) {
                    None | Some(DescriptorTerm::Wildcard { .. }) => hidden,
                    Some(pattern) => DescriptorTerm::As {
                        key: key.clone(),
                        binding_key: key.clone(),
                        name: id.as_str().to_owned(),
                        pattern: Box::new(pattern),
                    },
                };
                values.insert(field.clone(), value);
            } else if let Some(DescriptorTerm::Variable { name, .. }) = base
                && !values.contains_key(field)
                && let Some(fill) = self.updates.fill(name, field)
            {
                let value = match fill {
                    Fill::Binder(binder) => variable(binder),
                    Fill::Hidden(id) => variable(id.as_str()),
                };
                values.insert(field.clone(), value);
            }
        }
    }

    /// Replaces each direct subterm of `term` by its long form.
    fn children(&self, term: &mut DescriptorTerm) -> Result<(), DescriptorLoweringError> {
        let replace = |slot: &mut DescriptorTerm| -> Result<(), DescriptorLoweringError> {
            *slot = self.term(slot, None)?;
            Ok(())
        };
        match term {
            DescriptorTerm::Application { arguments, .. } => match arguments {
                krs_ir::Arguments::Positional(values) => {
                    for value in values {
                        replace(value)?;
                    }
                }
                krs_ir::Arguments::Named(values) => {
                    let named = values
                        .iter()
                        .map(|argument| {
                            Ok(krs_ir::NamedTermArgument {
                                key: argument.key.clone(),
                                field: argument.field.clone(),
                                value: Box::new(self.term(&argument.value, None)?),
                            })
                        })
                        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
                    *arguments = krs_ir::Arguments::named(named);
                }
            },
            DescriptorTerm::OrBool { arguments, .. } => {
                *arguments = arguments.try_map_ref(|argument| self.term(argument, None))?;
            }
            DescriptorTerm::Or { alternatives, .. } => {
                *alternatives =
                    alternatives.try_map_ref(|alternative| self.term(alternative, None))?;
            }
            DescriptorTerm::SortTest { operand, .. } => replace(operand)?,
            DescriptorTerm::Matches {
                subject, pattern, ..
            } => {
                replace(subject)?;
                replace(pattern)?;
            }
            DescriptorTerm::Let {
                pattern,
                value,
                body,
                ..
            } => {
                replace(pattern)?;
                replace(value)?;
                replace(body)?;
            }
            DescriptorTerm::Closure { body, .. } => replace(body)?,
            DescriptorTerm::Rewrite { from, to, .. } => {
                replace(from)?;
                if let Some(to) = to {
                    replace(to)?;
                }
            }
            DescriptorTerm::As { pattern, .. } => replace(pattern)?,
            DescriptorTerm::Cell { fields, .. } => {
                for field in fields {
                    replace(&mut field.value)?;
                }
            }
            DescriptorTerm::Variable { .. }
            | DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::Lexeme { .. } => {}
        }
        Ok(())
    }
}

/// The long form of a readable rule or claim, as `krs expand` writes it
/// (F5): its terms name every field, an alias used only as an update base is
/// no binding, and the hidden binders of its updates are bindings.
///
/// # Errors
///
/// Returns the scan's diagnostics and lookup errors of the bundle.
pub(crate) fn head_rule_long_form(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<krs_ir::DescriptorHeadRule, DescriptorLoweringError> {
    let descriptors = bundle.descriptors().iter().collect::<Vec<_>>();
    let catalog = super::catalog::build_production_catalog(&descriptors)?;
    let declarations = DescriptorIndex::new(bundle);
    let updates = RecordUpdates::scan(
        descriptor,
        &super::rules::head_rule_terms(rule),
        &catalog,
        Some(&declarations),
    )?;
    let long = |term: &DescriptorTerm| updates.long_form(term, &catalog, Some(&declarations));
    let mut rule = rule.clone();
    if let Some(head) = &mut rule.head {
        for item in &mut head.items {
            *item = long(item)?;
        }
        match &mut head.result {
            Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => *term = long(term)?,
            Some(krs_ir::ProtocolHeadRuleResult::Splice(items)) => {
                for item in items {
                    *item = long(item)?;
                }
            }
            Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => {}
        }
    }
    for extra in &mut rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                for entry in entries {
                    entry.key = long(&entry.key)?;
                }
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap { update, .. } => *update = long(update)?,
            krs_ir::ProtocolHeadRuleExtra::RewriteCell { before, after, .. } => {
                *before = long(before)?;
                if let Some(after) = after {
                    *after = long(after)?;
                }
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteState { before, after, .. } => {
                long_state(before, &long)?;
                if let Some(after) = after {
                    long_state(after, &long)?;
                }
            }
        }
    }
    for condition in rule.requires.iter_mut().chain(&mut rule.ensures) {
        condition.term = long(&condition.term)?;
    }
    rule.bindings
        .retain(|binding| !updates.is_dropped(&binding.name));
    rule.bindings
        .extend(
            updates
                .hidden_binders()
                .into_iter()
                .map(|id| krs_ir::ProtocolHeadRuleBinding {
                    name: id.as_str().to_owned(),
                    refinement: None,
                }),
        );
    Ok(rule)
}

/// The long form of a structured rule's terms, as [`head_rule_long_form`].
///
/// # Errors
///
/// Returns the scan's diagnostics and lookup errors of the bundle.
pub(crate) fn structured_rule_long_form(
    descriptor: &Descriptor,
    rule: &krs_ir::StructuredRuleDescriptor,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<krs_ir::StructuredRuleDescriptor, DescriptorLoweringError> {
    let descriptors = bundle.descriptors().iter().collect::<Vec<_>>();
    let catalog = super::catalog::build_production_catalog(&descriptors)?;
    let terms = std::iter::once(&rule.subject)
        .chain(&rule.result)
        .chain(rule.requires.iter().map(|condition| &condition.term))
        .chain(rule.ensures.iter().map(|condition| &condition.term))
        .collect::<Vec<_>>();
    let updates = RecordUpdates::scan(descriptor, &terms, &catalog, None)?;
    let long = |term: &DescriptorTerm| updates.long_form(term, &catalog, None);
    let mut rule = rule.clone();
    rule.subject = long(&rule.subject)?;
    if let Some(result) = &mut rule.result {
        *result = long(result)?;
    }
    for condition in rule.requires.iter_mut().chain(&mut rule.ensures) {
        condition.term = long(&condition.term)?;
    }
    Ok(rule)
}

fn long_state(
    state: &mut krs_ir::ProtocolRuleStateTerm<DescriptorTerm>,
    long: &impl Fn(&DescriptorTerm) -> Result<DescriptorTerm, DescriptorLoweringError>,
) -> Result<(), DescriptorLoweringError> {
    match state {
        krs_ir::ProtocolRuleStateTerm::Term(term) | krs_ir::ProtocolRuleStateTerm::Group(term) => {
            *term = long(term)?;
        }
        krs_ir::ProtocolRuleStateTerm::Present { value } => long_state(value, long)?,
        krs_ir::ProtocolRuleStateTerm::KSequence(sequence) => {
            for item in &mut sequence.items {
                item.value = long(&item.value)?;
            }
        }
        krs_ir::ProtocolRuleStateTerm::Instances(instances) => {
            for instance in instances.front.iter_mut().chain(&mut instances.back) {
                for field in &mut instance.fields {
                    long_state(&mut field.value, long)?;
                }
            }
        }
        krs_ir::ProtocolRuleStateTerm::Map(_) | krs_ir::ProtocolRuleStateTerm::Absent => {}
    }
    Ok(())
}
