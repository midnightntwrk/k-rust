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
    ProtocolCellContent, ProvenanceKey, SemanticId, StableItemId,
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
    /// A group child the pattern matches with a group record: the child cell
    /// rebuilt from that record's own fills, which are those of the named
    /// record (its alias, or a generated name for a record with none) (N7).
    Group(String),
}

/// One base: where it is bound and how its updates are filled.
#[derive(Clone, Debug)]
struct Alias {
    /// The `name @ pattern` provenance, the origin of the hidden binders.
    key: ProvenanceKey,
    /// The `#[k::cell]` group the record is, for a group record.
    group: Option<StableItemId>,
    fills: BTreeMap<ProductionFieldId, Fill>,
}

/// The record updates of one sentence, read before its terms are inferred.
#[derive(Clone, Debug, Default)]
pub(super) struct RecordUpdates {
    /// Each base by its alias. A group record below a base with no alias of
    /// its own is named by its path, `o.frame`, which no binder spells.
    aliases: BTreeMap<String, Alias>,
    /// Aliases matched without `#as`: those that occur only as update bases,
    /// and every alias over a group record that can be rebuilt (N7).
    dropped: BTreeSet<String>,
    /// Aliases over a group record that the sentence uses whole: each use is
    /// the group rebuilt from its children, `G { ..o }` (N7).
    reconstructed: BTreeSet<String>,
}

/// A record whose fields the sentence takes, while the scan computes which.
struct Base<'a> {
    key: ProvenanceKey,
    record: Record,
    fields: PatternFields<'a>,
    /// The fields some update leaves out, or every field of a record rebuilt
    /// whole.
    needed: BTreeSet<ProductionFieldId>,
}

impl RecordUpdates {
    /// Reads the updates of a sentence whose terms are `terms`: patterns,
    /// results, and conditions.
    ///
    /// A whole use of an alias over a group record, `o @ G { .. }`, is the
    /// update that lists no field, `G { ..o }`: a group cell has fixed
    /// children, so the matched cell is the cell over its children's
    /// binders, and no conjunction has to stand among a cell's children
    /// (N7). A group child that a base's pattern matches with a group record
    /// is rebuilt the same way, from its own children.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorLoweringError::InvalidRecordUpdate`] for a base
    /// that is not the alias of exactly one record of the update's
    /// constructor or cell, outside `|`, and for a group child that must be
    /// rebuilt but is matched by a pattern no record rebuilds.
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
        let groups = scan.group_aliases(declarations);
        if scan.updates.is_empty() && groups.is_empty() {
            return Ok(Self::default());
        }
        let mut bases = update_bases(descriptor, &scan, catalog, declarations)?;
        let reconstructed = groups
            .keys()
            .filter(|name| scan.whole.contains(*name))
            .cloned()
            .collect::<BTreeSet<_>>();
        rebuild_children(
            descriptor,
            &mut bases,
            &groups,
            &reconstructed,
            catalog,
            declarations,
        )?;
        let aliases = alias_fills(&bases, catalog, declarations)?;
        let dropped = scan
            .updates
            .keys()
            .filter(|name| !scan.whole.contains(*name))
            .chain(groups.keys())
            .cloned()
            .collect();
        Ok(Self {
            aliases,
            dropped,
            reconstructed,
        })
    }

    /// Whether `name` is the alias of a base: its record pattern binds the
    /// fields the updates leave out.
    pub(super) fn is_base(&self, name: &str) -> bool {
        self.aliases.contains_key(name)
    }

    /// Whether the alias `name` is matched without `#as`: it occurs only as
    /// an update base, or it aliases a group record (N7).
    pub(super) fn is_dropped(&self, name: &str) -> bool {
        self.dropped.contains(name)
    }

    /// The group whose cell a use of `name` rebuilds, for an alias over a
    /// group record that the sentence uses whole (N7).
    pub(super) fn reconstructed(&self, name: &str) -> Option<&StableItemId> {
        if !self.reconstructed.contains(name) {
            return None;
        }
        self.group(name)
    }

    /// The group of the group record named `name` (an alias, or the path of
    /// a group child below one).
    pub(super) fn group(&self, name: &str) -> Option<&StableItemId> {
        self.aliases.get(name)?.group.as_ref()
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

/// The bases of the sentence's explicit updates, each with the fields its
/// updates leave out.
fn update_bases<'a>(
    descriptor: &Descriptor,
    scan: &Scan<'a>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<BTreeMap<String, Base<'a>>, DescriptorLoweringError> {
    let error = |key: &ProvenanceKey, reason: String| invalid(descriptor, key, reason);
    let mut bases = BTreeMap::<String, Base<'a>>::new();
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
        let Some((record, pattern_fields)) = pattern_record(found.pattern, catalog, declarations)?
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
        bases.insert(
            base.clone(),
            Base {
                key: found.key.clone(),
                record,
                fields: pattern_fields,
                needed,
            },
        );
    }
    Ok(bases)
}

/// Makes each whole-used group alias a record rebuilt whole, and each
/// group child that a rebuilt or updated record takes and its pattern
/// matches with a group record a record rebuilt from its own children: a
/// child alias by its name, a record with no alias by its path (N7).
fn rebuild_children<'a>(
    descriptor: &Descriptor,
    bases: &mut BTreeMap<String, Base<'a>>,
    groups: &BTreeMap<String, (ProvenanceKey, &'a DescriptorTerm)>,
    reconstructed: &BTreeSet<String>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<(), DescriptorLoweringError> {
    let error = |key: &ProvenanceKey, reason: String| invalid(descriptor, key, reason);
    let mut pending = Vec::new();
    for name in reconstructed {
        pending.push(name.clone());
        whole_group(bases, name, &groups[name], catalog, declarations)?;
    }
    pending.extend(bases.keys().cloned());
    // A group child an update takes is rebuilt from its own children, so
    // each child record that must be rebuilt needs every field in turn.
    while let Some(name) = pending.pop() {
        for (field, nested) in children_to_rebuild(&bases[&name], declarations)? {
            let child = match bases[&name].fields.get(&field).copied() {
                Some(DescriptorTerm::As { name: alias, .. }) if groups.contains_key(alias) => {
                    whole_group(bases, alias, &groups[alias], catalog, declarations)?
                        .then(|| alias.clone())
                }
                Some(pattern @ DescriptorTerm::Cell { declaration, .. })
                    if *declaration == nested =>
                {
                    let child = format!("{name}.{}", field.as_str());
                    let key = bases[&name].key.clone();
                    whole_group(bases, &child, &(key, pattern), catalog, declarations)?
                        .then_some(child)
                }
                _ => {
                    return Err(error(
                        &bases[&name].key,
                        format!(
                            "the group child `{}` of `{}` is taken whole, so it must be bound: write a binder, `_`, or a group record for it",
                            field.as_str(),
                            name.split('.').next().unwrap_or(&name)
                        ),
                    ));
                }
            };
            pending.extend(child);
        }
    }
    Ok(())
}

/// How each base fills the fields its updates take, with the hidden
/// binders of the sentence allocated in a stable order.
fn alias_fills(
    bases: &BTreeMap<String, Base<'_>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<BTreeMap<String, Alias>, DescriptorLoweringError> {
    let mut names = HiddenNames::default();
    let mut aliases = BTreeMap::new();
    for (name, base) in bases {
        let children = record_children(&base.record, catalog, declarations)?;
        let mut fills = BTreeMap::new();
        for (field, nested) in children {
            if !base.needed.contains(&field) {
                continue;
            }
            let fill = match (base.fields.get(&field).copied(), nested) {
                (Some(DescriptorTerm::Variable { name: binder, .. }), _) => {
                    Fill::Binder(binder.clone())
                }
                (Some(DescriptorTerm::As { name: alias, .. }), Some(_)) => {
                    Fill::Group(alias.clone())
                }
                (Some(DescriptorTerm::Cell { .. }), Some(_)) => {
                    Fill::Group(format!("{name}.{}", field.as_str()))
                }
                _ => Fill::Hidden(names.allocate(name, &field)?),
            };
            fills.insert(field, fill);
        }
        aliases.insert(
            name.clone(),
            Alias {
                key: base.key.clone(),
                group: match &base.record {
                    Record::Cell(id) => Some(id.clone()),
                    Record::Production(_) => None,
                },
                fills,
            },
        );
    }
    Ok(aliases)
}

/// Makes `name`, the group record `occurrence` matches, a record the
/// sentence rebuilds whole, so every one of its fields is needed; whether
/// it newly needs a field.
fn whole_group<'a>(
    bases: &mut BTreeMap<String, Base<'a>>,
    name: &str,
    (key, pattern): &(ProvenanceKey, &'a DescriptorTerm),
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<bool, DescriptorLoweringError> {
    let Some((record, fields)) = pattern_record(pattern, catalog, declarations)? else {
        return Ok(false);
    };
    let declared = record_fields(&record, catalog, declarations)?;
    let base = bases.entry(name.to_owned()).or_insert_with(|| Base {
        key: key.clone(),
        record,
        fields,
        needed: BTreeSet::new(),
    });
    let before = base.needed.len();
    base.needed.extend(declared);
    Ok(base.needed.len() != before)
}

/// The needed group children of a group base whose pattern names them,
/// with each child's group: those the base's fills rebuild.
fn children_to_rebuild(
    base: &Base<'_>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<Vec<(ProductionFieldId, StableItemId)>, DescriptorLoweringError> {
    let Record::Cell(_) = &base.record else {
        return Ok(Vec::new());
    };
    Ok(
        record_children(&base.record, &BTreeMap::new(), declarations)?
            .into_iter()
            .filter_map(|(field, nested)| {
                let nested = nested?;
                let named = base.fields.get(&field).copied();
                (base.needed.contains(&field)
                    && !matches!(
                        named,
                        None | Some(
                            DescriptorTerm::Variable { .. } | DescriptorTerm::Wildcard { .. }
                        )
                    ))
                .then_some((field, nested))
            })
            .collect(),
    )
}

/// The hidden binders of one sentence. A binder is named by its alias and
/// the path of fields below it, `update_o_frame_pc`, and one whose name is
/// already taken gets an ordinal, so distinct paths never share a binder
/// (`a.x_y` and `a_x.y` would otherwise both read `update_a_x_y`).
#[derive(Default)]
struct HiddenNames {
    taken: BTreeSet<String>,
}

impl HiddenNames {
    fn allocate(
        &mut self,
        alias: &str,
        field: &ProductionFieldId,
    ) -> Result<SemanticId, DescriptorLoweringError> {
        let path = alias
            .split('.')
            .chain(std::iter::once(field.as_str()))
            .map(|segment| segment.strip_prefix("r#").unwrap_or(segment))
            .collect::<Vec<_>>()
            .join("_");
        let base = format!("{}update_{path}", krs_ir::ir::RESERVED_MARKER);
        let mut name = base.clone();
        let mut ordinal = 2_usize;
        while !self.taken.insert(name.clone()) {
            name = format!("{base}_{ordinal}");
            ordinal += 1;
        }
        Ok(SemanticId::new(name)?)
    }
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

/// The declared fields of a record, in declaration order, each with the
/// group a group child of a `#[k::cell]` record is.
fn record_children(
    record: &Record,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&DescriptorIndex<'_>>,
) -> Result<Vec<(ProductionFieldId, Option<StableItemId>)>, DescriptorLoweringError> {
    let (Record::Cell(id), Some(declarations)) = (record, declarations) else {
        return Ok(record_fields(record, catalog, declarations)?
            .into_iter()
            .map(|field| (field, None))
            .collect());
    };
    declarations
        .cell(id)?
        .fields
        .iter()
        .map(|field| {
            let nested = match &field.content {
                ProtocolCellContent::Nested { declaration } => {
                    Some(declaration.declaration.clone())
                }
                ProtocolCellContent::Leaf { .. } => None,
            };
            Ok((ProductionFieldId::new(&field.rust_field)?, nested))
        })
        .collect()
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
    /// The aliases over a group record that a sentence binds once, outside
    /// `|`, with the provenance and pattern of each: the matched cell is
    /// fixed by its children, which the pattern can bind (N7). None without
    /// the cell declarations, which give the children.
    fn group_aliases(
        &self,
        declarations: Option<&DescriptorIndex<'_>>,
    ) -> BTreeMap<String, (ProvenanceKey, &'a DescriptorTerm)> {
        if declarations.is_none() {
            return BTreeMap::new();
        }
        self.aliases
            .iter()
            .filter_map(|(name, occurrences)| match occurrences.as_slice() {
                [
                    found @ AliasOccurrence {
                        pattern: DescriptorTerm::Cell { .. },
                        alternative: false,
                        ..
                    },
                ] => Some((name.clone(), (found.key.clone(), found.pattern))),
                _ => None,
            })
            .collect()
    }

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
    /// or over a group record loses its `@`, an update lists every field, a
    /// whole use of an alias over a group record is the group rebuilt from
    /// its children (N7), and a group pattern's omitted children are `_`.
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
                Fill::Binder(_) | Fill::Group(_) => None,
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
                if self.updates.is_dropped(name) {
                    return Ok(long);
                }
                **pattern = long;
            }
            DescriptorTerm::Variable { key, name, .. } => {
                if let Some(group) = self.updates.reconstructed(name) {
                    return self.rebuilt(key, group, name);
                }
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
                self.fill(&declared, &mut values, alias, base.as_deref(), &key)?;
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
                for (field, value) in &mut values {
                    *value = self.term(value, self.child_record(alias, field, value))?;
                }
                let base = update.take();
                self.fill(&declared, &mut values, alias, base.as_deref(), key)?;
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

    /// The record whose fills a group child `value` of the base alias's
    /// record `alias` binds: a group child the alias's fills rebuild binds
    /// its own children (N7).
    fn child_record<'a>(
        &'a self,
        alias: Option<&str>,
        field: &ProductionFieldId,
        value: &DescriptorTerm,
    ) -> Option<&'a str> {
        match (
            alias.and_then(|alias| self.updates.fill(alias, field)),
            value,
        ) {
            (Some(Fill::Group(child)), DescriptorTerm::Cell { .. }) => Some(child),
            _ => None,
        }
    }

    /// The group record `name` rebuilt from its children: what a whole use
    /// of an alias over a group record, or a group child an update takes,
    /// stands for (N7).
    fn rebuilt(
        &self,
        key: &ProvenanceKey,
        group: &StableItemId,
        name: &str,
    ) -> Result<DescriptorTerm, DescriptorLoweringError> {
        self.term(
            &DescriptorTerm::Cell {
                key: key.clone(),
                declaration: group.clone(),
                fields: Vec::new(),
                open: false,
                update: Some(Box::new(DescriptorTerm::Variable {
                    key: key.clone(),
                    path_key: key.clone(),
                    name: name.to_owned(),
                })),
            },
            None,
        )
    }

    /// Fills the fields an update or a base alias's record pattern takes.
    fn fill(
        &self,
        declared: &[ProductionFieldId],
        values: &mut BTreeMap<ProductionFieldId, DescriptorTerm>,
        alias: Option<&str>,
        base: Option<&DescriptorTerm>,
        key: &ProvenanceKey,
    ) -> Result<(), DescriptorLoweringError> {
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
                    Fill::Group(child) => {
                        let group = self
                            .updates
                            .group(child)
                            .expect("a rebuilt group child is a group record");
                        self.rebuilt(key, group, child)?
                    }
                };
                values.insert(field.clone(), value);
            }
        }
        Ok(())
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
            krs_ir::ProtocolHeadRuleExtra::RewriteList { before, after, .. } => {
                for term in before.terms_mut().into_iter().chain(
                    after
                        .iter_mut()
                        .flat_map(krs_ir::ProtocolHeadRuleList::terms_mut),
                ) {
                    *term = long(term)?;
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
    // The long form reads the cell declarations, as lowering does: a group
    // record's children come from its declaration.
    let declarations = DescriptorIndex::new(bundle);
    let updates = RecordUpdates::scan(descriptor, &terms, &catalog, Some(&declarations))?;
    let long = |term: &DescriptorTerm| updates.long_form(term, &catalog, Some(&declarations));
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
