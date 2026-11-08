//! The syntax family of a `coverage` document at the KRS level: productions named by Rust path,
//! and the values of every `k::bits!` template's fields with their concrete encodings.
//!
//! kink-flow's syntax family (`kink_flow::coverage`, "Syntax") counts each production of an
//! authored sort as reached when a fired instance of a counted sentence inspected it, took it as
//! an operand or built it, and records the values of the template binders a front end selects.
//! It knows neither which sorts the author declared nor what a template is. This module gives
//! both ([`KrsSyntax::selection`], `kink_flow::FlowManifest::with_syntax`) and names what
//! kink-flow reports ([`KrsSyntax::annotate`]).
//!
//! # Authored sorts
//!
//! A sort is authored when a KRS item of one of the definition's packages declares it: its
//! symbol records the Rust path of its declaration. Excluded are the sorts no item declares,
//! which KRS generates (a cell's, a grammar registration's), the sorts of K's builtin modules
//! (`Int`, `Map`), which no package declares and whose values are domain values, and the sorts
//! of KRS's framework package (`KItem`, `KResult`), which KRS declares for every definition as
//! K's categories, so no author wrote them.
//!
//! Every package of the definition counts, a dependency's as the root's. The corpus judges one
//! definition, the one the emission wrote, and the rules family already counts every rule of it,
//! a dependency's included; the syntax family judges the same definition, so its universe is
//! that definition's syntax, and one definition has one universe. Counting only the root
//! package's sorts would judge a definition the corpus does not run: the rules over a
//! dependency's syntax would be obligations while the syntax they inspect and build would not.
//! The consequence is that a constructor of a shared syntax crate that this definition never
//! builds or inspects is an open obligation of this corpus, as an unfired rule of that crate is;
//! a project that does not mean to exercise it argues so for that item. kink-flow keeps of each
//! authored sort the productions that build a term with a constructor.
//!
//! # Productions by Rust path
//!
//! A production item gains `krs = {item, file, line, column}`: the Rust path of the variant or
//! struct that declares it, spelled as rules are (`crate::Instr::Ld` in the root package,
//! `lang::Op::Add` in a dependency; [`krs_exec::item_spelling`]), and the declaration's position.
//! kink-flow names the item and its target by `krs.item`, so the item's id is
//! `syntax:crate::Instr::Ld`.
//!
//! # Field values
//!
//! A `k::bits!` template `T` of width `w` in a rule or equation `S` binds one `Int` variable,
//! its binder, and each field `f` reads a function of the binder. `T` matches exactly the points
//! `v` with `0 <= v < 2^w` whose fixed bits (`0` and `1`) are as written, so its points are the
//! fixed bits with each assignment of its free bits (its holes `_` and its fields' letters), and
//! only those are enumerated. The template's arm domain is the set of its points at which no
//! conjunct of `S`'s condition after the templates' tests is decided false. The front end reads
//! each field through the language's own rewrite of the template,
//! [`krs_syntax::desugar_bit_templates`], applied to a function whose one parameter is the
//! pattern as the author wrote it, whose result reads each field as the sentence reads it.
//!
//! A conjunct is read as the emitted K term it is, whose nodes the source map pairs with the
//! authored source ([`super::guards::GuardNames::sentence_templates`]), not as the Rust the
//! author wrote: a Rust call or method is the builtin only where KRS resolved it to the builtin,
//! and the K says what it resolved to. A conjunct is decided at a point where its term is built
//! from literals, the template's binder, and K's builtin operations of `Int` and `Bool`
//! (comparisons, `+Int`, `-Int`, `*Int`, `/Int`, `%Int`, `divInt`, `modInt`, the bitwise
//! operations and shifts, `bitRangeInt`, and the Boolean connectives), each evaluated as K
//! defines it and undecided where K leaves it undefined (a division by zero); a field occurs in
//! the K as its bit-range term of the binder, so a literal hole such as `op != 0x76` and a
//! condition on a field are decided. Any other term, a function the definition declares
//! included whatever its Rust name, is undecided, and a conjunct that is not decided is taken to
//! hold; a conjunction with a false operand is false and a disjunction with a true one true,
//! whatever the other. So the domain contains every value a fired instance can bind, and is
//! exact where every conjunct is decided. The universe of `T` is each `(T, f, f(v))` for `v` in
//! the domain: a field value no point gives cannot be reached by any input, and one some point
//! gives can. A template with more than 16 free bits is not enumerated (at most 2^16 points per
//! template); its field values are no obligation, and the document lists it under
//! `families.syntax.krs.unenumerated` with the reason, as it does a template whose layout or
//! whose sentence's condition cannot be read. A template with holes and no field has no field
//! value, so it gives no item and is not listed.
//!
//! Every baseline run records the binder's values at the fired instances of `S`
//! ([`KrsSyntax::selection`]: the axiom by its label as the loaded definition stores it, the
//! variable as the compiled definition writes it, the cap the domain's size, so no value a fired
//! instance binds is left out; a template without a field records nothing). A field value is
//! reached when some comparable program's run bound the binder to a value `b` with `f(b)` the
//! value. Each item of kind `field-value` is
//! `{kind, template, field, value, status, reached_by, uncounted: {operand_of}, krs}`, with
//! `krs = {item, rule, label, file, line, column, encodings, matched_by, target}`: `item` names
//! it (`crate::decode_ld:r=3`), `encodings` are the points of the domain where the field has the
//! value, in hexadecimal and in runs, the inputs an author writes to reach it, and `matched_by`
//! the programs whose runs matched the sentence's templates (its row's `krs.matched_by`), the
//! cases closest to one that reaches the value. The target writes the value in decimal, then
//! the field's bits as the template places them (`= 2 (0b10)`), labelled `template bits` where
//! they read as another number than the value (a field a modifier places or reads signed:
//! `= 16 (template bits 0b001)`). Only templates of sentences of the rules
//! universe (`fired`, `matched` or `unmatched`) give items, as only those sentences' instances
//! count.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir_levels::{DefinitionSentence, SymbolIdentity};
use serde_json::{Value, json};
use syn::{BinOp, Expr, Lit, UnOp};

use super::annotate::qualified;
use super::guards::{GuardNames, KTerm, TemplateSite};
use crate::{DiagnosticSources, EmittedDefinition};

/// The K namespace of KRS's framework package, whose sorts are K's categories.
const FRAMEWORK_NAMESPACE: &str = "KRS-FRAMEWORK";

/// The most free bits (holes and fields) of a template whose points are enumerated.
const MAXIMUM_ENUMERATED_FREE_BITS: u32 = 16;

/// The most runs of encodings a target's text lists.
const LISTED_RUNS: usize = 8;

/// The rules family's statuses whose sentences count (kink-flow's rules universe).
const COUNTED: [&str; 3] = [
    kink_flow::coverage::FIRED,
    kink_flow::coverage::MATCHED,
    kink_flow::coverage::UNMATCHED,
];

/// The syntax family of one emission at the KRS level (module documentation).
pub(crate) struct KrsSyntax {
    /// The authored sorts, by K name.
    sorts: BTreeSet<String>,
    /// Each authored production's Rust name and position, by its K label.
    productions: BTreeMap<String, Value>,
    /// Each strict production's Rust name and position and the field of each of its
    /// nonterminals in order, by its K label ([`Self::name_heating`]).
    strict: BTreeMap<String, (Value, Vec<String>)>,
    /// Every template of a rule or equation, in emission order.
    templates: Vec<Template>,
}

/// One `k::bits!` template of a sentence.
struct Template {
    module: String,
    /// The sentence's label as the emission writes it.
    label: String,
    /// The sentence's label as the loaded definition stores it, which selects its binder.
    stored: String,
    /// The KRS item of the sentence, as rules are named.
    rule: Option<String>,
    /// The binder as the compiled definition writes it (`VarOp`).
    variable: String,
    literal: Option<String>,
    file: Option<String>,
    line: Option<u32>,
    column: Option<u32>,
    /// The template's layout and arm domain, or why it is not enumerated.
    layout: Result<Layout, String>,
}

/// A template's arm domain and its fields' values on it.
struct Layout {
    width: u32,
    /// The fields, in the order their letters first occur.
    fields: Vec<Field>,
    /// Each point of the arm domain, ascending, with its fields' values in field order.
    points: Vec<(u128, Vec<i128>)>,
}

impl Layout {
    /// The fields' values at `point`, where it is a point of the arm domain.
    fn values(&self, point: u128) -> Option<&[i128]> {
        let at = self
            .points
            .binary_search_by_key(&point, |(point, _)| *point)
            .ok()?;
        Some(&self.points[at].1)
    }
}

/// A field of a template: its letter and its template bits, most significant first.
struct Field {
    letter: char,
    positions: Vec<u32>,
}

impl KrsSyntax {
    /// The syntax family of `emitted`, whose guards `names` reads, positioning declarations in
    /// the source `sources` reads.
    pub(crate) fn new(
        emitted: &EmittedDefinition,
        names: &GuardNames,
        sources: &DiagnosticSources,
    ) -> Self {
        let definition = &emitted.ir;
        let mut sorts = BTreeSet::new();
        let mut productions = BTreeMap::new();
        let mut strict = BTreeMap::new();
        let text = sources.clone();
        let mut origins =
            krs_exec::Origins::new(Some(Box::new(move |file| text.source_text(file))));
        for module in definition.modules() {
            for sentence in module.sentences() {
                if let DefinitionSentence::Production(production) = sentence
                    && production.attributes().iter().any(|attribute| {
                        matches!(attribute, krs_ir::ProductionAttribute::Strictness { .. })
                    })
                    && let Some(path) = krs_exec::item_spelling(definition, sentence.origin())
                {
                    let span = origins.span(sentence.origin());
                    let fields = production
                        .items()
                        .iter()
                        .filter_map(|item| match item.kind() {
                            krs_ir::GrammarProductionItemKind::NonTerminal { field, .. } => {
                                Some(field.as_str().to_owned())
                            }
                            _ => None,
                        })
                        .collect();
                    strict.insert(
                        production.symbol().emitted_name().to_owned(),
                        (
                            json!({
                                "item": path,
                                "file": span.as_ref().map(|span| span.file.clone()),
                                "line": span.as_ref().and_then(|span| span.line),
                                "column": span.as_ref().and_then(|span| span.column),
                            }),
                            fields,
                        ),
                    );
                }
                match sentence {
                    DefinitionSentence::SyntaxSort(sort) if authored(sentence, sort.symbol()) => {
                        sorts.insert(sort.symbol().emitted_name().to_owned());
                    }
                    DefinitionSentence::Production(production)
                        if authored(sentence, production.symbol()) =>
                    {
                        let Some(path) = krs_exec::item_spelling(definition, sentence.origin())
                        else {
                            continue;
                        };
                        let span = origins.span(sentence.origin());
                        productions.insert(
                            production.symbol().emitted_name().to_owned(),
                            json!({
                                "item": path,
                                "file": span.as_ref().map(|span| span.file.clone()),
                                "line": span.as_ref().and_then(|span| span.line),
                                "column": span.as_ref().and_then(|span| span.column),
                            }),
                        );
                    }
                    _ => {}
                }
            }
        }
        let mut templates = Vec::new();
        for rule in &emitted.rules {
            let reading = names.sentence_templates(&rule.label);
            for site in &reading.templates {
                let Some(stored) = names.stored_label(&rule.module, &rule.label) else {
                    continue;
                };
                templates.push(Template {
                    module: rule.module.clone(),
                    label: rule.label.clone(),
                    stored,
                    rule: rule.item.clone(),
                    variable: k_rust::kast::identifier::encode_variable(
                        &site.variable,
                        k_rust::kore::ast::VariableKind::Element,
                    ),
                    literal: site.literal.clone(),
                    file: site.file.clone(),
                    line: site.line,
                    column: site.column,
                    layout: layout(site, &reading.conjuncts),
                });
            }
        }
        Self {
            sorts,
            productions,
            strict,
            templates,
        }
    }

    /// Name the heating items of a `coverage` document's rules family at the KRS level: a heating
    /// rule of a strict production (kink-flow's item of kind `heating`, `heating.production` its K
    /// label and `heating.position` the 1-based argument position) gains
    /// `krs = {item, field, file, line, column}`, the Rust path and position of the variant or
    /// struct that declares the production, as the syntax family names it, and the field the
    /// position is: the production's nonterminals are its fields in the order the declaration
    /// writes them, which is the order of the K production's arguments. kink-flow names the item
    /// by both (`rule:crate::Exp::Add:heat:lhs`). A `context`'s heating rule is named by the
    /// context's own item, as its rules are. Applying it twice gives what applying it once does.
    pub(crate) fn name_heating(&self, document: &mut Value) {
        let Some(items) = document["families"]["rules"]["items"].as_array_mut() else {
            return;
        };
        for item in items {
            if item["kind"] != kink_flow::coverage::HEATING {
                continue;
            }
            let Some((name, fields)) = item["heating"]["production"]
                .as_str()
                .and_then(|label| self.strict.get(label))
            else {
                continue;
            };
            let mut krs = name.clone();
            krs["field"] = item["heating"]["position"]
                .as_u64()
                .and_then(|position| usize::try_from(position).ok()?.checked_sub(1))
                .and_then(|index| fields.get(index))
                .map_or(Value::Null, |field| json!(field));
            item["krs"] = krs;
        }
    }

    /// kink-flow's reading of the syntax family: the authored sorts, and each enumerated
    /// template's binder, selected by its sentence's label as the loaded definition stores it and
    /// capped at its domain's size.
    pub(crate) fn selection(&self) -> kink_flow::manifest::SyntaxSelection {
        kink_flow::manifest::SyntaxSelection {
            sorts: self.sorts.clone(),
            binders: self
                .templates
                .iter()
                .filter_map(|template| {
                    // A template without a field has no value to record.
                    let layout = template
                        .layout
                        .as_ref()
                        .ok()
                        .filter(|layout| !layout.fields.is_empty())?;
                    Some((
                        template.stored.clone(),
                        template.variable.clone(),
                        layout.points.len(),
                    ))
                })
                .collect(),
        }
    }

    /// Name the syntax family of the `coverage` document `document` (module documentation): each
    /// production item gains its Rust name, and each enumerated template of a counted sentence
    /// gives its field-value items. Applying it twice gives what applying it once does.
    pub(crate) fn annotate(&self, document: &mut Value) {
        if !document["families"]["syntax"]["items"].is_array() {
            return;
        }
        let programs = document["programs"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|program| program["id"].as_str().map(str::to_owned))
            .collect::<Vec<_>>();
        let rules = document["families"]["rules"]["items"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        let family = &mut document["families"]["syntax"];
        let binders = family["binders"].as_array().cloned().unwrap_or_default();
        let readable = family.get("reason").is_none() && family["binders"].is_array();
        let Some(items) = family["items"].as_array_mut() else {
            return;
        };
        // The field-value items of an earlier application, by name, whose derived fields
        // (kink-flow's `derive`) a new item of the same name keeps.
        let mut previous = BTreeMap::new();
        items.retain(|item| {
            if item["kind"] != kink_flow::coverage::FIELD_VALUE {
                return true;
            }
            if let Some(name) = item["krs"]["item"].as_str() {
                previous.insert(name.to_owned(), item.clone());
            }
            false
        });
        for item in items.iter_mut() {
            if let Some(name) = item["production"]
                .as_str()
                .and_then(|label| self.productions.get(label))
            {
                item["krs"] = name.clone();
            }
        }
        let mut unenumerated = Vec::new();
        if readable {
            let names = self.field_names();
            for (template, name) in self.templates.iter().zip(names) {
                let Some(rule) = rules
                    .iter()
                    .find(|rule| same_sentence(rule, &template.module, &template.label))
                else {
                    continue;
                };
                if !COUNTED.contains(&rule["status"].as_str().unwrap_or_default()) {
                    continue;
                }
                match &template.layout {
                    Ok(layout) => {
                        let binder = binders.iter().find(|binder| {
                            binder["variable"] == template.variable.as_str()
                                && binder["sentences"].as_array().is_some_and(|sentences| {
                                    sentences.iter().any(|sentence| {
                                        same_sentence(sentence, &template.module, &template.label)
                                    })
                                })
                        });
                        for item in template.items(layout, &name, binder, rule, &programs) {
                            let kept = item["krs"]["item"]
                                .as_str()
                                .and_then(|name| previous.remove(name));
                            items.push(match (kept, item) {
                                (Some(Value::Object(mut kept)), Value::Object(item)) => {
                                    kept.extend(item);
                                    Value::Object(kept)
                                }
                                (_, item) => item,
                            });
                        }
                    }
                    Err(reason) => unenumerated.push(json!({
                        "rule": template.rule,
                        "label": template.label,
                        "template": template.literal,
                        "file": template.file,
                        "line": template.line,
                        "reason": reason,
                    })),
                }
            }
        }
        if unenumerated.is_empty() {
            if let Some(krs) = family.get_mut("krs").and_then(Value::as_object_mut) {
                krs.remove("unenumerated");
            }
        } else {
            family["krs"]["unenumerated"] = json!(unenumerated);
        }
    }

    /// The name of each template's field values, by template: its sentence's KRS item, else its
    /// label where no item names it or two templated sentences share the item.
    fn field_names(&self) -> Vec<String> {
        let mut counts = BTreeMap::<&str, BTreeSet<&str>>::new();
        for template in &self.templates {
            if let Some(rule) = &template.rule {
                counts
                    .entry(rule.as_str())
                    .or_default()
                    .insert(template.label.as_str());
            }
        }
        self.templates
            .iter()
            .map(|template| match &template.rule {
                Some(rule) if counts[rule.as_str()].len() == 1 => rule.clone(),
                _ => template.label.clone(),
            })
            .collect()
    }
}

impl Template {
    /// The field-value items of this template, named after `name`, of the comparable and other
    /// programs `binder` (kink-flow's `families.syntax.binders` entry, if some program bound the
    /// binder) lists; `rule` is the sentence's rules item and `programs` the document's.
    fn items(
        &self,
        layout: &Layout,
        name: &str,
        binder: Option<&Value>,
        rule: &Value,
        programs: &[String],
    ) -> Vec<Value> {
        // The programs behind each field's values, comparable then not.
        let mut by_value: Vec<[BTreeMap<i128, BTreeSet<&str>>; 2]> =
            layout.fields.iter().map(|_| Default::default()).collect();
        for (slot, values) in [
            binder.map(|binder| &binder["values"]),
            binder.map(|binder| &binder["uncounted"]["values"]),
        ]
        .into_iter()
        .enumerate()
        {
            for entry in values.and_then(Value::as_array).into_iter().flatten() {
                let Some(point) = entry["value"]
                    .as_str()
                    .and_then(|value| value.parse::<u128>().ok())
                else {
                    continue;
                };
                let Some(fields) = layout.values(point) else {
                    continue;
                };
                for (index, value) in fields.iter().enumerate() {
                    by_value[index][slot].entry(*value).or_default().extend(
                        entry["programs"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .filter_map(Value::as_str),
                    );
                }
            }
        }
        let ordered = |set: Option<&BTreeSet<&str>>| -> Vec<String> {
            programs
                .iter()
                .filter(|program| set.is_some_and(|set| set.contains(program.as_str())))
                .cloned()
                .collect()
        };
        let matched_by = rule["krs"]
            .get("matched_by")
            .cloned()
            .unwrap_or(Value::Null);
        let rule_name = self.rule.clone().unwrap_or_else(|| self.label.clone());
        let mut items = Vec::new();
        for (index, field) in layout.fields.iter().enumerate() {
            let letter = field.letter;
            let mut encodings = BTreeMap::<i128, Vec<u128>>::new();
            for (point, fields) in &layout.points {
                encodings.entry(fields[index]).or_default().push(*point);
            }
            for (value, points) in encodings {
                let reached_by = ordered(by_value[index][0].get(&value));
                let uncounted = ordered(by_value[index][1].get(&value));
                let runs = runs(&points, layout.width);
                let shown = value_text(value, field, points[0]);
                let mut target = format!(
                    "a case in which {rule_name} fires with field {letter} of k::bits!({:?}) = {shown}: {}",
                    self.literal.as_deref().unwrap_or_default(),
                    listed_encodings(&runs),
                );
                match matched_by.as_array() {
                    Some(matched) if !matched.is_empty() => {
                        target.push_str("; the cases that match its templates: ");
                        target.push_str(
                            &matched
                                .iter()
                                .filter_map(Value::as_str)
                                .collect::<Vec<_>>()
                                .join(", "),
                        );
                    }
                    Some(_) => target.push_str("; no comparable case matches its templates"),
                    None => {}
                }
                items.push(json!({
                    "kind": kink_flow::coverage::FIELD_VALUE,
                    "template": self.literal,
                    "field": letter.to_string(),
                    "value": value.to_string(),
                    "status": if reached_by.is_empty() {
                        kink_flow::coverage::UNREACHED
                    } else {
                        kink_flow::coverage::REACHED
                    },
                    "reached_by": reached_by,
                    "uncounted": {"operand_of": uncounted},
                    "krs": {
                        "item": format!("{name}:{letter}={value}"),
                        "rule": self.rule,
                        "label": self.label,
                        "file": self.file,
                        "line": self.line,
                        "column": self.column,
                        "encodings": runs,
                        "matched_by": matched_by,
                        "target": target,
                    },
                }));
            }
        }
        items
    }
}

/// Whether `symbol`, of the syntax sentence `sentence`, is authored (module documentation,
/// "Authored sorts"): an item declares it, and that item is not of the framework package.
fn authored(sentence: &DefinitionSentence, symbol: &SymbolIdentity) -> bool {
    symbol.declaration().is_some()
        && sentence
            .item()
            .is_none_or(|item| item.package().k_namespace() != FRAMEWORK_NAMESPACE)
}

/// Whether the document object `object` (`{module, index, label}`) names the sentence of
/// `module` labelled `label`.
fn same_sentence(object: &Value, module: &str, label: &str) -> bool {
    object["module"] == module
        && object["label"]
            .as_str()
            .is_some_and(|written| qualified(written, module) == qualified(label, module))
}

/// The layout and arm domain of the template `site`, whose sentence's condition has the
/// conjuncts `conjuncts` after its templates' tests (module documentation, "Field values").
fn layout(site: &TemplateSite, conjuncts: &Result<Vec<KTerm>, String>) -> Result<Layout, String> {
    let conjuncts = conjuncts
        .as_ref()
        .map_err(|reason| format!("its sentence's condition cannot be read: {reason}"))?;
    let literal = site
        .literal
        .as_deref()
        .ok_or("the template's string cannot be read from the source")?;
    let pattern = site
        .pattern
        .as_deref()
        .ok_or("the template's pattern cannot be read from the source")?;
    // The template's bits, most significant first: `0` and `1` are fixed, `_` and a field letter
    // free.
    let bits = literal
        .chars()
        .filter(|character| matches!(character, '0' | '1' | '_') || character.is_ascii_lowercase())
        .collect::<Vec<_>>();
    let width = u32::try_from(bits.len()).map_err(|_| "the template is too wide")?;
    let mut fixed = 0_u128;
    let mut free = Vec::new();
    let mut fields = Vec::<Field>::new();
    for (position, character) in (0..width).rev().zip(&bits) {
        match character {
            '0' => {}
            '1' => fixed |= 1 << position,
            '_' => free.push(position),
            letter => {
                free.push(position);
                match fields.iter_mut().find(|field| field.letter == *letter) {
                    Some(field) => field.positions.push(position),
                    None => fields.push(Field {
                        letter: *letter,
                        positions: vec![position],
                    }),
                }
            }
        }
    }
    // A template without a field has no field value, so nothing of it is enumerated.
    if fields.is_empty() {
        return Ok(Layout {
            width,
            fields,
            points: Vec::new(),
        });
    }
    let free_bits = u32::try_from(free.len()).unwrap_or(u32::MAX);
    if free_bits > MAXIMUM_ENUMERATED_FREE_BITS {
        return Err(format!(
            "the template has {free_bits} free bits, more than the {MAXIMUM_ENUMERATED_FREE_BITS} whose values are enumerated"
        ));
    }
    if width >= i128::BITS {
        return Err(format!(
            "the template is {width} bits wide, wider than the {} bits its values are evaluated in",
            i128::BITS - 1
        ));
    }
    let (binder, terms) = rewritten(pattern, &fields)?;
    let terms = terms
        .iter()
        .map(|term| Term::of_rewrite(term, &binder))
        .collect::<Vec<_>>();
    let conjuncts = conjuncts
        .iter()
        .map(|conjunct| Term::of_k(conjunct, &site.variable))
        .collect::<Vec<_>>();
    // Free bits ascending, so that the points come ascending.
    free.reverse();
    let mut points = Vec::new();
    for index in 0..(1_u128 << free_bits) {
        let point = free
            .iter()
            .enumerate()
            .filter(|(bit, _)| (index >> bit) & 1 == 1)
            .fold(fixed, |point, (_, position)| point | (1 << position));
        let value = point.cast_signed();
        if conjuncts
            .iter()
            .any(|conjunct| conjunct.value(value) == Some(Val::Bool(false)))
        {
            continue;
        }
        let values = terms
            .iter()
            .map(|term| match term.value(value) {
                Some(Val::Int(field)) => Ok(field),
                _ => Err("a field of the rewritten template is no integer term"),
            })
            .collect::<Result<Vec<_>, _>>()?;
        points.push((point, values));
    }
    Ok(Layout {
        width,
        fields,
        points,
    })
}

/// The template whose pattern the author wrote `pattern`, with the fields `fields`, rewritten by
/// the language's own rewrite ([`krs_syntax::desugar_bit_templates`]) on a function whose one
/// parameter it is: the binder's name and each field's term.
fn rewritten(pattern: &str, fields: &[Field]) -> Result<(String, Vec<Expr>), String> {
    let letters = fields
        .iter()
        .map(|field| field.letter.to_string())
        .collect::<Vec<_>>();
    let source = format!(
        "fn layout({pattern}: Int) -> Int {{ ({},) }}",
        letters.join(", ")
    );
    let mut item = syn::parse_str::<syn::ItemFn>(&source)
        .map_err(|error| format!("the template's pattern does not parse: {error}"))?;
    krs_syntax::desugar_bit_templates(&mut item)
        .map_err(|error| format!("the template does not rewrite: {error}"))?;
    let binder = match item.sig.inputs.first() {
        Some(syn::FnArg::Typed(typed)) => match &*typed.pat {
            syn::Pat::Ident(ident) => ident.ident.to_string(),
            _ => return Err("the rewritten template binds no variable".into()),
        },
        _ => return Err("the rewritten template binds no variable".into()),
    };
    let terms = match item.block.stmts.last() {
        Some(syn::Stmt::Expr(Expr::Tuple(tuple), None)) => {
            tuple.elems.iter().cloned().collect::<Vec<_>>()
        }
        _ => return Err("the rewritten template reads no field".into()),
    };
    Ok((binder, terms))
}

/// A value of a decided term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Val {
    Int(i128),
    Bool(bool),
}

/// A term of the template's binder, read once and evaluated at each point (module
/// documentation, "Field values").
#[derive(Debug)]
enum Term {
    Int(i128),
    Bool(bool),
    /// The template's binder.
    Binder,
    /// A term no point decides.
    Unknown,
    /// A builtin operation of `Int` or `Bool` on its operands.
    Apply(Op, Vec<Term>),
}

/// A builtin operation [`Term::value`] decides.
#[derive(Clone, Copy, Debug)]
enum Op {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    /// `/Int`, division truncated towards zero.
    Quot,
    /// `%Int`, the remainder of [`Op::Quot`].
    Rem,
    /// `divInt`, Euclidean division.
    Div,
    /// `modInt`, its remainder, never negative.
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    /// `bitRangeInt(value, offset, length)`.
    BitRange,
    Neg,
    And,
    Or,
    Not,
    Xor,
    Implies,
}

impl Op {
    /// The operation the emitted K writes with `head` on `arity` operands, where it is one of K's
    /// builtin `Int` and `Bool` operations. A term with this head and arity is that operation: the
    /// K is read by its productions, and a production of the definition with the same syntax and
    /// operand sorts would make the term ambiguous (and one with the same symbol is refused).
    fn of_k(head: &str, arity: usize) -> Option<Self> {
        Some(match (head, arity) {
            ("==Int" | "==K" | "==Bool", 2) => Self::Eq,
            ("=/=Int" | "=/=K" | "=/=Bool", 2) => Self::Ne,
            ("<Int", 2) => Self::Lt,
            ("<=Int", 2) => Self::Le,
            (">Int", 2) => Self::Gt,
            (">=Int", 2) => Self::Ge,
            ("+Int", 2) => Self::Add,
            ("-Int", 2) => Self::Sub,
            ("*Int", 2) => Self::Mul,
            ("/Int", 2) => Self::Quot,
            ("%Int", 2) => Self::Rem,
            ("divInt", 2) => Self::Div,
            ("modInt", 2) => Self::Mod,
            ("&Int", 2) => Self::BitAnd,
            ("|Int", 2) => Self::BitOr,
            ("xorInt", 2) => Self::BitXor,
            ("<<Int", 2) => Self::Shl,
            (">>Int", 2) => Self::Shr,
            ("bitRangeInt", 3) => Self::BitRange,
            ("andBool" | "andThenBool", 2) => Self::And,
            ("orBool" | "orElseBool", 2) => Self::Or,
            ("notBool", 1) => Self::Not,
            ("xorBool", 2) => Self::Xor,
            ("impliesBool", 2) => Self::Implies,
            _ => return None,
        })
    }

    /// The operation a method of the rewrite's terms names on `arity` operands, its receiver
    /// first: the rewrite writes the builtin methods of `Int` (`x.bit_range::<Int>(3, 3)`).
    fn of_method(name: &str, arity: usize) -> Option<Self> {
        Some(match (name, arity) {
            ("eq", 2) => Self::Eq,
            ("ne", 2) => Self::Ne,
            ("lt", 2) => Self::Lt,
            ("le", 2) => Self::Le,
            ("gt", 2) => Self::Gt,
            ("ge", 2) => Self::Ge,
            ("add", 2) => Self::Add,
            ("sub", 2) => Self::Sub,
            ("mul", 2) => Self::Mul,
            ("bit_range", 3) => Self::BitRange,
            _ => return None,
        })
    }

    /// The operation of the Rust operator `op` on integers and Booleans.
    const fn of_binary(op: BinOp) -> Option<Self> {
        Some(match op {
            BinOp::Eq(_) => Self::Eq,
            BinOp::Ne(_) => Self::Ne,
            BinOp::Lt(_) => Self::Lt,
            BinOp::Le(_) => Self::Le,
            BinOp::Gt(_) => Self::Gt,
            BinOp::Ge(_) => Self::Ge,
            BinOp::Add(_) => Self::Add,
            BinOp::Sub(_) => Self::Sub,
            BinOp::Mul(_) => Self::Mul,
            BinOp::And(_) => Self::And,
            BinOp::Or(_) => Self::Or,
            _ => return None,
        })
    }
}

impl Term {
    /// The emitted K term `term`, a conjunct of a condition, of the template whose binder the
    /// K writes `binder`: its literals, the binder, and K's builtin operations on them
    /// ([`Op::of_k`]); any other term, a function the definition declares included, is unknown.
    fn of_k(term: &KTerm, binder: &str) -> Self {
        if term.operands.is_empty() {
            let name = term
                .head
                .split_once(':')
                .map_or(term.head.as_str(), |(name, _)| name);
            return match name {
                "true" => Self::Bool(true),
                "false" => Self::Bool(false),
                _ if name == binder => Self::Binder,
                _ => name.parse::<i128>().map_or(Self::Unknown, Self::Int),
            };
        }
        match Op::of_k(&term.head, term.operands.len()) {
            Some(op) => Self::Apply(
                op,
                term.operands
                    .iter()
                    .map(|operand| Self::of_k(operand, binder))
                    .collect(),
            ),
            None => Self::Unknown,
        }
    }

    /// The term `term` of the template's rewrite ([`rewritten`]), whose binder is named
    /// `binder`: literals, the binder, Rust operators and the builtin methods the rewrite writes
    /// ([`Op::of_method`]); any other term is unknown.
    fn of_rewrite(term: &Expr, binder: &str) -> Self {
        let apply = |op: Option<Op>, operands: Vec<&Expr>| match op {
            Some(op) => Self::Apply(
                op,
                operands
                    .into_iter()
                    .map(|operand| Self::of_rewrite(operand, binder))
                    .collect(),
            ),
            None => Self::Unknown,
        };
        match term {
            Expr::Lit(literal) => match &literal.lit {
                Lit::Int(integer) => integer
                    .base10_parse::<i128>()
                    .map_or(Self::Unknown, Self::Int),
                Lit::Bool(boolean) => Self::Bool(boolean.value),
                _ => Self::Unknown,
            },
            Expr::Path(path) if path.path.is_ident(binder) => Self::Binder,
            Expr::Paren(inner) => Self::of_rewrite(&inner.expr, binder),
            Expr::Group(inner) => Self::of_rewrite(&inner.expr, binder),
            Expr::Unary(unary) => apply(
                match unary.op {
                    UnOp::Not(_) => Some(Op::Not),
                    UnOp::Neg(_) => Some(Op::Neg),
                    _ => None,
                },
                vec![&unary.expr],
            ),
            Expr::Binary(binary) => {
                apply(Op::of_binary(binary.op), vec![&binary.left, &binary.right])
            }
            Expr::MethodCall(call) => apply(
                Op::of_method(&call.method.to_string(), call.args.len() + 1),
                std::iter::once(&*call.receiver).chain(&call.args).collect(),
            ),
            _ => Self::Unknown,
        }
    }

    /// The term's value where the binder is `binder`, `None` where it is not decided. A
    /// conjunction one of whose operands is `false` is `false`, and a disjunction one of whose
    /// operands is `true` is `true`, whatever the other (module documentation, "Field values").
    fn value(&self, binder: i128) -> Option<Val> {
        match self {
            Self::Int(value) => Some(Val::Int(*value)),
            Self::Bool(value) => Some(Val::Bool(*value)),
            Self::Binder => Some(Val::Int(binder)),
            Self::Unknown => None,
            Self::Apply(op, operands) => apply(*op, operands, binder),
        }
    }
}

/// The value of `op` on `operands` where the binder is `binder` ([`Term::value`]).
fn apply(op: Op, operands: &[Term], binder: i128) -> Option<Val> {
    use Val::{Bool, Int};
    let value = |index: usize| operands.get(index).and_then(|term| term.value(binder));
    match op {
        Op::And => {
            return match (value(0), value(1)) {
                (Some(Bool(false)), _) | (_, Some(Bool(false))) => Some(Bool(false)),
                (Some(Bool(true)), Some(Bool(true))) => Some(Bool(true)),
                _ => None,
            };
        }
        Op::Or => {
            return match (value(0), value(1)) {
                (Some(Bool(true)), _) | (_, Some(Bool(true))) => Some(Bool(true)),
                (Some(Bool(false)), Some(Bool(false))) => Some(Bool(false)),
                _ => None,
            };
        }
        Op::Implies => {
            return match (value(0), value(1)) {
                (Some(Bool(false)), _) | (_, Some(Bool(true))) => Some(Bool(true)),
                (Some(Bool(true)), Some(Bool(false))) => Some(Bool(false)),
                _ => None,
            };
        }
        _ => {}
    }
    // Every other operation needs each operand's value.
    let shift = |amount: i128| u32::try_from(amount).ok().filter(|amount| *amount < 127);
    let right = if operands.len() > 1 {
        Some(value(1)?)
    } else {
        None
    };
    Some(match (op, value(0)?, right) {
        (Op::Not, Bool(operand), None) => Bool(!operand),
        (Op::Neg, Int(operand), None) => Int(operand.checked_neg()?),
        (Op::Eq, left, Some(right)) => Bool(left == right),
        (Op::Ne, left, Some(right)) => Bool(left != right),
        (Op::Xor, Bool(left), Some(Bool(right))) => Bool(left != right),
        (Op::BitRange, Int(operand), Some(Int(offset))) => {
            let Some(Int(length)) = value(2) else {
                return None;
            };
            let (offset, length) = (shift(offset)?, shift(length)?);
            Int((operand >> offset) & ((1_i128 << length) - 1))
        }
        (op, Int(left), Some(Int(right))) => match op {
            Op::Lt => Bool(left < right),
            Op::Le => Bool(left <= right),
            Op::Gt => Bool(left > right),
            Op::Ge => Bool(left >= right),
            Op::Add => Int(left.checked_add(right)?),
            Op::Sub => Int(left.checked_sub(right)?),
            Op::Mul => Int(left.checked_mul(right)?),
            Op::Quot => Int(left.checked_div(right)?),
            Op::Rem => Int(left.checked_rem(right)?),
            Op::Div => Int(left.checked_div_euclid(right)?),
            Op::Mod => Int(left.checked_rem_euclid(right)?),
            Op::BitAnd => Int(left & right),
            Op::BitOr => Int(left | right),
            Op::BitXor => Int(left ^ right),
            Op::Shl => {
                let amount = shift(right)?;
                let shifted = left.checked_shl(amount)?;
                (shifted >> amount == left).then_some(Int(shifted))?
            }
            Op::Shr => Int(match shift(right) {
                Some(amount) => left >> amount,
                None if right >= 0 => left >> 127,
                None => return None,
            }),
            _ => return None,
        },
        _ => return None,
    })
}

/// The runs of consecutive points of `points` (ascending), each in hexadecimal with the digits
/// a `width`-bit value takes: `0x1c-0x1e`, or `0x1f` alone.
fn runs(points: &[u128], width: u32) -> Vec<String> {
    let digits = usize::try_from(width.div_ceil(4).max(1)).unwrap_or(1);
    let hex = |point: u128| format!("0x{point:0digits$x}");
    let mut runs = Vec::new();
    let mut iter = points.iter().copied().peekable();
    while let Some(first) = iter.next() {
        let mut last = first;
        while iter.peek() == Some(&(last + 1)) {
            last += 1;
            iter.next();
        }
        runs.push(if first == last {
            hex(first)
        } else {
            format!("{}-{}", hex(first), hex(last))
        });
    }
    runs
}

/// A target's list of encodings: the first [`LISTED_RUNS`] runs, then how many more.
fn listed_encodings(runs: &[String]) -> String {
    let mut text = format!(
        "encodings {}",
        runs[..runs.len().min(LISTED_RUNS)].join(", ")
    );
    if runs.len() > LISTED_RUNS {
        text.push_str(" and ");
        text.push_str(&(runs.len() - LISTED_RUNS).to_string());
        text.push_str(" more runs");
    }
    text
}

/// The value `value` of the field `field` as a target writes it, at `point`, an encoding where
/// the field has that value: decimal, then the field's template bits at `point`, most
/// significant first, labelled as such where they read as another number than the value (a field
/// whose modifier places its bits or reads them signed).
fn value_text(value: i128, field: &Field, point: u128) -> String {
    let bits = field
        .positions
        .iter()
        .map(|position| {
            if (point >> position) & 1 == 1 {
                '1'
            } else {
                '0'
            }
        })
        .collect::<String>();
    let placed = field.positions.iter().fold(0_i128, |sum, position| {
        (sum << 1) | i128::from((point >> position) & 1 == 1)
    });
    if placed == value {
        format!("{value} (0b{bits})")
    } else {
        format!("{value} (template bits 0b{bits})")
    }
}

#[cfg(test)]
mod tests {
    use super::{Field, KTerm, Term, Val, runs, value_text};

    fn k(head: &str, operands: Vec<KTerm>) -> KTerm {
        KTerm {
            head: head.to_owned(),
            operands,
        }
    }

    fn leaf(head: &str) -> KTerm {
        k(head, Vec::new())
    }

    #[test]
    fn emitted_builtins_are_decided_and_declared_functions_are_not() {
        // `Op:Int =/=Int 31`
        let hole = k("=/=Int", vec![leaf("Op:Int"), leaf("31")]);
        assert_eq!(Term::of_k(&hole, "Op").value(31), Some(Val::Bool(false)));
        assert_eq!(Term::of_k(&hole, "Op").value(30), Some(Val::Bool(true)));
        // `bitRangeInt(Op:Int, 0, 2) +Int 1 ==Int 0`, the builtin, and the same with a function
        // the definition declares, which is no builtin whatever its Rust name.
        let range = k("bitRangeInt", vec![leaf("Op:Int"), leaf("0"), leaf("2")]);
        let builtin = k("==Int", vec![k("+Int", vec![range, leaf("1")]), leaf("0")]);
        assert_eq!(Term::of_k(&builtin, "Op").value(11), Some(Val::Bool(false)));
        let range = k("bitRangeInt", vec![leaf("Op:Int"), leaf("0"), leaf("2")]);
        let declared = k("==Int", vec![k("add", vec![range, leaf("1")]), leaf("0")]);
        assert_eq!(Term::of_k(&declared, "Op").value(11), None);
        // A conjunct an operand of which is unknown is decided by the other where it can be.
        let other = k(
            "andThenBool",
            vec![k("<Int", vec![leaf("Op:Int"), leaf("0")]), leaf("Ime:Bool")],
        );
        assert_eq!(Term::of_k(&other, "Op").value(3), Some(Val::Bool(false)));
        let undecided = k(
            "andThenBool",
            vec![k(">Int", vec![leaf("Op:Int"), leaf("0")]), leaf("Ime:Bool")],
        );
        assert_eq!(Term::of_k(&undecided, "Op").value(3), None);
        // K's division truncates, its `modInt` is never negative, and division by zero is
        // undefined, so undecided.
        let quotient = k("/Int", vec![leaf("-7"), leaf("Op:Int")]);
        assert_eq!(Term::of_k(&quotient, "Op").value(2), Some(Val::Int(-3)));
        assert_eq!(Term::of_k(&quotient, "Op").value(0), None);
        let modulo = k("modInt", vec![leaf("-7"), leaf("Op:Int")]);
        assert_eq!(Term::of_k(&modulo, "Op").value(2), Some(Val::Int(1)));
    }

    #[test]
    fn the_rewrites_methods_are_decided() {
        let term = syn::parse_str("op.bit_range::<Int>(2, 2).mul::<Int>(4)").unwrap();
        assert_eq!(
            Term::of_rewrite(&term, "op").value(0x1f),
            Some(Val::Int(12))
        );
        let call = syn::parse_str("add(op, 1)").unwrap();
        assert_eq!(Term::of_rewrite(&call, "op").value(0x1f), None);
    }

    #[test]
    fn encodings_are_listed_in_runs() {
        assert_eq!(runs(&[28, 29, 30, 40], 6), ["0x1c-0x1e", "0x28"]);
        let plain = Field {
            letter: 'r',
            positions: vec![3, 2],
        };
        assert_eq!(value_text(3, &plain, 0x1c), "3 (0b11)");
        // `k::bits!("uuu 1", u: [6:4])`: the value is the template bits times 16.
        let placed = Field {
            letter: 'u',
            positions: vec![3, 2, 1],
        };
        assert_eq!(value_text(16, &placed, 0b0011), "16 (template bits 0b001)");
        // A signed field's value -2 is template bits 1110.
        let signed = Field {
            letter: 'i',
            positions: vec![7, 6, 5, 4],
        };
        assert_eq!(value_text(-2, &signed, 0xe3), "-2 (template bits 0b1110)");
    }
}
