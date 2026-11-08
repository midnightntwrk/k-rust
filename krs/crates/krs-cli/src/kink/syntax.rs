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
//! K's categories, so no author wrote them. Every package of the definition counts, as its
//! rules are obligations of the rules family: the corpus judges the definition the emission
//! wrote, of which a dependency's syntax is part, and the rules over that syntax are among the
//! rules the family counts. kink-flow keeps of each authored sort the productions that build a
//! term with a constructor.
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
//! its binder, and each field `f` reads a function of the binder. The template's arm domain is
//! the set of points `v` with `0 <= v < 2^w` that every conjunct of `S`'s condition decided by
//! `v` alone holds at. The front end reads `T`'s layout through the language's own rewrite of
//! the template, [`krs_syntax::desugar_bit_templates`], applied to a function whose one
//! parameter is the pattern as the author wrote it: its condition is the template's range test
//! and fixed-bit equalities, and its result reads each field as the sentence reads it. The
//! conjuncts of `S`'s condition after the templates' tests, as the author wrote them, are
//! evaluated at each point where they are Boolean combinations of integer comparisons,
//! arithmetic and bit ranges over the binder, the template's fields and literals (a literal
//! hole such as `op != 0x76`); any other conjunct is taken to hold, so the domain contains every
//! value a fired instance can bind and is exact where every conjunct is decided. The universe of
//! `T` is each `(T, f, f(v))` for `v` in the domain: a field value no point gives cannot be
//! reached by any input, and one some point gives can. A template wider than 16 bits is not
//! enumerated (at most 2^16 points per template); its field values are no obligation, and the
//! document lists it under `families.syntax.krs.unenumerated` with the reason, as it does a
//! template whose layout or whose sentence's condition cannot be read.
//!
//! Every baseline run records the binder's values at the fired instances of `S`
//! ([`KrsSyntax::selection`]: the axiom by its label as the loaded definition stores it, the
//! variable as the compiled definition writes it, the cap the domain's size, so no value a fired
//! instance binds is left out). A field value is reached when some comparable program's run
//! bound the binder to a value `b` with `f(b)` the value. Each item of kind `field-value` is
//! `{kind, template, field, value, status, reached_by, uncounted: {operand_of}, krs}`, with
//! `krs = {item, rule, label, file, line, column, encodings, matched_by, target}`: `item` names
//! it (`crate::decode_ld:r=3`), `encodings` are the points of the domain where the field has the
//! value, in hexadecimal and in runs, the inputs an author writes to reach it, and `matched_by`
//! the programs whose runs matched the sentence's templates (its row's `krs.matched_by`), the
//! cases closest to one that reaches the value. Only templates of sentences of the rules
//! universe (`fired`, `matched` or `unmatched`) give items, as only those sentences' instances
//! count.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir_levels::{DefinitionSentence, SymbolIdentity};
use serde_json::{Value, json};
use syn::{BinOp, Expr, Lit, UnOp};

use super::annotate::qualified;
use super::guards::{GuardNames, TemplateSite};
use crate::{DiagnosticSources, EmittedDefinition};

/// The K namespace of KRS's framework package, whose sorts are K's categories.
const FRAMEWORK_NAMESPACE: &str = "KRS-FRAMEWORK";

/// The widest template enumerated, in bits.
const MAXIMUM_ENUMERATED_WIDTH: u32 = 16;

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
    /// The fields, most significant first: each letter and its number of template bits.
    fields: Vec<(char, u32)>,
    /// Each point of the arm domain, ascending, with its fields' values in field order.
    points: BTreeMap<u128, Vec<i128>>,
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
        let text = sources.clone();
        let mut origins =
            krs_exec::Origins::new(Some(Box::new(move |file| text.source_text(file))));
        for module in definition.modules() {
            for sentence in module.sentences() {
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
            templates,
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
                    let layout = template.layout.as_ref().ok()?;
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
                let Some(fields) = layout.points.get(&point) else {
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
        for (index, (letter, bits)) in layout.fields.iter().enumerate() {
            let mut encodings = BTreeMap::<i128, Vec<u128>>::new();
            for (point, fields) in &layout.points {
                encodings.entry(fields[index]).or_default().push(*point);
            }
            for (value, points) in encodings {
                let reached_by = ordered(by_value[index][0].get(&value));
                let uncounted = ordered(by_value[index][1].get(&value));
                let runs = runs(&points, layout.width);
                let shown = value_text(value, *bits);
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
fn layout(
    site: &TemplateSite,
    conjuncts: &Result<Vec<Option<String>>, String>,
) -> Result<Layout, String> {
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
    let mut fields = Vec::<(char, u32)>::new();
    let mut width = 0_u32;
    for character in literal.chars() {
        match character {
            '0' | '1' | '_' => width += 1,
            letter if letter.is_ascii_lowercase() => {
                width += 1;
                match fields.iter_mut().find(|(name, _)| *name == letter) {
                    Some((_, bits)) => *bits += 1,
                    None => fields.push((letter, 1)),
                }
            }
            _ => {}
        }
    }
    if width > MAXIMUM_ENUMERATED_WIDTH {
        return Err(format!(
            "the template is {width} bits wide, wider than the {MAXIMUM_ENUMERATED_WIDTH} bits whose points are enumerated"
        ));
    }
    let (binder, guard, terms) = rewritten(pattern, &fields)?;
    let authored = conjuncts
        .iter()
        .flatten()
        .filter_map(|text| syn::parse_str::<Expr>(text).ok())
        .collect::<Vec<_>>();
    let mut points = BTreeMap::new();
    for point in 0..(1_u128 << width) {
        let mut environment = BTreeMap::new();
        environment.insert(binder.clone(), Val::Int(point.cast_signed()));
        if evaluate(&guard, &environment) == Some(Val::Bool(false)) {
            continue;
        }
        let mut values = Vec::with_capacity(terms.len());
        for term in &terms {
            match evaluate(term, &environment) {
                Some(Val::Int(value)) => values.push(value),
                _ => return Err("a field of the rewritten template is no integer term".into()),
            }
        }
        for ((letter, _), value) in fields.iter().zip(&values) {
            environment.insert(letter.to_string(), Val::Int(*value));
        }
        if authored
            .iter()
            .any(|conjunct| evaluate(conjunct, &environment) == Some(Val::Bool(false)))
        {
            continue;
        }
        points.insert(point, values);
    }
    Ok(Layout {
        width,
        fields,
        points,
    })
}

/// The template whose pattern the author wrote `pattern`, with the fields `fields`, rewritten by
/// the language's own rewrite ([`krs_syntax::desugar_bit_templates`]) on a function whose one
/// parameter it is: the binder's name, the template's test, and each field's term.
fn rewritten(pattern: &str, fields: &[(char, u32)]) -> Result<(String, Expr, Vec<Expr>), String> {
    let letters = fields
        .iter()
        .map(|(letter, _)| letter.to_string())
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
    let guard = item
        .attrs
        .iter()
        .find_map(|attribute| match &attribute.meta {
            syn::Meta::List(list)
                if list
                    .path
                    .segments
                    .last()
                    .is_some_and(|s| s.ident == "requires") =>
            {
                syn::parse2::<Expr>(list.tokens.clone()).ok()
            }
            _ => None,
        })
        .ok_or("the rewritten template has no test")?;
    let terms = match item.block.stmts.last() {
        Some(syn::Stmt::Expr(Expr::Tuple(tuple), None)) => {
            tuple.elems.iter().cloned().collect::<Vec<_>>()
        }
        _ => return Err("the rewritten template reads no field".into()),
    };
    Ok((binder, guard, terms))
}

/// A value of a decided term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Val {
    Int(i128),
    Bool(bool),
}

/// The value of `term` (Rust syntax) where it is decided by `environment`: literals, the bound
/// names, and integer comparisons, arithmetic and bit ranges, and Boolean connectives over them,
/// written as operators, as methods (`x.bit_range::<Int>(3, 3)`, `x.ne::<Int>(6)`) or as calls
/// (`int::ne(x, 6)`); `None` for any other term. A conjunction one of whose operands is `false`
/// is `false`, and a disjunction one of whose operands is `true` is `true`, whatever the other.
fn evaluate(term: &Expr, environment: &BTreeMap<String, Val>) -> Option<Val> {
    match term {
        Expr::Lit(literal) => match &literal.lit {
            Lit::Int(integer) => integer.base10_parse::<i128>().ok().map(Val::Int),
            Lit::Bool(boolean) => Some(Val::Bool(boolean.value)),
            _ => None,
        },
        Expr::Path(path) => environment
            .get(&path.path.get_ident()?.to_string())
            .copied(),
        Expr::Paren(inner) => evaluate(&inner.expr, environment),
        Expr::Group(inner) => evaluate(&inner.expr, environment),
        Expr::Unary(unary) => match (unary.op, evaluate(&unary.expr, environment)?) {
            (UnOp::Not(_), Val::Bool(value)) => Some(Val::Bool(!value)),
            (UnOp::Neg(_), Val::Int(value)) => value.checked_neg().map(Val::Int),
            _ => None,
        },
        Expr::Binary(binary) => {
            let left = evaluate(&binary.left, environment);
            let right = evaluate(&binary.right, environment);
            match binary.op {
                BinOp::And(_) => match (left, right) {
                    (Some(Val::Bool(false)), _) | (_, Some(Val::Bool(false))) => {
                        Some(Val::Bool(false))
                    }
                    (Some(Val::Bool(true)), Some(Val::Bool(true))) => Some(Val::Bool(true)),
                    _ => None,
                },
                BinOp::Or(_) => match (left, right) {
                    (Some(Val::Bool(true)), _) | (_, Some(Val::Bool(true))) => {
                        Some(Val::Bool(true))
                    }
                    (Some(Val::Bool(false)), Some(Val::Bool(false))) => Some(Val::Bool(false)),
                    _ => None,
                },
                op => operation(binary_name(op)?, &[left?, right?]),
            }
        }
        Expr::MethodCall(call) => {
            let mut operands = vec![evaluate(&call.receiver, environment)?];
            for argument in &call.args {
                operands.push(evaluate(argument, environment)?);
            }
            operation(&call.method.to_string(), &operands)
        }
        Expr::Call(call) => {
            let Expr::Path(function) = &*call.func else {
                return None;
            };
            let name = function.path.segments.last()?.ident.to_string();
            let operands = call
                .args
                .iter()
                .map(|argument| evaluate(argument, environment))
                .collect::<Option<Vec<_>>>()?;
            operation(&name, &operands)
        }
        _ => None,
    }
}

/// The method name of a binary operator [`operation`] decides.
const fn binary_name(op: BinOp) -> Option<&'static str> {
    Some(match op {
        BinOp::Eq(_) => "eq",
        BinOp::Ne(_) => "ne",
        BinOp::Lt(_) => "lt",
        BinOp::Le(_) => "le",
        BinOp::Gt(_) => "gt",
        BinOp::Ge(_) => "ge",
        BinOp::Add(_) => "add",
        BinOp::Sub(_) => "sub",
        BinOp::Mul(_) => "mul",
        _ => return None,
    })
}

/// The operation `name` on `operands`, where it is one [`evaluate`] decides.
fn operation(name: &str, operands: &[Val]) -> Option<Val> {
    use Val::{Bool, Int};
    Some(match (name, operands) {
        ("eq", [left, right]) => Bool(left == right),
        ("ne", [left, right]) => Bool(left != right),
        ("lt", [Int(left), Int(right)]) => Bool(left < right),
        ("le", [Int(left), Int(right)]) => Bool(left <= right),
        ("gt", [Int(left), Int(right)]) => Bool(left > right),
        ("ge", [Int(left), Int(right)]) => Bool(left >= right),
        ("add", [Int(left), Int(right)]) => Int(left.checked_add(*right)?),
        ("sub", [Int(left), Int(right)]) => Int(left.checked_sub(*right)?),
        ("mul", [Int(left), Int(right)]) => Int(left.checked_mul(*right)?),
        ("bit_range", [Int(value), Int(offset), Int(length)]) => {
            let offset = u32::try_from(*offset).ok().filter(|offset| *offset < 127)?;
            let length = u32::try_from(*length).ok().filter(|length| *length < 127)?;
            Int((value >> offset) & ((1_i128 << length) - 1))
        }
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

/// A field's value as a target writes it: decimal, and binary in the field's `bits` template
/// bits where it fits them.
fn value_text(value: i128, bits: u32) -> String {
    match u32::try_from(value) {
        Ok(unsigned) if bits < 32 && unsigned < (1_u32 << bits) => {
            let digits = usize::try_from(bits).unwrap_or(1);
            format!("{value} (0b{unsigned:0digits$b})")
        }
        _ => value.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::{Val, evaluate, runs, value_text};
    use std::collections::BTreeMap;

    fn decide(text: &str, bindings: &[(&str, Val)]) -> Option<Val> {
        let environment = bindings
            .iter()
            .map(|(name, value)| ((*name).to_owned(), *value))
            .collect::<BTreeMap<_, _>>();
        evaluate(&syn::parse_str(text).unwrap(), &environment)
    }

    #[test]
    fn decided_terms_are_evaluated_and_others_are_not() {
        let op = ("op", Val::Int(0x1f));
        assert_eq!(decide("op != 0x1f", &[op]), Some(Val::Bool(false)));
        assert_eq!(decide("int::ne(op, 31)", &[op]), Some(Val::Bool(false)));
        assert_eq!(
            decide("op.bit_range::<Int>(2, 2).eq::<Int>(3)", &[op]),
            Some(Val::Bool(true))
        );
        // A conjunct an operand of which is unknown is decided by the other where it can be.
        assert_eq!(decide("op < 0 && ime", &[op]), Some(Val::Bool(false)));
        assert_eq!(decide("op > 0 && ime", &[op]), None);
        assert_eq!(decide("op / 2 == 15", &[op]), None);
    }

    #[test]
    fn encodings_are_listed_in_runs() {
        assert_eq!(runs(&[28, 29, 30, 40], 6), ["0x1c-0x1e", "0x28"]);
        assert_eq!(value_text(3, 2), "3 (0b11)");
        assert_eq!(value_text(-2, 4), "-2");
    }
}
