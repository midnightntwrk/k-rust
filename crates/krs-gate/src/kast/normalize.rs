//! Transform typed KAST before applying canonical JSON layout rules.

use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    definition::{Attributes, FlatModule, ProductionItem, Sentence},
    kast::{Label, Sort, Term},
};
use serde_json::{Value, json};

use super::{
    canonical_json,
    policy::{self, AttributePolicy, NamePolicy},
    reader::{self, Document},
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Variables {
    Preserve,
    Ordinary,
    Behavior,
    Static,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Names {
    Identity,
    Policy,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum AttributeHandling {
    Unchecked,
    Known,
    Source,
    Claim,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Sentences {
    All,
    Source,
    Claims,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Terms {
    All,
    Rewrite,
    Plain,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum TagOrder {
    Preserve,
    Canonical,
    String,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum ModuleOrder {
    Preserve,
    Children,
    NamesAndChildren,
}

#[derive(Clone, Copy)]
pub(crate) struct Options {
    variables: Variables,
    names: Names,
    attributes: AttributeHandling,
    sentences: Sentences,
    terms: Terms,
    tags: TagOrder,
    modules: ModuleOrder,
}

impl Options {
    pub(crate) fn source() -> Self {
        Self {
            variables: Variables::Ordinary,
            names: Names::Policy,
            attributes: AttributeHandling::Source,
            sentences: Sentences::Source,
            terms: Terms::Rewrite,
            tags: TagOrder::Canonical,
            modules: ModuleOrder::Preserve,
        }
    }
    fn for_variant(variant: &str) -> Result<Self, String> {
        let mut options = Self::source();
        options.tags = TagOrder::Preserve;
        match variant {
            "behavior" => {
                options.variables = Variables::Behavior;
                options.attributes = AttributeHandling::Known;
            }
            "proof_result" => {
                options.attributes = AttributeHandling::Known;
            }
            "proof_claim" => {
                options.attributes = AttributeHandling::Claim;
                options.sentences = Sentences::Claims;
                options.modules = ModuleOrder::Children;
            }
            "static_proof" => {
                options.variables = Variables::Static;
                options.names = Names::Identity;
                options.attributes = AttributeHandling::Unchecked;
                options.terms = Terms::Plain;
            }
            "static_claim" => {
                options.variables = Variables::Static;
                options.names = Names::Identity;
                options.attributes = AttributeHandling::Unchecked;
                options.sentences = Sentences::Claims;
                options.modules = ModuleOrder::Children;
            }
            "normalized_definition" => {
                options.variables = Variables::Preserve;
                options.names = Names::Identity;
                options.attributes = AttributeHandling::Unchecked;
                options.sentences = Sentences::All;
                options.terms = Terms::All;
                options.tags = TagOrder::String;
                options.modules = ModuleOrder::NamesAndChildren;
            }
            _ => return Err(format!("unknown KAST normalization variant {variant:?}")),
        }
        Ok(options)
    }
}

pub(crate) struct Normalizer<'a> {
    options: Options,
    names: &'a NamePolicy,
    attribute_policy: &'a AttributePolicy,
    variables: BTreeMap<(String, char, String), String>,
}

impl<'a> Normalizer<'a> {
    pub(crate) fn new(
        options: Options,
        names: &'a NamePolicy,
        attributes: &'a AttributePolicy,
    ) -> Self {
        Self {
            options,
            names,
            attribute_policy: attributes,
            variables: BTreeMap::new(),
        }
    }
    fn mapped(&self, name: &str, kind: &str) -> Result<String, String> {
        if self.options.names == Names::Policy {
            self.names.mapped(name, kind)
        } else {
            Ok(name.into())
        }
    }
    fn sort(&self, sort: &mut Sort) -> Result<(), String> {
        sort.name = self.mapped(&sort.name, "sort")?;
        for parameter in &mut sort.parameters {
            self.sort(parameter)?;
        }
        Ok(())
    }
    fn label(&self, label: &mut Label) -> Result<(), String> {
        label.name = self.mapped(&label.name, "label")?;
        for parameter in &mut label.parameters {
            self.sort(parameter)?;
        }
        Ok(())
    }
    fn variable(&mut self, name: &mut String, sort: &mut Option<Sort>) -> Result<(), String> {
        if self.options.variables == Variables::Static && sort.is_none() {
            return Err("proof variable has no concrete sort name".into());
        }
        if self.options.variables != Variables::Preserve {
            let sort_name = sort.as_ref().map_or_else(
                || Ok("<unsorted>".into()),
                |sort| self.mapped(&sort.name, "sort"),
            )?;
            let kind = match self.options.variables {
                Variables::Static => 'V',
                _ if name.starts_with('?') => 'E',
                _ if name.starts_with('_') => 'A',
                Variables::Behavior => 'V',
                _ => 'O',
            };
            let key = (name.clone(), kind, sort_name);
            let next = self.variables.len();
            name.clone_from(
                self.variables
                    .entry(key)
                    .or_insert_with(|| format!("{kind}{next}")),
            );
        }
        if let Some(sort) = sort {
            self.sort(sort)?;
        }
        Ok(())
    }
    pub(crate) fn term(&mut self, term: &mut Term) -> Result<(), String> {
        match term {
            Term::Variable { name, sort } => self.variable(name, sort),
            Term::Token { sort, .. } => self.sort(sort),
            Term::Apply { label, arguments } => {
                self.label(label)?;
                for term in arguments {
                    self.term(term)?;
                }
                Ok(())
            }
            Term::Sequence(items) => {
                for term in items {
                    self.term(term)?;
                }
                Ok(())
            }
            Term::Rewrite { left, right } if self.options.terms != Terms::Plain => {
                self.term(left)?;
                self.term(right)
            }
            Term::As { pattern, alias } if self.options.terms == Terms::All => {
                self.term(pattern)?;
                self.term(alias)
            }
            Term::InjectedLabel(label) if self.options.terms == Terms::All => self.label(label),
            Term::Annotated { term, .. } => self.term(term),
            _ => Err("unclassified proof KAST node".into()),
        }
    }
    pub(crate) fn attributes(&mut self, attributes: &mut Attributes) -> Result<(), String> {
        let mut entries = BTreeMap::new();
        for (name, value) in attributes.wire_entries() {
            if self.options.attributes != AttributeHandling::Unchecked
                && !self.attribute_policy.known_attributes.contains(name)
            {
                return Err(format!("unknown attributes: {name}"));
            }
            if self.attribute_policy.metadata_attributes.contains(name) {
                continue;
            }
            let mut child = value.clone();
            let mapped = (self.options.attributes == AttributeHandling::Source)
                .then(|| {
                    self.attribute_policy
                        .attribute_value_map
                        .get(name)
                        .and_then(|map| child.as_str().and_then(|value| map.get(value)))
                })
                .flatten();
            if let Some(mapped) = mapped {
                child = Value::String(mapped.clone());
            } else if child.is_string()
                && ((self.options.attributes == AttributeHandling::Source
                    && ["label", "bracketLabel", "element", "unit", "initializer"].contains(&name))
                    || (self.options.attributes == AttributeHandling::Claim && name == "label"))
            {
                child =
                    Value::String(self.mapped(child.as_str().expect("string checked"), "label")?);
            } else if self.options.attributes == AttributeHandling::Source
                && name == "syntaxModule"
                && child.is_string()
            {
                child =
                    Value::String(self.mapped(child.as_str().expect("string checked"), "name")?);
            } else {
                self.payload(&mut child)?;
            }
            entries.insert(name.to_owned(), child);
        }
        *attributes = Attributes::new(entries);
        Ok(())
    }
    fn payload(&mut self, value: &mut Value) -> Result<(), String> {
        match value {
            Value::Array(items) => {
                for child in items {
                    self.payload(child)?;
                }
            }
            Value::Object(object) => {
                if object.get("node").is_some_and(|node| !node.is_string())
                    && self.options.attributes != AttributeHandling::Unchecked
                {
                    return Err("unclassified KAST attribute payload node".into());
                }
                match object.get("node").and_then(Value::as_str) {
                    Some("KSort") => {
                        let Term::Token { mut sort, .. } =
                            reader::term(&json!({"node":"KToken","token":"","sort":value}))?
                        else {
                            unreachable!()
                        };
                        self.sort(&mut sort)?;
                        *value = reader::term_value(&Term::Token {
                            token: String::new(),
                            sort,
                        })?["sort"]
                            .take();
                    }
                    Some("KLabel") => {
                        let Term::Apply { mut label, .. } = reader::term(
                            &json!({"node":"KApply","label":value,"args":[],"arity":0}),
                        )?
                        else {
                            unreachable!()
                        };
                        self.label(&mut label)?;
                        *value = reader::term_value(&Term::Apply {
                            label,
                            arguments: vec![],
                        })?["label"]
                            .take();
                    }
                    Some(
                        "KApply" | "KToken" | "KVariable" | "KSequence" | "KRewrite" | "KAs"
                        | "InjectedKLabel",
                    ) => {
                        let mut term = reader::term(value)?;
                        self.term(&mut term)?;
                        *value = reader::term_value(&term)?;
                    }
                    Some(
                        "KRule"
                        | "KClaim"
                        | "KContext"
                        | "KProduction"
                        | "KSyntaxSort"
                        | "KSyntaxPriority"
                        | "KSyntaxAssociativity"
                        | "KSortSynonym"
                        | "KSyntaxLexical"
                        | "KConfiguration"
                        | "KBubble",
                    ) => {
                        let mut sentence = reader::payload_sentence(value)?;
                        self.sentence(&mut sentence)?;
                        *value = reader::sentence_value(&sentence)?;
                    }
                    Some("KAtt") => {
                        let mut attributes = reader::payload_attributes(value)?;
                        self.attributes(&mut attributes)?;
                        *value = json!({"node":"KAtt","att":attributes.wire_entries().map(|(name,value)| (name.to_owned(),value.clone())).collect::<serde_json::Map<_,_>>()});
                    }
                    Some("KFlatModule") => {
                        let mut module = reader::payload_module(value)?;
                        self.module(&mut module)?;
                        *value = reader::module_value(&module)?;
                    }
                    Some("KDefinition" | "KFlatModuleList") => {
                        let mut document = reader::from_value(value)?;
                        self.document(&mut document)?;
                        *value = document.to_value()?["term"].take();
                    }
                    Some("badsentence") if object.len() == 1 => {}
                    Some(_) if self.options.sentences != Sentences::All => {
                        return Err("unclassified KAST attribute payload node".into());
                    }
                    _ => {
                        for child in object.values_mut() {
                            self.payload(child)?;
                        }
                    }
                }
            }
            Value::Number(number)
                if number.is_f64() && self.options.attributes != AttributeHandling::Unchecked =>
            {
                return Err("unsupported KAST scalar".into());
            }
            _ => {}
        }
        Ok(())
    }
    fn tags(&self, tags: &mut [String]) -> Result<(), String> {
        for tag in tags {
            *tag = self.mapped(tag, "label")?;
        }
        Ok(())
    }
    pub(crate) fn sentence(&mut self, sentence: &mut Sentence) -> Result<(), String> {
        if self.options.sentences == Sentences::Claims
            && !matches!(sentence, Sentence::Claim { .. })
        {
            return Err("unclassified claim KAST sentence".into());
        }
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
            } => {
                self.term(body)?;
                self.term(requires)?;
                self.term(ensures)?;
            }
            Sentence::Context { body, requires, .. } => {
                self.term(body)?;
                self.term(requires)?;
            }
            Sentence::SyntaxSort {
                sort, parameters, ..
            } => {
                self.sort(sort)?;
                for sort in parameters {
                    self.sort(sort)?;
                }
            }
            Sentence::Production {
                sort,
                items,
                parameters,
                label,
                ..
            } => {
                self.sort(sort)?;
                for item in items {
                    match item {
                        ProductionItem::NonTerminal { sort, .. } => self.sort(sort)?,
                        ProductionItem::RegexTerminal {
                            precede_regex,
                            follow_regex,
                            ..
                        } if self.options.sentences != Sentences::All
                            && (precede_regex.is_some() || follow_regex.is_some()) =>
                        {
                            return Err("unsupported KRegexTerminal representation".into());
                        }
                        _ => {}
                    }
                }
                for sort in parameters {
                    self.sort(sort)?;
                }
                if let Some(label) = label {
                    self.label(label)?;
                }
            }
            Sentence::SyntaxAssociativity { tags, .. } => self.tags(tags)?,
            Sentence::SyntaxPriority { priorities, .. } => {
                for tags in priorities {
                    self.tags(tags)?;
                }
            }
            Sentence::SortSynonym {
                new_sort, old_sort, ..
            } if self.options.sentences == Sentences::All => {
                self.sort(new_sort)?;
                self.sort(old_sort)?;
            }
            Sentence::Configuration { body, ensures, .. }
                if self.options.sentences == Sentences::All =>
            {
                self.term(body)?;
                self.term(ensures)?;
            }
            Sentence::ContextAlias { body, requires, .. }
                if self.options.sentences == Sentences::All =>
            {
                self.term(body)?;
                self.term(requires)?;
            }
            Sentence::SyntaxLexical { .. } | Sentence::Bubble { .. }
                if self.options.sentences == Sentences::All => {}
            _ => return Err("unclassified KAST sentence".into()),
        }
        self.attributes(sentence.attributes_mut())
    }
    fn module(&mut self, module: &mut FlatModule) -> Result<(), String> {
        module.name = self.mapped(&module.name, "name")?;
        for imported in &mut module.imports {
            imported.name = self.mapped(&imported.name, "name")?;
        }
        for sentence in &mut module.local_sentences {
            self.sentence(Arc::make_mut(sentence))?;
        }
        self.attributes(&mut module.attributes)
    }
    fn document(&mut self, document: &mut Document) -> Result<(), String> {
        match document {
            Document::Term(term) => self.term(term),
            Document::Definition(document) => {
                document.definition.main_module =
                    self.mapped(&document.definition.main_module, "name")?;
                for module in &mut document.definition.modules {
                    self.module(module)?;
                }
                self.attributes(&mut document.definition.attributes)
            }
            Document::ModuleList {
                main_module,
                modules,
            } => {
                *main_module = self.mapped(main_module, "name")?;
                for module in modules {
                    self.module(module)?;
                }
                Ok(())
            }
        }
    }
}

fn layout(value: &mut Value, options: Options) {
    match value {
        Value::Array(items) => {
            for child in items {
                layout(child, options);
            }
        }
        Value::Object(object) => {
            for child in object.values_mut() {
                layout(child, options);
            }
            if options.tags != TagOrder::Preserve {
                if object.get("node").and_then(Value::as_str) == Some("KSyntaxAssociativity")
                    && let Some(Value::Array(tags)) = object.get_mut("tags")
                {
                    sort_tags(tags, options.tags);
                }
                if object.get("node").and_then(Value::as_str) == Some("KSyntaxPriority")
                    && let Some(Value::Array(groups)) = object.get_mut("priorities")
                {
                    for group in groups {
                        if let Value::Array(tags) = group {
                            sort_tags(tags, options.tags);
                        }
                    }
                }
            }
            if options.modules != ModuleOrder::Preserve {
                for field in ["imports", "localSentences"] {
                    if let Some(Value::Array(items)) = object.get_mut(field) {
                        items.sort_by_key(canonical_json);
                    }
                }
            }
        }
        _ => {}
    }
}
fn sort_tags(tags: &mut [Value], order: TagOrder) {
    if order == TagOrder::Canonical {
        tags.sort_by_key(canonical_json);
    } else {
        tags.sort_by(|left, right| left.as_str().cmp(&right.as_str()));
    }
}
pub(crate) fn source_layout(value: &mut Value) {
    layout(value, Options::source());
}

fn selected_claim(document: &Document, label: &str, unique: bool) -> Result<Sentence, String> {
    let modules = match document {
        Document::ModuleList { modules, .. } => modules,
        Document::Definition(document) => &document.definition.modules,
        Document::Term(_) => {
            return Err("claim normalization requires a module list or definition".into());
        }
    };
    let claims = modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter(|sentence| matches!(sentence.as_ref(), Sentence::Claim { .. }))
        .collect::<Vec<_>>();
    if unique && claims.len() != 1 {
        return Err(format!(
            "expected exactly one KClaim, found {}",
            claims.len()
        ));
    }
    let matching = claims
        .iter()
        .filter(|claim| claim.attributes().get_str("label") == Some(label))
        .collect::<Vec<_>>();
    if matching.len() != 1 {
        return Err(format!(
            "expected exactly one KClaim {label:?}, found {}",
            matching.len()
        ));
    }
    Ok(matching[0].as_ref().clone())
}

pub(crate) fn normalize(
    document: &Document,
    variant: &str,
    raw_policy: &Value,
    label: Option<&str>,
) -> Result<Value, String> {
    let options = Options::for_variant(variant)?;
    let (names, attributes) = policy::read(raw_policy, variant)?;
    let mut normalizer = Normalizer::new(options, &names, &attributes);
    match variant {
        "proof_claim" => {
            let mut claim = selected_claim(
                document,
                label.ok_or("claim normalization requires label")?,
                false,
            )?;
            if claim.attributes().get("priority").is_some() {
                return Err("claims must not carry rule/equation priority".into());
            }
            normalizer.sentence(&mut claim)?;
            Ok(json!({"format":"KRS-IMP-CLAIM","version":1,"term":reader::sentence_value(&claim)?}))
        }
        "static_claim" => {
            selected_claim(
                document,
                label.ok_or("static claim normalization requires label")?,
                true,
            )?;
            if !matches!(document, Document::ModuleList { .. }) {
                return Err("static claim normalization requires KFlatModuleList".into());
            }
            let mut document = document.clone();
            normalizer.document(&mut document)?;
            let mut value = document.to_value()?;
            layout(&mut value, options);
            Ok(value)
        }
        "normalized_definition" => {
            document.definition()?;
            let mut document = document.clone();
            normalizer.document(&mut document)?;
            let mut value = document.to_value()?;
            layout(&mut value, options);
            value["term"]["modules"]
                .as_array_mut()
                .expect("writer emits definition modules")
                .sort_by(|left, right| left["name"].as_str().cmp(&right["name"].as_str()));
            Ok(value)
        }
        _ => {
            let mut term = document.term()?.clone();
            normalizer.term(&mut term)?;
            let value = reader::term_value(&term)?;
            if variant == "behavior" {
                Ok(value)
            } else {
                Ok(reader::envelope(value))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn policy() -> Value {
        json!({"label_map":{},"sort_map":{},"identity_sorts":["Int"],"identity_labels":["f"]})
    }
    #[test]
    fn typed_variables_keep_variant_schemes_and_scope() {
        let term = Term::apply(
            "f",
            ["X", "?Y", "_Z", "X"]
                .into_iter()
                .map(|name| Term::Variable {
                    name: name.into(),
                    sort: Some(Sort::new("Int")),
                })
                .collect(),
        );
        let document = Document::Term(term);
        let behavior = normalize(&document, "behavior", &policy(), None).unwrap();
        assert_eq!(
            behavior["args"]
                .as_array()
                .unwrap()
                .iter()
                .map(|term| term["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            ["V0", "E1", "A2", "V0"]
        );
        assert_eq!(
            normalize(&document, "proof_result", &policy(), None).unwrap()["term"]["args"][0]["name"],
            "O0"
        );
        assert_eq!(
            normalize(&document, "static_proof", &json!({}), None).unwrap()["term"]["args"][1]["name"],
            "V1"
        );
        assert!(
            normalize(
                &Document::Term(Term::variable("X")),
                "static_proof",
                &json!({}),
                None
            )
            .is_err()
        );
    }
    #[test]
    fn typed_sentence_visits_bodies_before_attribute_payloads() {
        let names = NamePolicy::default();
        let attributes = AttributePolicy {
            known_attributes: ["payload".into()].into(),
            metadata_attributes: std::collections::BTreeSet::default(),
            attribute_value_map: BTreeMap::default(),
        };
        let mut options = Options::source();
        options.names = Names::Identity;
        let mut sentence = Sentence::Claim {
            body: Term::variable("B"),
            requires: Term::variable("R"),
            ensures: Term::variable("E"),
            attributes: Attributes::new(BTreeMap::from([(
                "payload".into(),
                json!({"node":"KVariable","name":"A"}),
            )])),
        };
        Normalizer::new(options, &names, &attributes)
            .sentence(&mut sentence)
            .unwrap();
        let out = reader::sentence_value(&sentence).unwrap();
        assert_eq!(out["body"]["name"], "O0");
        assert_eq!(out["requires"]["name"], "O1");
        assert_eq!(out["ensures"]["name"], "O2");
        assert_eq!(out["att"]["att"]["payload"]["name"], "O3");
    }
    #[test]
    fn layout_sorts_syntax_tags_but_preserves_ordinary_attribute_maps() {
        let mut value = json!({"payload":{"tags":["z","a"],"priorities":[["z","a"]]},"syntax":{"node":"KSyntaxAssociativity","tags":["z","a"]}});
        source_layout(&mut value);
        assert_eq!(value["payload"]["tags"], json!(["z", "a"]));
        assert_eq!(value["payload"]["priorities"], json!([["z", "a"]]));
        assert_eq!(value["syntax"]["tags"], json!(["a", "z"]));
    }
}
