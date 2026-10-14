//! Declaration classification at the pinned backend, separate from campaign verdicts.

use std::{collections::BTreeMap, fmt, sync::OnceLock};

use k_rust::names::{BuiltinSort, KoreAttribute};
use k_rust::{
    builtin,
    kompile::{CompilationBackend, CompileOptions},
    kore::{
        ast::{Attributes, Sentence},
        parser::parse_definition,
    },
    outer::{LoadOptions, ResolvedSource},
};
use k_rust_backend::{
    builtin::{BuiltinResult, UnsupportedHookReason, evaluate_hook},
    definition::BackendDefinition,
    term::{CollectionMetadata, CollectionSymbols, Sort, Symbol},
};
use kink_patch::Baseline;

use crate::{NativeValidator, ValidatedDefinition};

/// Domain of the canonical census document and its payload digest.
pub const CENSUS_DOMAIN: &str = "kink/declaration-census/v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// A census is natural exactly when it contains no finding.
pub enum CensusVerdict {
    Natural,
    Flagged,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// Rules N (sort names), H (signatures), C (roles), and U (unknown hooks).
pub enum CensusClass {
    N,
    H,
    C,
    U,
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// A declaration that fails a census rule, with compiled KORE provenance.
pub struct CensusFinding {
    pub class: CensusClass,
    pub symbol: String,
    pub hook: Option<String>,
    pub arguments: Vec<String>,
    pub result: String,
    pub expected: Option<String>,
    pub source: Option<String>,
    pub location: Option<[u32; 4]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// An unknown hook verified to produce no value at the pinned backend.
pub struct InertDeclaration {
    pub symbol: String,
    pub hook: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Deterministic declaration findings and verified inert hooks.
pub struct DeclarationCensus {
    findings: Vec<CensusFinding>,
    inert: Vec<InertDeclaration>,
}

impl DeclarationCensus {
    pub fn verdict(&self) -> CensusVerdict {
        if self.findings.is_empty() {
            CensusVerdict::Natural
        } else {
            CensusVerdict::Flagged
        }
    }
    pub fn findings(&self) -> &[CensusFinding] {
        &self.findings
    }
    pub fn inert(&self) -> &[InertDeclaration] {
        &self.inert
    }
    pub fn value(&self) -> serde_json::Value {
        serde_json::json!({
            "census": CENSUS_DOMAIN,
            "k_rust": crate::K_RUST_REVISION,
            "verdict": match self.verdict() { CensusVerdict::Natural => "natural", CensusVerdict::Flagged => "flagged" },
            "findings": self.findings.iter().map(|f| serde_json::json!({
                "class": format!("{:?}", f.class), "symbol": f.symbol, "hook": f.hook,
                "declared": {"arguments": f.arguments, "result": f.result},
                "expected": f.expected, "source": f.source, "location": f.location,
            })).collect::<Vec<_>>(),
            "inert": self.inert.iter().map(|i| serde_json::json!({"symbol": i.symbol, "hook": i.hook})).collect::<Vec<_>>(),
        })
    }
    pub fn text(&self) -> String {
        kink_patch::canonical_json(&self.value())
    }
    pub fn digest(&self) -> kink_patch::Sha256Digest {
        kink_patch::payload_digest(CENSUS_DOMAIN, self.text().as_bytes())
    }
}

/// Computes declarations only. No campaign verdict path calls this function.
pub fn declaration_census(side: &ValidatedDefinition) -> Result<DeclarationCensus, CensusError> {
    let reference = reference()?;
    let backend = internalize(side)?;
    census_backend(&backend, &declaration_attributes(side)?, reference)
}

fn census_backend(
    backend: &BackendDefinition,
    attributes: &BTreeMap<String, Attributes>,
    reference: &Reference,
) -> Result<DeclarationCensus, CensusError> {
    let mut census = DeclarationCensus {
        findings: Vec::new(),
        inert: Vec::new(),
    };
    for builtin in BuiltinSort::ALL {
        let name = builtin.kore_name();
        if let Some(sort) = backend.sorts().get(name) {
            let canonical = canonical_sort_hook(builtin);
            if sort.hook.as_deref() != canonical {
                let mut finding = CensusFinding {
                    class: CensusClass::N,
                    symbol: name.to_owned(),
                    hook: sort.hook.as_ref().map(ToString::to_string),
                    arguments: Vec::new(),
                    result: name.to_owned(),
                    expected: Some(format!("hook {canonical:?}")),
                    source: None,
                    location: None,
                };
                provenance(&mut finding, attributes.get(name))?;
                census.findings.push(finding);
            }
        }
    }
    for symbol in backend.symbols().values() {
        if let Some(collection) = &symbol.attributes.collection
            && !natural_role(symbol, collection, backend)
        {
            census.findings.push(symbol_finding(
                CensusClass::C,
                symbol,
                Some(role_expectation(collection)),
                attributes,
            )?);
        }
        let Some(hook) = symbol.attributes.hook.as_deref() else {
            continue;
        };
        if let Some(signatures) = reference.hooks.get(hook) {
            if !signatures
                .iter()
                .any(|signature| signature_matches(signature, symbol))
                && !natural_collection_hook(symbol, backend, signatures)
            {
                let expected = signatures
                    .iter()
                    .map(signature_text)
                    .collect::<Vec<_>>()
                    .join(" or ");
                census.findings.push(symbol_finding(
                    CensusClass::H,
                    symbol,
                    Some(expected),
                    attributes,
                )?);
            }
        } else if inert_hook(hook) {
            census.inert.push(InertDeclaration {
                symbol: symbol.name.to_string(),
                hook: hook.to_owned(),
            });
        } else {
            census.findings.push(symbol_finding(
                CensusClass::U,
                symbol,
                Some("reference declaration or verified inert hook".to_owned()),
                attributes,
            )?);
        }
    }
    census
        .findings
        .sort_by(|a, b| (&a.symbol, &a.hook).cmp(&(&b.symbol, &b.hook)));
    census
        .inert
        .sort_by(|a, b| (&a.symbol, &a.hook).cmp(&(&b.symbol, &b.hook)));
    Ok(census)
}

fn canonical_sort_hook(sort: BuiltinSort) -> Option<&'static str> {
    match sort {
        BuiltinSort::Int => Some("INT.Int"),
        BuiltinSort::Bool => Some("BOOL.Bool"),
        BuiltinSort::String => Some("STRING.String"),
        BuiltinSort::Bytes => Some("BYTES.Bytes"),
        BuiltinSort::Float => Some("FLOAT.Float"),
        BuiltinSort::Map => Some("MAP.Map"),
        BuiltinSort::List => Some("LIST.List"),
        BuiltinSort::Set => Some("SET.Set"),
        BuiltinSort::K
        | BuiltinSort::KItem
        | BuiltinSort::KConfigVar
        | BuiltinSort::GeneratedTopCell
        | BuiltinSort::GeneratedCounterCell => None,
    }
}

fn inert_hook(hook: &str) -> bool {
    !hook.starts_with("IO.")
        && !FOLDED_HOOKS.contains(&hook)
        && matches!(
            std::panic::catch_unwind(|| evaluate_hook(hook, &[])),
            Ok(Ok(Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented
            ))))
        )
}

fn sort_text(sort: &Sort) -> String {
    match sort {
        Sort::Variable(name) => name.to_string(),
        Sort::Application { name, arguments } if arguments.is_empty() => name.to_string(),
        Sort::Application { name, arguments } => format!(
            "{}{{{}}}",
            name,
            arguments
                .iter()
                .map(sort_text)
                .collect::<Vec<_>>()
                .join(",")
        ),
    }
}
fn signature_text(symbol: &Symbol) -> String {
    format!(
        "({}) -> {}",
        symbol
            .argument_sorts
            .iter()
            .map(sort_text)
            .collect::<Vec<_>>()
            .join(", "),
        sort_text(&symbol.result_sort)
    )
}
fn signature_matches(reference: &Symbol, symbol: &Symbol) -> bool {
    if reference.argument_sorts.len() != symbol.argument_sorts.len() {
        return false;
    }
    let mut bindings = BTreeMap::new();
    reference
        .argument_sorts
        .iter()
        .zip(&symbol.argument_sorts)
        .chain(std::iter::once((
            &reference.result_sort,
            &symbol.result_sort,
        )))
        .all(|(formal, actual)| {
            match_sort(formal, actual, &reference.sort_variables, &mut bindings)
        })
}
fn match_sort(
    formal: &Sort,
    actual: &Sort,
    variables: &[k_rust_backend::term::Name],
    bindings: &mut BTreeMap<String, Sort>,
) -> bool {
    match (formal, actual) {
        (Sort::Variable(name), _) if variables.contains(name) => {
            match bindings.get(name.as_ref()) {
                Some(previous) => previous == actual,
                None => {
                    bindings.insert(name.to_string(), actual.clone());
                    true
                }
            }
        }
        (
            Sort::Application { name, arguments },
            Sort::Application {
                name: actual_name,
                arguments: actual_arguments,
            },
        ) => {
            name == actual_name
                && arguments.len() == actual_arguments.len()
                && arguments
                    .iter()
                    .zip(actual_arguments)
                    .all(|(f, a)| match_sort(f, a, variables, bindings))
        }
        _ => formal == actual,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RolePosition {
    Collection,
    Key,
    Value,
    Element,
    Bool,
}
use RolePosition::{Bool, Collection, Element, Key, Value};

/// Which symbols may carry a C-H hook over a non-standard collection sort C.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RoleCarrier {
    /// Only C's own metadata symbol of this role: `Term::application` canonicalizes exactly
    /// that symbol into a C collection, while any other symbol with the hook is evaluated by
    /// the builtin, which builds K's standard List/Map/Set value whatever its declared sort
    /// (kb/builtin/list.rs `element`/`unit`, map.rs, set.rs; CS-01 review 1, VI-T13 V6).
    Unit,
    Element,
    Concat,
    /// Any symbol: the hook's value is a Bool, not a collection.
    AnySymbol,
}

/// Closed C-H table: positions are taken from the corresponding domains.md declarations.
const COLLECTION_ROLE_POSITIONS: &[(&str, &[RolePosition], RolePosition, RoleCarrier)] = &[
    (
        "MAP.concat",
        &[Collection, Collection],
        Collection,
        RoleCarrier::Concat,
    ),
    ("MAP.unit", &[], Collection, RoleCarrier::Unit),
    (
        "MAP.element",
        &[Key, Value],
        Collection,
        RoleCarrier::Element,
    ),
    (
        "MAP.in_keys",
        &[Key, Collection],
        Bool,
        RoleCarrier::AnySymbol,
    ),
    (
        "SET.concat",
        &[Collection, Collection],
        Collection,
        RoleCarrier::Concat,
    ),
    ("SET.unit", &[], Collection, RoleCarrier::Unit),
    ("SET.element", &[Element], Collection, RoleCarrier::Element),
    (
        "LIST.concat",
        &[Collection, Collection],
        Collection,
        RoleCarrier::Concat,
    ),
    ("LIST.unit", &[], Collection, RoleCarrier::Unit),
    ("LIST.element", &[Element], Collection, RoleCarrier::Element),
];

struct CollectionRoles<'a> {
    namespace: &'static str,
    sort: &'a str,
    symbols: &'a CollectionSymbols,
    key: Option<&'a str>,
    value: Option<&'a str>,
    element: Option<&'a str>,
}
fn collection_roles(metadata: &CollectionMetadata) -> CollectionRoles<'_> {
    match metadata {
        CollectionMetadata::Map(d) => CollectionRoles {
            namespace: "MAP",
            sort: &d.map_sort,
            symbols: &d.symbols,
            key: Some(&d.key_sort),
            value: Some(&d.value_sort),
            element: None,
        },
        CollectionMetadata::List(d) => CollectionRoles {
            namespace: "LIST",
            sort: &d.list_sort,
            symbols: &d.symbols,
            key: None,
            value: None,
            element: Some(&d.element_sort),
        },
        CollectionMetadata::Set(d) => CollectionRoles {
            namespace: "SET",
            sort: &d.list_sort,
            symbols: &d.symbols,
            key: None,
            value: None,
            element: Some(&d.element_sort),
        },
    }
}
fn role_sort(position: RolePosition, roles: &CollectionRoles<'_>) -> Option<Sort> {
    let name = match position {
        Collection => Some(roles.sort),
        Key => roles.key,
        Value => roles.value,
        Element => roles.element,
        Bool => Some("SortBool"),
    }?;
    Some(Sort::simple(name))
}
fn role_signature(
    symbol: &Symbol,
    positions: &[RolePosition],
    result: RolePosition,
    roles: &CollectionRoles<'_>,
) -> bool {
    symbol.sort_variables.is_empty()
        && symbol.argument_sorts.len() == positions.len()
        && symbol
            .argument_sorts
            .iter()
            .zip(positions)
            .all(|(sort, p)| role_sort(*p, roles).as_ref() == Some(sort))
        && role_sort(result, roles).as_ref() == Some(&symbol.result_sort)
}
fn natural_role(
    symbol: &Symbol,
    metadata: &CollectionMetadata,
    backend: &BackendDefinition,
) -> bool {
    let roles = collection_roles(metadata);
    let role = if symbol.name == roles.symbols.unit {
        "unit"
    } else if symbol.name == roles.symbols.element {
        "element"
    } else if symbol.name == roles.symbols.concat {
        "concat"
    } else {
        return false;
    };
    let hook = format!("{}.{role}", roles.namespace);
    symbol.attributes.hook.as_deref() == Some(hook.as_str())
        && backend.sorts().get(roles.sort).is_some_and(|s| {
            s.hook.as_deref()
                == Some(
                    format!(
                        "{}.{}",
                        roles.namespace,
                        match roles.namespace {
                            "MAP" => "Map",
                            "LIST" => "List",
                            _ => "Set",
                        }
                    )
                    .as_str(),
                )
        })
        && COLLECTION_ROLE_POSITIONS
            .iter()
            .any(|(h, args, result, _)| *h == hook && role_signature(symbol, args, *result, &roles))
}
/// Whether `symbol` is a natural collection role (rules C and C-H): its
/// own metadata's unit, element or concat, with the namespace's role hook, over a sort with the
/// namespace's sort hook, at the role's signature.
pub(crate) fn natural_collection_symbol(symbol: &Symbol, backend: &BackendDefinition) -> bool {
    symbol
        .attributes
        .collection
        .as_ref()
        .is_some_and(|metadata| natural_role(symbol, metadata, backend))
}
fn natural_collection_hook(
    symbol: &Symbol,
    backend: &BackendDefinition,
    signatures: &[Symbol],
) -> bool {
    let Some(hook) = symbol.attributes.hook.as_deref() else {
        return false;
    };
    let Some((_, positions, result, carrier)) = COLLECTION_ROLE_POSITIONS
        .iter()
        .find(|(h, _, _, _)| *h == hook)
    else {
        return false;
    };
    // A collection-building role is natural only on the symbol whose own metadata names it
    // for that role; every other metadata, and every symbol without metadata, is a finding.
    let candidates: Vec<&CollectionMetadata> = match carrier {
        RoleCarrier::AnySymbol => backend
            .symbols()
            .values()
            .filter_map(|s| s.attributes.collection.as_ref())
            .collect(),
        RoleCarrier::Unit | RoleCarrier::Element | RoleCarrier::Concat => {
            symbol.attributes.collection.iter().collect()
        }
    };
    candidates.into_iter().any(|metadata| {
        let roles = collection_roles(metadata);
        let carrier_matches = match carrier {
            RoleCarrier::Unit => symbol.name == roles.symbols.unit,
            RoleCarrier::Element => symbol.name == roles.symbols.element,
            RoleCarrier::Concat => symbol.name == roles.symbols.concat,
            RoleCarrier::AnySymbol => true,
        };
        let standard = match roles.namespace {
            "MAP" => "SortMap",
            "LIST" => "SortList",
            _ => "SortSet",
        };
        carrier_matches
            && roles.sort != standard
            && hook.starts_with(&format!("{}.", roles.namespace))
            && [
                &roles.symbols.unit,
                &roles.symbols.element,
                &roles.symbols.concat,
            ]
            .iter()
            .all(|n| {
                backend
                    .symbols()
                    .get(*n)
                    .is_some_and(|s| natural_role(s, metadata, backend))
            })
            && role_signature(symbol, positions, *result, &roles)
            // Require the closed table itself to agree with a standard prelude signature.
            && signatures.iter().any(|s| {
                let standard_roles = CollectionRoles {
                    sort: standard,
                    key: Some("SortKItem"),
                    value: Some("SortKItem"),
                    element: Some("SortKItem"),
                    ..roles
                };
                role_signature(s, positions, *result, &standard_roles)
            })
    })
}
fn role_expectation(metadata: &CollectionMetadata) -> String {
    let roles = collection_roles(metadata);
    format!(
        "{} roles with result {}, unit (), element metadata sorts, concat ({}, {})",
        roles.namespace, roles.sort, roles.sort, roles.sort
    )
}

fn symbol_finding(
    class: CensusClass,
    symbol: &Symbol,
    expected: Option<String>,
    attributes: &BTreeMap<String, Attributes>,
) -> Result<CensusFinding, CensusError> {
    let mut finding = CensusFinding {
        class,
        symbol: symbol.name.to_string(),
        hook: symbol.attributes.hook.as_ref().map(ToString::to_string),
        arguments: symbol.argument_sorts.iter().map(sort_text).collect(),
        result: sort_text(&symbol.result_sort),
        expected,
        source: None,
        location: None,
    };
    provenance(&mut finding, attributes.get(symbol.name.as_ref()))?;
    Ok(finding)
}
fn provenance(
    finding: &mut CensusFinding,
    attributes: Option<&Attributes>,
) -> Result<(), CensusError> {
    let Some(attributes) = attributes else {
        return Ok(());
    };
    finding.source = attributes
        .string(KoreAttribute::Source)
        .map_err(|e| CensusError::Backend(format!("{e:?}")))?
        .map(str::to_owned);
    if finding.source.as_deref().is_some_and(|s| {
        std::path::Path::new(
            s.strip_prefix("Source(")
                .and_then(|s| s.strip_suffix(')'))
                .unwrap_or(s),
        )
        .is_absolute()
    }) {
        return Err(CensusError::Backend(
            "absolute declaration source".to_owned(),
        ));
    }
    if let Some(location) = attributes
        .string(KoreAttribute::Location)
        .map_err(|e| CensusError::Backend(format!("{e:?}")))?
    {
        let values: Vec<u32> = location
            .strip_prefix("Location(")
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(location)
            .split(',')
            .map(|s| s.trim().parse::<u32>())
            .collect::<Result<_, _>>()
            .map_err(|e| CensusError::Backend(e.to_string()))?;
        finding.location = Some(
            values
                .try_into()
                .map_err(|_| CensusError::Backend("location needs four coordinates".to_owned()))?,
        );
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Infrastructure failure; it never yields a natural census.
pub enum CensusError {
    Reference(String),
    Backend(String),
}

impl fmt::Display for CensusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reference(detail) => write!(f, "census reference: {detail}"),
            Self::Backend(detail) => write!(f, "census backend: {detail}"),
        }
    }
}
impl std::error::Error for CensusError {}

/// Every file of the pinned embedded builtin directory.
pub const REFERENCE_FILES: [&str; 9] = [
    "kast.md",
    "prelude.md",
    "domains.md",
    "ffi.md",
    "json.md",
    "rat.md",
    "substitution.md",
    "timer.md",
    "unification.k",
];

struct Reference {
    side: ValidatedDefinition,
    hooks: BTreeMap<String, Vec<Symbol>>,
}

fn load_options() -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![
            builtin::embedded("kast.md").expect("embedded kast"),
            builtin::embedded("prelude.md").expect("embedded prelude"),
        ],
        excluded_module_attributes: vec![
            CompilationBackend::Rust
                .excluded_module_attribute()
                .to_owned(),
        ],
        ..LoadOptions::default()
    }
}

fn load_reference_source(text: String) -> Result<Baseline, String> {
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new("census-reference.k", text),
        "CENSUS-REFERENCE",
        None,
        &mut resolver,
        &load_options(),
    )
    .map_err(|error| error.to_string())
}

fn reference_text(files: &[String], modules: &[String]) -> String {
    let mut text = String::new();
    for file in files {
        text.push_str(&format!("requires \"{file}\"\n"));
    }
    text.push_str("module CENSUS-REFERENCE\n");
    for module in modules {
        text.push_str(&format!("  imports {module}\n"));
    }
    text.push_str("endmodule\n");
    text
}

/// Modules that fail a standalone default compilation at k-rust 927b9ce6.
/// The census tests also check that none declares a hooked symbol.
pub const EXCLUDED_REFERENCE_MODULES: &[&str] = &[
    "KAST",
    "KSEQ",
    "KSEQ-SYMBOLIC",
    "KCELLS",
    "RULE-CELLS",
    "CONFIG-CELLS",
    "K",
    "K-TERM",
    "DEFAULT-LAYOUT",
    "ID-SYNTAX-PROGRAM-PARSING",
    "KVAR-SYNTAX-PROGRAM-PARSING",
];

fn build_reference() -> Result<Reference, CensusError> {
    let files: Vec<String> = REFERENCE_FILES.iter().map(|f| (*f).to_owned()).collect();
    let mut modules = Vec::new();
    for file in REFERENCE_FILES {
        let source = builtin::embedded(file)
            .ok_or_else(|| CensusError::Reference(format!("missing {file}")))?;
        let code = if file.ends_with(".md") {
            k_rust::outer::extract_fenced_k_code(&source.text, "k")
                .map_err(|e| CensusError::Reference(e.to_string()))?
        } else {
            source.text.clone()
        };
        let parsed = k_rust::outer::parse(source.source, &code)
            .map_err(|e| CensusError::Reference(e.to_string()))?;
        modules.extend(
            parsed
                .modules
                .into_iter()
                .filter(|m| {
                    !m.attributes
                        .iter()
                        .any(|a| a.key == CompilationBackend::Rust.excluded_module_attribute())
                        && !EXCLUDED_REFERENCE_MODULES.contains(&m.name.as_str())
                })
                .map(|m| m.name),
        );
    }
    modules.sort();
    modules.dedup();
    let loaded =
        load_reference_source(reference_text(&files, &modules)).map_err(CensusError::Reference)?;
    let side = NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .map_err(|e| CensusError::Reference(e.to_string()))?;
    let backend = internalize(&side).map_err(|e| CensusError::Reference(e.to_string()))?;
    let mut hooks: BTreeMap<String, Vec<Symbol>> = BTreeMap::new();
    for symbol in backend.symbols().values() {
        if let Some(hook) = &symbol.attributes.hook {
            hooks
                .entry(hook.to_string())
                .or_default()
                .push((**symbol).clone());
        }
    }
    // Multiple declarations of one hook must yield the same expected-signature text
    // regardless of the backend symbol map's iteration order.
    for signatures in hooks.values_mut() {
        signatures.sort_by_cached_key(signature_text);
    }
    Ok(Reference { side, hooks })
}

/// The pinned reference compiled once per process; available for census audits.
pub fn reference_prelude() -> Result<&'static ValidatedDefinition, CensusError> {
    reference().map(|reference| &reference.side)
}

fn reference() -> Result<&'static Reference, CensusError> {
    static REFERENCE: OnceLock<Result<Reference, CensusError>> = OnceLock::new();
    REFERENCE
        .get_or_init(build_reference)
        .as_ref()
        .map_err(Clone::clone)
}

/// Internalizes the compiled execution definition with kompile's encoded module identity.
/// Census audits use this same path for standalone reference modules.
pub fn internalize(side: &ValidatedDefinition) -> Result<BackendDefinition, CensusError> {
    let parsed = parse_definition(&side.artifacts().definition_kore)
        .map_err(|e| CensusError::Backend(e.to_string()))?;
    BackendDefinition::internalize_for_source_execution(
        &parsed,
        &k_rust::kast::identifier::encode(&side.definition().main_module),
        &side.artifacts().execution_rewrite_order,
    )
    .map_err(|e| CensusError::Backend(e.to_string()))
}

// Retain the compiled declaration attributes for finding provenance.
fn declaration_attributes(
    side: &ValidatedDefinition,
) -> Result<BTreeMap<String, Attributes>, CensusError> {
    let parsed = parse_definition(&side.artifacts().definition_kore)
        .map_err(|e| CensusError::Backend(e.to_string()))?;
    let mut declarations = BTreeMap::new();
    for module in parsed.modules {
        for sentence in module.sentences {
            match sentence {
                Sentence::SortDeclaration {
                    name, attributes, ..
                } => {
                    declarations.insert(name, attributes);
                }
                Sentence::SymbolDeclaration {
                    symbol, attributes, ..
                } => {
                    declarations.insert(symbol.name, attributes);
                }
                _ => {}
            }
        }
    }
    Ok(declarations)
}

/// Hook-name arms of k-rust 927b9ce6, kompile/passes/constant_folding.rs:286-395.
pub const FOLDED_HOOKS: &[&str] = &[
    "BOOL.not",
    "BOOL.and",
    "BOOL.andThen",
    "BOOL.xor",
    "BOOL.or",
    "BOOL.orElse",
    "BOOL.implies",
    "BOOL.eq",
    "BOOL.ne",
    "INT.not",
    "INT.pow",
    "INT.powmod",
    "INT.mul",
    "INT.tdiv",
    "INT.tmod",
    "INT.ediv",
    "INT.emod",
    "INT.add",
    "INT.sub",
    "INT.shr",
    "INT.shl",
    "INT.and",
    "INT.xor",
    "INT.or",
    "INT.min",
    "INT.max",
    "INT.abs",
    "INT.log2",
    "INT.bitRange",
    "INT.signExtendBitRange",
    "INT.lt",
    "INT.gt",
    "INT.le",
    "INT.ge",
    "INT.eq",
    "INT.ne",
    "STRING.concat",
    "STRING.length",
    "STRING.chr",
    "STRING.ord",
    "STRING.substr",
    "STRING.find",
    "STRING.rfind",
    "STRING.findChar",
    "STRING.rfindChar",
    "STRING.string2int",
    "STRING.int2string",
    "STRING.string2base",
    "STRING.base2string",
    "STRING.replaceAll",
    "STRING.replace",
    "STRING.replaceFirst",
    "STRING.countAllOccurrences",
    "STRING.eq",
    "STRING.ne",
    "STRING.lt",
    "STRING.gt",
    "STRING.le",
    "STRING.ge",
    "STRING.token2string",
    "STRING.string2token",
    "STRING.string2float",
];
