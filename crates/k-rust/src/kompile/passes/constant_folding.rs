//! ```toml algorithm
//! id = "kompile.constant_folding.evaluate"
//! name = "bottom-up evaluation of constant hooked operations"
//! sites = ["constant_fold", "constant_fold_pass", "Folder::fold", "Folder::try_fold"]
//! variable = "N = visited term nodes; h = term height"
//! counters = []
//! no_counter = "constant folding has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N x h) plus hook-specific arithmetic cost"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Compile-time evaluation of pure `BOOL`, `INT`, `STRING` and `FLOAT` hooks on literals, through
//! the backend's evaluation entry ([`k_rust_backend::builtin::evaluate_declared`]): the fold
//! writes the value the backend computes for an application outside an execution, at the
//! application's declared sort, and computes nothing itself, in every build.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeMap, fmt};

use num_bigint::BigInt;

use k_rust_backend::{
    builtin::{BuiltinResult, DeclarationFacts, evaluate_declared},
    evaluation::EvaluationMode,
    term::{DomainKind, Sort as BackendSort, Term as BackendTerm, TermKind},
};

use super::super::declaration_facts::{EmittedDeclarations, backend_sort};
use super::super::module_to_kore::encode_kore_sort;
use super::super::term_to_kore::{token_payload, token_text};
use crate::definition::AttributeKey;
use crate::{
    definition::{
        Definition, DefinitionViews, LabelHead, ModuleId, ProductionCatalog, ProductionItem,
        Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term, TermParts},
    kore::{ast::KoreString, string::LiteralEncoding},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstantFoldingError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ConstantFoldingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "constant folding produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ConstantFoldingError {}

/// Replace constant applications of pure hooks on the right-hand sides and conditions of local
/// rules by the literals of their values, leaving every application the fold does not evaluate.
pub fn constant_fold(definition: &Definition) -> Result<Definition, ConstantFoldingError> {
    super::super::pipeline::run_standalone(
        definition,
        constant_fold_pass,
        Some(GeneratingPass::ConstantFolding),
    )
}

pub(crate) fn constant_fold_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ConstantFoldingError> {
    let resolved = input.resolved_raw().map_err(|error| ConstantFoldingError {
        diagnostics: vec![Diagnostic {
            severity: Severity::Error,
            code: DiagnosticCode::InvalidConstantFolding,
            message: error.to_string(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        }],
    })?;
    let views = resolved.views();
    // The emitted definition states the declarations of its main module's sorts, which the
    // backend reads when it evaluates an application of the loaded definition.
    let main = resolved.main_module_id();
    let facts = EmittedDeclarations::new(views.sort_catalog(main), views.production_catalog(main));
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let folder = Folder::new(&views, module_id, &facts);
        for sentence in &mut module.local_sentences {
            // Only rules change. The kind is decided before taking a mutable sentence, which
            // copies a shared one, so every other kind stays shared.
            match &**sentence {
                Sentence::Rule { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = sentence
            else {
                unreachable!("copy-on-write keeps the kind decided above");
            };
            *body = folder.fold(body.clone(), Position::Both);
            *requires = folder.fold(requires.clone(), Position::Right);
            *ensures = folder.fold(ensures.clone(), Position::Right);
        }
    }
    Ok(output)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Position {
    Both,
    Left,
    Right,
}

struct Folder<'view, 'definition> {
    productions: &'view ProductionCatalog<'definition>,
    facts: &'view EmittedDeclarations<'view, 'definition>,
}

impl<'view, 'definition> Folder<'view, 'definition> {
    fn new(
        views: &'view DefinitionViews<'definition>,
        module: ModuleId,
        facts: &'view EmittedDeclarations<'view, 'definition>,
    ) -> Self {
        Self {
            productions: views.production_catalog(module),
            facts,
        }
    }

    // Invariant: `fold` rebuilds `term` bottom-up, folding an `Apply` in `Position::Right` only after its `arguments` are folded; each call recurses into the immediate subterms of `term`, so its finite depth bounds the recursion.
    fn fold(&self, term: Term, position: Position) -> Term {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated().into_parts() {
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.fold(*left, Position::Left)),
                right: Box::new(self.fold(*right, Position::Right)),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(self.fold(*pattern, position)),
                alias: Box::new(self.fold(*alias, position)),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.fold(item, position))
                    .collect(),
            ),
            TermParts::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.fold(argument, position))
                    .collect::<Vec<_>>();
                // An application the fold does not evaluate keeps its meaning as written: the
                // fold only replaces a term by a token that denotes the same value.
                if position == Position::Right
                    && let Some(token) = self.try_fold(&label, &arguments)
                {
                    return token;
                }
                Term::Apply { label, arguments }
            }
            leaf @ (TermParts::InjectedLabel(_)
            | TermParts::Variable { .. }
            | TermParts::Token { .. }) => Term::from(leaf),
            TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        match metadata {
            Some(metadata) => rebuilt.with_metadata(metadata),
            None => rebuilt,
        }
    }

    /// The token an application folds to, `None` when it stays as written: an application of a
    /// pure hook whose value on these literals the backend computes outside an execution, at
    /// exactly the declared result sort, within `MAX_FOLDED_BITS`.
    fn try_fold(&self, label: &Label, arguments: &[Term]) -> Option<Term> {
        let application = self.application(label, arguments)?;
        self.evaluate(&application)
    }

    /// `label` applied to `arguments` as the fold reads it: an application of a pure hook of
    /// the `BOOL`, `INT`, `STRING` or `FLOAT` namespace to tokens, with its declared argument and
    /// result sorts. `None` for any other application.
    fn application<'a>(&'a self, label: &Label, arguments: &'a [Term]) -> Option<Application<'a>> {
        let production = self
            .productions
            .productions_for(&LabelHead::from(label))
            .first()
            .map(|id| self.productions.production(*id))?;
        let Sentence::Production {
            parameters,
            sort,
            items,
            attributes,
            ..
        } = production
        else {
            unreachable!()
        };
        let hook = attributes.string(AttributeKey::Hook)?;
        // Only a `function` production is emitted as a hooked symbol, which the backend evaluates
        // (`interpreted_hook`), and an `impure` one depends on more than its arguments. A `macro`
        // or `alias` production means its expansion, which the definition's rules state and
        // macro expansion, after this pass, substitutes; the hook does not compute it.
        if !attributes.has(AttributeKey::Function)
            || attributes.has(AttributeKey::Impure)
            || AttributeKey::MACRO_LIKE
                .iter()
                .any(|key| attributes.has(*key))
            || !matches!(
                hook.split_once('.').map(|pair| pair.0),
                Some("BOOL" | "INT" | "STRING" | "FLOAT")
            )
        {
            return None;
        }
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only the listed variants are special here"
        )]
        let tokens = arguments
            .iter()
            .map(|argument| match argument.unannotated() {
                Term::Token { token, sort } => Some((token.as_str(), sort)),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        // A result sort that mentions a sort parameter is known only through the label's
        // instance; a label without one (as loaded, before sort injection solves it) gives the
        // folded token no sort. A result sort free of parameters is the token's sort whatever
        // the instance.
        if parameters.len() != label.parameters.len()
            && parameters
                .iter()
                .any(|parameter| sort_mentions(sort, parameter))
        {
            return None;
        }
        let substitution = parameters
            .iter()
            .cloned()
            .zip(label.parameters.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        // The sort each argument is declared at, `None` where it mentions a parameter the label
        // gives no instance of.
        let argument_sorts = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            })
            .map(|declared| {
                let declared = substitute_sort(declared, &substitution);
                (!parameters
                    .iter()
                    .any(|parameter| sort_mentions(&declared, parameter)))
                .then_some(declared)
            })
            .collect::<Vec<_>>();
        if argument_sorts.len() != tokens.len() {
            return None;
        }
        Some(Application {
            hook,
            tokens,
            argument_sorts,
            result_sort: substitute_sort(sort, &substitution),
            total: attributes.has(AttributeKey::Total) || attributes.has(AttributeKey::Functional),
        })
    }

    /// The token of the value the backend's evaluation entry gives `application` outside an
    /// execution, over the declarations the emitted definition states: the same composition, on
    /// the same arguments, as an evaluation of the application in the loaded definition, so the
    /// token stands exactly where that evaluation gives the same value.
    fn evaluate(&self, application: &Application<'_>) -> Option<Term> {
        let arguments = application
            .tokens
            .iter()
            .zip(&application.argument_sorts)
            .map(|((token, sort), declared)| self.argument(token, sort, declared.as_ref()))
            .collect::<Option<Vec<_>>>()?;
        let (result_sort, encoding) = emitted(&application.result_sort);
        let Ok(Ok(BuiltinResult::Value(value))) = evaluate_declared(
            application.hook,
            &arguments,
            &result_sort,
            application.total,
            self.facts,
            EvaluationMode::Proof,
            Some(MAX_FOLDED_BITS),
        ) else {
            return None;
        };
        // A value of a strict subsort of the result sort is an injection, which no token writes.
        let TermKind::DomainValue { sort, value } = value.kind() else {
            return None;
        };
        if *sort != result_sort || exceeds_folded_bits(self.facts.domain_kind(&result_sort), value)?
        {
            return None;
        }
        Some(Term::Token {
            token: token_text(value, self.facts.hook(&application.result_sort), encoding)?,
            sort: application.result_sort.clone(),
        })
    }

    /// The term the emitted definition writes for the token `token` of sort `sort` as an
    /// argument declared at `declared`: the domain value the loaded definition reads from its
    /// literal, injected into `declared` when `sort` is a strict subsort of it. `None` when the
    /// token is no domain value of its sort there, or its sort is not below `declared`. An
    /// argument whose declared sort mentions an uninstantiated parameter is at its own sort.
    fn argument(&self, token: &str, sort: &Sort, declared: Option<&Sort>) -> Option<BackendTerm> {
        let (backend, encoding) = emitted(sort);
        let payload = token_payload(token, self.facts.hook(sort), encoding).ok()?;
        let value = BackendTerm::domain_value_in(self.facts, backend.clone(), payload)?;
        let Some(declared) = declared
            .map(backend_sort)
            .filter(|declared| *declared != backend)
        else {
            return Some(value);
        };
        self.facts
            .check_subsort(&backend, &declared)
            .then(|| BackendTerm::injection(backend, declared, value))
    }
}

/// An application of a pure hook to tokens, as [`Folder::application`] reads it.
struct Application<'a> {
    hook: &'a str,
    tokens: Vec<(&'a str, &'a Sort)>,
    argument_sorts: Vec<Option<Sort>>,
    result_sort: Sort,
    total: bool,
}

/// The KORE sort the emitted definition writes for `sort`, as the backend holds it, and the
/// encoding of the payloads of its domain values.
fn emitted(sort: &Sort) -> (BackendSort, LiteralEncoding) {
    (
        backend_sort(sort),
        LiteralEncoding::of_domain_value(&encode_kore_sort(sort)),
    )
}

/// The largest value the fold writes into a definition, in bits: an `Int`'s bit length, and eight
/// times the length of any other domain value's payload (a `String`'s UTF-8, a `Float`'s
/// canonical text). A compile must not spend memory unrelated to the size of its input on what it
/// emits, and a folded token is part of the emitted definition, read on every load, so a larger
/// value is left for execution: 2^20 bits is 315,653 decimal digits. The backend's bound on
/// `^Int` and `<<Int` results is never below this one (asserted below), so the fold never writes
/// a value the backend would not compute.
pub(crate) const MAX_FOLDED_BITS: u64 = 1 << 20;

const _: () = assert!(MAX_FOLDED_BITS <= k_rust_backend::builtin::MAX_INT_RESULT_BITS);

/// Whether the domain value `value`, of a sort of kind `kind`, is larger than
/// `MAX_FOLDED_BITS`; `None` for an `Int` payload that is not UTF-8, or that is read as an
/// integer and is no decimal (a value the backend built has its kind's canonical text, so
/// neither occurs). An integer's canonical
/// text has no leading zero, so `d` digits bound its bit length between
/// `floor((d - 1) log2 10) + 1` and `ceil(d log2 10)`; only a length near the bound is read as
/// an integer.
fn exceeds_folded_bits(kind: Option<DomainKind>, value: &KoreString) -> Option<bool> {
    if kind != Some(DomainKind::Int) {
        return Some(8 * value.as_bytes().len() as u64 > MAX_FOLDED_BITS);
    }
    let text = value.as_utf8().ok()?;
    let digits = text.strip_prefix('-').unwrap_or(text).len() as u64;
    // log2 10 is between 3.3219 and 3.3220.
    if digits.saturating_mul(33_220).div_ceil(10_000) <= MAX_FOLDED_BITS {
        return Some(false);
    }
    if digits.saturating_sub(1).saturating_mul(33_219) / 10_000 + 1 > MAX_FOLDED_BITS {
        return Some(true);
    }
    Some(text.parse::<BigInt>().ok()?.bits() > MAX_FOLDED_BITS)
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| {
        Sort::with_parameters(
            &sort.name,
            sort.parameters
                .iter()
                .map(|parameter| substitute_sort(parameter, substitution))
                .collect(),
        )
    })
}

/// Whether `sort` is `parameter` or has it among its (nested) sort arguments.
fn sort_mentions(sort: &Sort, parameter: &Sort) -> bool {
    sort == parameter
        || sort
            .parameters
            .iter()
            .any(|argument| sort_mentions(argument, parameter))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The bit length of a folded integer is decided from its digits away from the bound and by
    /// reading it near the bound; any other value is measured by its payload's length.
    #[test]
    fn measures_folded_values_by_their_bit_length() {
        let int = |text: String| exceeds_folded_bits(Some(DomainKind::Int), &text.into());
        let power = |exponent: u64| (BigInt::from(1) << exponent).to_string();
        assert_eq!(int("0".into()), Some(false));
        assert_eq!(int(format!("-{}", power(100))), Some(false));
        assert_eq!(int(power(MAX_FOLDED_BITS - 1)), Some(false));
        assert_eq!(int(format!("-{}", power(MAX_FOLDED_BITS - 1))), Some(false));
        assert_eq!(int(power(MAX_FOLDED_BITS)), Some(true));
        assert_eq!(int("9".repeat(400_000)), Some(true));
        let text = |bytes: u64| -> KoreString { "x".repeat(bytes as usize).into() };
        assert_eq!(
            exceeds_folded_bits(Some(DomainKind::String), &text(MAX_FOLDED_BITS / 8)),
            Some(false)
        );
        assert_eq!(
            exceeds_folded_bits(None, &text(MAX_FOLDED_BITS / 8 + 1)),
            Some(true)
        );
    }
}
