//! The declarations the emitted definition states about its sorts, read from the frontend's
//! definition before it is emitted, in the KORE sorts the backend reads.
//!
//! A hooked application evaluates in a loaded definition by the kind of its sorts' domain values,
//! by which sorts have domain values, and by the subsort order
//! ([`k_rust_backend::builtin::DeclarationFacts`]). The emitted definition states each of these
//! from the main module's declarations:
//! - a sort head is declared with `hasDomainValues` exactly when the sort catalog admits domain
//!   values for it ([`SortCatalog::head_admits_domain_values`]), and with the hook its sort
//!   declaration carries;
//! - the kind follows from those two facts by the rule the backend applies
//!   ([`DomainKind::of_declared_sort`]);
//! - the subsort axioms are those `emitted_subsort_pair` states.
//!
//! So an evaluation over these facts ([`k_rust_backend::builtin::evaluate_declared`]) decides an
//! application as an evaluation of the same application in the emitted definition, once loaded,
//! decides it.

use std::cell::OnceCell;

use k_rust_backend::{
    builtin::DeclarationFacts,
    term::{DomainKind, Sort as BackendSort},
};

use super::module_to_kore::{emitted_subsort_pair, encode_kore_sort};
use crate::{
    definition::{AttributeKey, PartialOrder, ProductionCatalog, SortCatalog, SortHead},
    kast::{Sort, identifier},
    kore::ast::Sort as KoreSort,
};

/// The declarations of the sorts of one module, as the definition emitted with that module as
/// its main module states them. Read before the stages after the constant fold, they lack the
/// subsorts those stages add for the cell sorts they generate (`KCell < KCellOpt`, a generated
/// cell sort below `KItem`); none of those sorts has domain values, and the fold asks the subsort
/// order only about the sort of a domain value.
pub(crate) struct EmittedDeclarations<'view, 'definition> {
    sorts: &'view SortCatalog<'definition>,
    productions: &'view ProductionCatalog<'definition>,
    /// The order the emitted subsort axioms state, built on the first subsort question; `None`
    /// when the axioms are cyclic, which emission reports.
    subsorts: OnceCell<Option<PartialOrder<Sort>>>,
}

impl<'view, 'definition> EmittedDeclarations<'view, 'definition> {
    pub(crate) fn new(
        sorts: &'view SortCatalog<'definition>,
        productions: &'view ProductionCatalog<'definition>,
    ) -> Self {
        Self {
            sorts,
            productions,
            subsorts: OnceCell::new(),
        }
    }

    /// The hook the declaration of `sort`'s head carries.
    pub(crate) fn hook(&self, sort: &Sort) -> Option<&str> {
        self.sorts
            .attributes_for(&SortHead::from(sort))
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
    }
}

impl DeclarationFacts for EmittedDeclarations<'_, '_> {
    type Sort = BackendSort;

    fn domain_kind(&self, sort: &BackendSort) -> Option<DomainKind> {
        let frontend = frontend_sort(sort)?;
        DomainKind::of_declared_sort(
            sort,
            self.sorts
                .head_admits_domain_values(&SortHead::from(&frontend)),
            self.hook(&frontend),
        )
    }

    fn has_domain_values(&self, sort: &BackendSort) -> bool {
        frontend_sort(sort).is_some_and(|frontend| {
            self.sorts
                .head_admits_domain_values(&SortHead::from(&frontend))
        })
    }

    fn check_subsort(&self, sub: &BackendSort, sup: &BackendSort) -> bool {
        if sub == sup {
            return true;
        }
        let (Some(sub), Some(sup)) = (frontend_sort(sub), frontend_sort(sup)) else {
            return false;
        };
        self.subsorts
            .get_or_init(|| {
                PartialOrder::new(
                    self.productions
                        .productions()
                        .filter_map(|(_, production)| emitted_subsort_pair(production))
                        .map(|(child, parent)| (child.clone(), parent.clone())),
                )
                .ok()
            })
            .as_ref()
            .is_some_and(|order| order.less_than_eq(&sub, &sup))
    }
}

/// The KORE sort the emitted definition writes for `sort`, as the backend holds it.
pub(crate) fn backend_sort(sort: &Sort) -> BackendSort {
    fn convert(sort: &KoreSort) -> BackendSort {
        match sort {
            KoreSort::Application { name, arguments } => {
                BackendSort::application(name.as_str(), arguments.iter().map(convert).collect())
            }
            KoreSort::Variable(name) => BackendSort::Variable(name.as_str().into()),
        }
    }
    convert(&encode_kore_sort(sort))
}

/// The frontend sort the emitted KORE sort `sort` writes; `None` for a sort variable or a name
/// that no frontend sort encodes.
fn frontend_sort(sort: &BackendSort) -> Option<Sort> {
    let BackendSort::Application { name, arguments } = sort else {
        return None;
    };
    Some(Sort::with_parameters(
        &identifier::decode_sort_name(name).ok()?,
        arguments
            .iter()
            .map(frontend_sort)
            .collect::<Option<Vec<_>>>()?,
    ))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use k_rust_backend::{
        builtin::DeclarationFacts, definition::BackendDefinition, term::Sort as BackendSort,
    };

    use super::EmittedDeclarations;
    use crate::{
        builtin::embedded,
        definition::{Definition, ResolvedDefinition},
        kompile::{
            CompilationBackend, CompileOptions, compile::compile_loaded_definition_observed,
        },
        outer::{LoadOptions, ResolvedSource, load_with_options},
        timings::PhaseTimings,
    };

    /// The definition the constant-folding stage receives when `source` (main module `MAIN`)
    /// compiles, with the embedded prelude unless `prelude` is false, and the emitted
    /// definition, loaded.
    fn fold_input_and_emitted(source: &str, prelude: bool) -> (Definition, BackendDefinition) {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                implicit_sources: if prelude {
                    vec![embedded("prelude.md").expect("the embedded prelude")]
                } else {
                    Vec::new()
                },
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .expect("the definition loads");
        let mut input = None;
        let compiled = compile_loaded_definition_observed(
            &loaded,
            CompileOptions::default(),
            &mut PhaseTimings::default(),
            &mut |stage, definition, _| {
                if stage.name == "constant folding" {
                    input = Some(definition.clone());
                }
            },
        )
        .expect("the definition compiles");
        let kore = crate::kore::parser::parse_definition(&compiled.definition_kore)
            .expect("the emitted definition parses");
        let emitted =
            BackendDefinition::internalize(&kore, "MAIN").expect("the emitted definition loads");
        (input.expect("the fold stage ran"), emitted)
    }

    /// The closed sorts of `definition`: every sort without parameters it declares, and every
    /// instance of a parametric one that a symbol declaration names.
    fn closed_sorts(definition: &BackendDefinition) -> BTreeSet<BackendSort> {
        let mut sorts = definition
            .sorts()
            .iter()
            .filter(|(_, info)| info.parameters.is_empty())
            .map(|(name, _)| BackendSort::application(name.clone(), Vec::new()))
            .collect::<BTreeSet<_>>();
        for symbol in definition.symbols().values() {
            for sort in symbol
                .argument_sorts
                .iter()
                .chain(std::iter::once(&symbol.result_sort))
            {
                if !sort.has_variable() {
                    sorts.insert(sort.clone());
                }
            }
        }
        sorts
    }

    /// The facts the fold reads from the definition it receives are those the emitted
    /// definition states once it is loaded: for every closed sort of the emitted definition, its
    /// kind and whether it has domain values, and whether a sort without parameters that has
    /// domain values is a subsort of each sort without parameters. The fold asks the subsort
    /// order only about a sort with domain values (a literal's, or a hook value's); later stages
    /// add the subsorts of the generated cell sorts, which have none.
    fn assert_facts_agree(source: &str, prelude: bool, compared: &[&str]) {
        let (input, emitted) = fold_input_and_emitted(source, prelude);
        let resolved = ResolvedDefinition::resolve(&input).expect("the fold input resolves");
        let views = resolved.views();
        let main = resolved.main_module_id();
        let facts =
            EmittedDeclarations::new(views.sort_catalog(main), views.production_catalog(main));
        let sorts = closed_sorts(&emitted);
        let names = sorts
            .iter()
            .filter_map(|sort| match sort {
                BackendSort::Application { name, .. } => Some(name.as_ref()),
                BackendSort::Variable(_) => None,
            })
            .collect::<BTreeSet<_>>();
        for name in compared {
            assert!(names.contains(name), "{name} is no sort of {names:?}");
        }
        let mut differences = Vec::new();
        for sort in &sorts {
            let (folded, loaded) = (facts.domain_kind(sort), emitted.domain_kind(sort));
            if folded != loaded {
                differences.push(format!("domain_kind({sort:?}): {folded:?} != {loaded:?}"));
            }
            let (folded, loaded) = (
                facts.has_domain_values(sort),
                DeclarationFacts::has_domain_values(&emitted, sort),
            );
            if folded != loaded {
                differences.push(format!("has_domain_values({sort:?}): {folded} != {loaded}"));
            }
        }
        let simple = sorts
            .iter()
            .filter(|sort| matches!(sort, BackendSort::Application { arguments, .. } if arguments.is_empty()))
            .collect::<Vec<_>>();
        for sub in simple
            .iter()
            .filter(|sub| DeclarationFacts::has_domain_values(&emitted, sub))
        {
            for sup in &simple {
                let (folded, loaded) = (
                    facts.check_subsort(sub, sup),
                    DeclarationFacts::check_subsort(&emitted, sub, sup),
                );
                if folded != loaded {
                    differences.push(format!(
                        "check_subsort({sub:?}, {sup:?}): {folded} != {loaded}"
                    ));
                }
            }
        }
        assert!(
            differences.is_empty(),
            "{} of {} sorts:\n{}",
            differences.len(),
            sorts.len(),
            differences.join("\n")
        );
    }

    /// With the prelude: a token sort, sorts hooked `INT.Int`, `STRING.String`, `BYTES.Bytes` and
    /// `FLOAT.Float` under other names, a subsort chain, a sort of a privately imported module and
    /// the instances of the parametric `MInt` the declarations name.
    #[test]
    fn emitted_declarations_answer_as_the_loaded_emitted_definition() {
        assert_facts_agree(
            r#"
            module HIDDEN
              imports INT
              syntax Secret ::= r"s[0-9]+" [token]
              syntax Int ::= secretLength(Secret) [function, total]
              rule secretLength(_) => 1
            endmodule

            module MAIN-SYNTAX
              imports INT-SYNTAX
              syntax Tok ::= r"tok[0-9]+" [token]
              syntax Op ::= "go" [symbol(go)]
            endmodule

            module MAIN
              imports MAIN-SYNTAX
              imports DOMAINS
              imports BYTES
              imports FLOAT
              imports MINT
              imports private HIDDEN
              configuration <k> $PGM:Op </k>
              syntax MyInt [hook(INT.Int), token]
              syntax MyString [hook(STRING.String), token]
              syntax MyBytes [hook(BYTES.Bytes), token]
              syntax MyFloat [hook(FLOAT.Float), token]
              syntax Low ::= Tok
              syntax Mid ::= Low
              syntax Top ::= Mid | Int
              syntax MInt{64}
              syntax KItem ::= res(K) [symbol(res)]
              syntax MInt{64} ::= wrap(Int) [function, total, hook(MINT.integer), symbol(wrap)]
              rule go => res(#token("tok1", "Tok"))
            endmodule
            "#,
            true,
            &[
                "SortMyInt",
                "SortMyString",
                "SortMyBytes",
                "SortMyFloat",
                "SortTok",
                "SortLow",
                "SortTop",
                "SortSecret",
                "SortMInt",
                "SortMap",
                "SortId",
            ],
        );
    }

    /// Without the prelude: an unhooked `Int`, which the emitted definition still reads as the
    /// integers by its name, and an unhooked `Bool`.
    #[test]
    fn emitted_declarations_answer_as_the_loaded_emitted_definition_without_the_prelude() {
        assert_facts_agree(
            r#"
            module MAIN
              syntax K
              syntax Int ::= r"[\\+\\-]?[0-9]+" [token]
              syntax Bool ::= "true" [token] | "false" [token]
              syntax Name ::= r"[a-z]+" [token]
              syntax Val ::= Int | Name
              syntax KItem ::= res(Val) [symbol(res)]
              configuration <k> res(0) </k>
            endmodule
            "#,
            false,
            &["SortInt", "SortBool", "SortName", "SortVal"],
        );
    }
}
