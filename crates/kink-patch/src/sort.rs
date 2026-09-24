//! Local sort preservation.
//!
//! k-rust does not sort-check already-parsed rule terms: an ill-sorted
//! structured term compiles with an injection between unrelated sorts, and a
//! non-`Bool` condition compiles (upstream request `structured-term-sort-check`,
//! not yet in the ledger).
//! Until that lands, this check is the only guard. It is conservative: an
//! undecidable sort is a rejection, and a rewrite must not widen its left
//! sort, which rejects some rewrites between sibling sorts that K accepts.

use crate::{field_term, path_in};
use k_rust::definition::{
    DefinitionViews, LabelHead, PartialOrder, ProductionCatalog, ProductionSignature,
    ResolvedDefinition, Sentence,
};
use k_rust::kast::{Label, Sort, Term};
use k_rust::names::BuiltinSort;

/// Productions and subsorts visible in one module of the baseline.
pub(crate) struct Typing<'v, 'a> {
    catalog: &'v ProductionCatalog<'a>,
    subsorts: &'v PartialOrder<Sort>,
}

impl<'v, 'a> Typing<'v, 'a> {
    pub(crate) fn new(
        resolved: &ResolvedDefinition,
        views: &'v DefinitionViews<'a>,
        module: &str,
    ) -> Result<Self, String> {
        let id = resolved
            .module_id(module)
            .ok_or_else(|| format!("module {module} is not resolved"))?;
        let subsorts = views
            .subsorts(id)
            .map_err(|cycle| format!("subsort cycle in {module}: {cycle:?}"))?;
        Ok(Self {
            catalog: views.production_catalog(id),
            subsorts,
        })
    }

    /// The sort a replacement at `path` must have: the old term's sort at a
    /// body root or below a rewrite, sequence or as-pattern; `Bool` at a
    /// condition root; the declared argument sort below an application; the
    /// cast sort below a semantic cast.
    pub(crate) fn position_sort(&self, sentence: &Sentence, path: &[u32]) -> Result<Sort, String> {
        let old = path_in(sentence, path).ok_or("path does not resolve")?;
        let Some((last, parent_path)) = path.split_last() else {
            return Err("empty path".to_owned());
        };
        if parent_path.is_empty() {
            return if *last == 0 {
                self.sort_of(old)
            } else {
                Ok(bool_sort())
            };
        }
        let parent = path_in(sentence, parent_path).ok_or("parent does not resolve")?;
        match parent.unannotated() {
            Term::Apply { label, arguments } => {
                if let Some(cast) = label.semantic_cast_sort() {
                    return Ok(cast);
                }
                let signature = self.signature(label, arguments.len())?;
                let index = usize::try_from(*last).map_err(|error| error.to_string())?;
                signature
                    .arguments
                    .get(index)
                    .cloned()
                    .ok_or_else(|| format!("{} has no argument {index}", label.name))
            }
            _ => self.sort_of(old),
        }
    }

    /// Checks every term field of a rule-like sentence that differs from
    /// `old` (all fields when there is no `old`) at its field position.
    pub(crate) fn check_fields(
        &self,
        sentence: &Sentence,
        old: Option<&Sentence>,
    ) -> Result<(), String> {
        for field in 0..3 {
            let Some(term) = field_term(sentence, field) else {
                continue;
            };
            match old {
                Some(old) if field_term(old, field) == Some(term) => {}
                Some(old) => {
                    let expected = self.position_sort(old, &[field])?;
                    self.check(term, &expected)?;
                }
                None if field == 0 => {
                    self.sort_of(term)?;
                }
                None => self.check(term, &bool_sort())?,
            }
        }
        Ok(())
    }

    pub(crate) fn check(&self, term: &Term, expected: &Sort) -> Result<(), String> {
        let sort = self.sort_of(term)?;
        if self.subsorts.less_than_eq(&sort, expected) {
            Ok(())
        } else {
            Err(format!(
                "{term} has sort {sort}, not a subsort of {expected}"
            ))
        }
    }

    fn sort_of(&self, term: &Term) -> Result<Sort, String> {
        match term.unannotated() {
            Term::Token { sort, .. }
            | Term::Variable {
                sort: Some(sort), ..
            } => Ok(sort.clone()),
            Term::Variable { name, sort: None } => Err(format!(
                "variable {name} has no sort; loaded variables sit under semantic casts"
            )),
            Term::Apply { label, arguments } => {
                if let Some(cast) = label.semantic_cast_sort() {
                    let [argument] = arguments.as_slice() else {
                        return Err(format!("{} takes exactly one argument", label.name));
                    };
                    // A cast over a variable is how the loader types it; a
                    // cast over any other term must agree with it.
                    if !matches!(argument.unannotated(), Term::Variable { .. }) {
                        self.check(argument, &cast)?;
                    }
                    return Ok(cast);
                }
                let signature = self.signature(label, arguments.len())?;
                for (index, argument) in arguments.iter().enumerate() {
                    let declared = &signature.arguments[index];
                    self.check(argument, declared)?;
                }
                Ok(signature.result.clone())
            }
            Term::Rewrite { left, right } => {
                let sort = self.sort_of(left)?;
                self.check(right, &sort)?;
                Ok(sort)
            }
            other => Err(format!("{other} has no local sort")),
        }
    }

    /// The label's unique production signature, which must take `arity`
    /// arguments. Casts are absent from the catalog and handled by callers.
    fn signature(&self, label: &Label, arity: usize) -> Result<&'v ProductionSignature, String> {
        if !label.parameters.is_empty() {
            return Err(format!("parametric label {} is not checked", label.name));
        }
        let signatures = self
            .catalog
            .signatures_for(&LabelHead::from(label))
            .ok_or_else(|| format!("unknown label {}", label.name))?;
        let mut signatures = signatures.iter();
        let (Some(signature), None) = (signatures.next(), signatures.next()) else {
            return Err(format!("overloaded label {}", label.name));
        };
        if signature.arguments.len() == arity {
            Ok(signature)
        } else {
            Err(format!(
                "{} takes {} arguments, not {arity}",
                label.name,
                signature.arguments.len()
            ))
        }
    }
}

fn bool_sort() -> Sort {
    Sort::builtin(BuiltinSort::Bool)
}
