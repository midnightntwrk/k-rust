//! The binders the KORE emitter generates.
//!
//! A binder the emitter adds, rather than converts from a binder the author wrote, exists to bind
//! something: an existential over a right side's `?` variable, over a variable of an owise
//! competitor, or over an argument of a generated constructor, functional or subsort axiom.
//! One whose variable does not occur free in its body binds nothing, so it stands in place of the
//! binder the construct meant to have. Invariant K3 states that this does not happen, and it is
//! checked here, where the binder is built and is known to be generated, rather than from the
//! spelling of its variable afterwards: an authored binder may have any variable, including one
//! that its body does not mention, and its variable may be spelled like a minted name.
//!
//! - K3 (generated binder): every binder built by this module has its variable free in its body.
//!   KORE variable identity is the name together with the sort, so a body occurrence at another
//!   sort, or one that an inner binder of the same variable binds, does not count.
//!
//! The check is compiled under `cfg(any(debug_assertions, feature = "kompile-invariant-checks"))`,
//! like the other kompile invariants (`kompile::invariants`), and panics on a violation, which is
//! a compiler defect, never a user error. Without it the constructors build the same pattern.
//!
//! Every `\exists` or `\forall` the emitter generates is built here. The converter's quantifier
//! (`term_to_kore`) is the authored path and does not check K3; a rebuild that copies an existing
//! binder at a new sort (`equations::predicate_at`) generates no binder. The emitter
//! generates no `\forall` today; a new one gets its constructor here.

use crate::kore::ast::{Pattern, Sort as KoreSort, Variable};

/// `\exists{sort}(variable, body)`, a binder the emitter generates.
///
/// Under the invariant checks, panics when `variable` does not occur free in `body` (K3).
pub(super) fn generated_exists(sort: KoreSort, variable: Variable, body: Pattern) -> Pattern {
    generated_exists_all(&sort, vec![variable], body)
}

/// `\exists{sort}(v1, \exists{sort}(v2, .. \exists{sort}(vn, body)))` for `variables` `v1 .. vn`:
/// the first variable is the outermost binder.
///
/// Under the invariant checks, panics when some `vi` does not occur free in the body of its own
/// binder, `\exists{sort}(vi+1, .. body)` (K3); the innermost violation is reported.
pub(super) fn generated_exists_all(
    sort: &KoreSort,
    variables: Vec<Variable>,
    body: Pattern,
) -> Pattern {
    // The free variables of the innermost body, computed once: the body of the binder over `vi`
    // has the free variables of `body` less `vi+1 .. vn`.
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    let mut free = k_rust_kore::measure::without_counting(|| body.free_variables());
    let mut pattern = body;
    // Invariant: `pattern` is `body` wrapped in one binder per variable after `variable`, in order,
    // and (under the checks) `free` holds the free variables of `pattern`.
    for variable in variables.into_iter().rev() {
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        {
            assert!(
                free.contains(&variable),
                "kompile invariant {}",
                k3_violation("\\exists", &variable, &pattern)
            );
            free.remove(&variable);
        }
        pattern = Pattern::Exists {
            sort: sort.clone(),
            variable: Box::new(variable),
            body: Box::new(pattern),
        };
    }
    pattern
}

/// The report of a K3 violation: `binder` over `variable` with body `body`.
#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
fn k3_violation(binder: &str, variable: &Variable, body: &Pattern) -> String {
    format!(
        "K3 (generated binder) violated: {binder} binds the compiler-generated variable \
         {}:{}, which does not occur free in its body\n  generated binder's body: {body}",
        variable.name, variable.sort
    )
}

#[cfg(test)]
mod tests {
    use super::{generated_exists, generated_exists_all};
    use crate::kore::ast::{Pattern, Sort as KoreSort, Variable, VariableKind};

    fn sort(name: &str) -> KoreSort {
        KoreSort::Application {
            name: name.into(),
            arguments: Vec::new(),
        }
    }

    fn variable(name: &str, sort_name: &str) -> Variable {
        Variable {
            kind: VariableKind::Element,
            name: name.into(),
            sort: sort(sort_name),
        }
    }

    fn equals(left: Pattern, right: Pattern) -> Pattern {
        Pattern::Equals {
            operand_sort: Box::new(sort("SortInt")),
            result_sort: sort("SortGeneratedTopCell"),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn exists(variable: Variable, body: Pattern) -> Pattern {
        Pattern::Exists {
            sort: sort("SortGeneratedTopCell"),
            variable: Box::new(variable),
            body: Box::new(body),
        }
    }

    /// The panic message of `build`, or `None` when it returns.
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    fn violation(build: impl FnOnce() -> Pattern) -> Option<String> {
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(build));
        outcome.err().map(|payload| {
            payload
                .downcast_ref::<String>()
                .cloned()
                .unwrap_or_else(|| "non-string panic".into())
        })
    }

    /// A generated binder over a variable its body has free builds exactly the binder, with the
    /// first variable outermost.
    #[test]
    fn a_binder_over_a_free_variable_is_built_as_given() {
        let x = variable("VarX", "SortInt");
        let y = variable("VarY", "SortInt");
        let body = equals(Pattern::Variable(x.clone()), Pattern::Variable(y.clone()));
        assert_eq!(
            generated_exists(sort("SortGeneratedTopCell"), x.clone(), body.clone()),
            exists(x.clone(), body.clone())
        );
        assert_eq!(
            generated_exists_all(
                &sort("SortGeneratedTopCell"),
                vec![x.clone(), y.clone()],
                body.clone()
            ),
            exists(x, exists(y, body.clone()))
        );
        assert_eq!(
            generated_exists_all(&sort("SortGeneratedTopCell"), Vec::new(), body.clone()),
            body
        );
    }

    /// K3 is decided by the binding structure, not by the variable's spelling: a binder over an
    /// absent variable, over one an inner binder rebinds, over one present only at another sort,
    /// or a repeated variable, is vacuous whatever its name, and the report names the binder's
    /// variable.
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    #[test]
    fn a_vacuous_generated_binder_panics_whatever_its_variable_is_spelled() {
        let top = || sort("SortGeneratedTopCell");
        let one = || Pattern::DomainValue {
            sort: sort("SortInt"),
            value: "1".into(),
        };
        for name in ["VarX", "Var'Ques'Z", "Var'Unds'Gen0", "Var'QuesUnds'Gen1"] {
            let bound = variable(name, "SortInt");
            let other = variable("VarY", "SortInt");
            let absent = equals(Pattern::Variable(other.clone()), one());
            let rebound = exists(
                bound.clone(),
                equals(Pattern::Variable(bound.clone()), one()),
            );
            let other_sort = equals(
                Pattern::Variable(variable(name, "SortBool")),
                Pattern::Variable(other.clone()),
            );
            for body in [absent, rebound, other_sort] {
                let report = violation(|| generated_exists(top(), bound.clone(), body.clone()))
                    .unwrap_or_else(|| panic!("{name} over {body} is vacuous"));
                assert!(
                    report.starts_with(&format!(
                        "kompile invariant K3 (generated binder) violated: \\exists binds the \
                         compiler-generated variable {name}:SortInt{{}}, which does not occur \
                         free in its body\n  generated binder's body: "
                    )),
                    "{report}"
                );
            }
            // A repeated variable: the outer of the two binders is vacuous.
            let body = equals(Pattern::Variable(bound.clone()), one());
            assert!(
                violation(|| generated_exists_all(
                    &top(),
                    vec![bound.clone(), other.clone(), bound.clone()],
                    equals(body.clone(), Pattern::Variable(other.clone()))
                ))
                .is_some_and(|report| report.contains(&format!("variable {name}:SortInt{{}}"))),
                "{name}"
            );
        }
    }

    /// The innermost vacuous binder of a nest is the one reported: the right side of
    /// `ensures #Exists ?_ . (X ==Int ?_)` lifts its binder `?_Gen0` (at the default sort) and
    /// the body's `?_Gen1`, which only the converted inner binder binds.
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    #[test]
    fn the_innermost_vacuous_binder_of_a_nest_is_reported() {
        let binder = variable("Var'QuesUnds'Gen0", "SortK");
        let body_variable = variable("Var'QuesUnds'Gen1", "SortInt");
        let x = variable("VarX", "SortInt");
        let ensures = exists(
            body_variable.clone(),
            equals(
                Pattern::Variable(x),
                Pattern::Variable(body_variable.clone()),
            ),
        );
        let report = violation(|| {
            generated_exists_all(
                &sort("SortGeneratedTopCell"),
                vec![binder, body_variable],
                ensures,
            )
        })
        .expect("both lifted binders are vacuous");
        assert!(
            report.contains(
                "\\exists binds the compiler-generated variable Var'QuesUnds'Gen1:SortInt{}, \
                 which does not occur free in its body"
            ),
            "{report}"
        );
    }
}
