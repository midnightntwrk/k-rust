//! An audit of the rewrite index's sorted keys (`rule::CellIndex::Sorted`) over whole
//! definitions: every rule a sorted key drops for a subject is refuted by the rewrite matcher.
//!
//! A sorted key decides by the subject item's rigid sort alone, and that sort is a function of
//! the item's root (a free constructor in no overload relation, or a domain value) and of its
//! sort. So the audit enumerates, for a definition, every such root as a `<k>` head (applied to
//! fresh variables, since the key reads no argument), puts it in the place of the `<k>` head of
//! the left-hand side of some rules of the definition (the contexts), and checks every rule the
//! key newly drops there: one that the same subject without its rigid sorts keeps, and that its
//! sorted key therefore drops alone.
//!
//! It also checks the order's numbering against `SortGraph::check_subsort` for every pair of
//! numbered sorts.

use std::{collections::BTreeSet, path::Path, sync::Arc};

use k_rust_kore::kore::parser::parse_definition;
use k_rust_kore::names::WellKnownSymbol;

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{TermIndex, rename_apart, subject_index, term_index},
    term::{HeadRole, Sort, Term, TermKind, Variable, items::Items},
};

/// What one definition's audit checked and the rules it found dropped although the matcher does
/// not refute them.
#[derive(Debug, Default)]
pub(crate) struct Audit {
    pub(crate) heads: usize,
    pub(crate) contexts: usize,
    pub(crate) dropped_by_sort: usize,
    pub(crate) order_pairs: usize,
    pub(crate) failures: Vec<String>,
}

/// The `<k>` heads whose rigid sort a subject key reads: every free constructor in no overload
/// relation with no sort parameter, applied to fresh variables of its argument sorts, injected
/// into `KItem` when its sort is a numbered sort below `KItem`.
fn rigid_heads(definition: &BackendDefinition) -> Vec<(String, Term)> {
    let kitem = Sort::simple("SortKItem");
    let sorts = definition.sort_graph();
    definition
        .symbols()
        .values()
        .filter(|symbol| {
            symbol.sort_variables.is_empty()
                && symbol.attributes.head_role() == HeadRole::FreeConstructor
                && !definition.overloads().is_overloaded(&symbol.name)
                && !symbol.is(WellKnownSymbol::Inj)
        })
        .filter_map(|symbol| {
            let arguments = symbol
                .argument_sorts
                .iter()
                .enumerate()
                .map(|(position, sort)| {
                    Term::variable(Variable::new(format!("AuditArg{position}"), sort.clone()))
                })
                .collect();
            let application = Term::application(Arc::clone(symbol), Vec::new(), arguments);
            let sort = &symbol.result_sort;
            let head = if sort == &kitem {
                application
            } else if sorts.check_subsort(sort, &kitem) == Ok(true) && sorts.sort_id(sort).is_some()
            {
                Term::injection(sort.clone(), kitem.clone(), application)
            } else {
                return None;
            };
            Some((symbol.name.to_string(), head))
        })
        .collect()
}

/// `term` with the head of its one `<k>` cell replaced by `head`, along the path `fetch_k_cell`
/// takes, or `None` when the cell is not reached through applications, injections and map
/// entries, or its contents are not `kseq(head, tail)`.
fn with_k_head(term: &Term, head: &Term) -> Option<Term> {
    let holds = |term: &Term| term.attributes().k_cells() > 0;
    match term.kind() {
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } if symbol.is(WellKnownSymbol::KCell) => {
            let [contents] = arguments.as_slice() else {
                return None;
            };
            let TermKind::Application {
                symbol: kseq,
                sort_arguments: kseq_sorts,
                arguments: kseq_arguments,
            } = contents.kind()
            else {
                return None;
            };
            let [_, tail] = kseq_arguments.as_slice() else {
                return None;
            };
            if !kseq.is(WellKnownSymbol::KSeq) {
                return None;
            }
            let contents = Term::application(
                Arc::clone(kseq),
                kseq_sorts.clone(),
                vec![head.clone(), tail.clone()],
            );
            Some(Term::application(
                Arc::clone(symbol),
                sort_arguments.clone(),
                vec![contents],
            ))
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => {
            let position = arguments.iter().position(&holds)?;
            let mut arguments = arguments.clone();
            arguments[position] = with_k_head(&arguments[position], head)?;
            Some(Term::application(
                Arc::clone(symbol),
                sort_arguments.clone(),
                arguments,
            ))
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => Some(Term::injection(
            source.clone(),
            target.clone(),
            with_k_head(term, head)?,
        )),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let entries: Vec<(Term, Term)> = entries.iter().cloned().collect();
            let position = entries
                .iter()
                .position(|(key, value)| holds(key) || holds(value))?;
            let mut entries = entries;
            let (key, value) = entries[position].clone();
            entries[position] = if holds(&key) {
                (with_k_head(&key, head)?, value)
            } else {
                (key, with_k_head(&value, head)?)
            };
            Some(Term::map_of_items(
                Arc::clone(definition),
                Items::from_vec(entries),
                rest.clone(),
            ))
        }
        TermKind::And(..)
        | TermKind::List { .. }
        | TermKind::Set { .. }
        | TermKind::DomainValue { .. }
        | TermKind::Variable(_) => None,
    }
}

/// Audit `definition` with at most `contexts_per_bucket` contexts from each term-index bucket.
pub(crate) fn audit(definition: &BackendDefinition, contexts_per_bucket: usize) -> Audit {
    let mut audit = Audit::default();
    let sorts = definition.sort_graph();
    let numbered = sorts.numbered_sorts().cloned().collect::<Vec<_>>();
    for sup in &numbered {
        let below = sorts
            .numbered_below(sup)
            .expect("a numbered sort is closed with a known head");
        for sub in &numbered {
            audit.order_pairs += 1;
            let id = sorts.sort_id(sub).expect("numbered");
            if below.contains(id) != (sorts.check_subsort(sub, sup) == Ok(true)) {
                audit.failures.push(format!(
                    "numbering disagrees with check_subsort({sub:?}, {sup:?})"
                ));
            }
        }
    }
    let heads = rigid_heads(definition);
    audit.heads = heads.len();
    let theory = definition.rewrite_theory();
    for (bucket, groups) in theory {
        let contexts = groups
            .values()
            .flatten()
            .filter(|stored| stored.lhs.attributes().k_cells() == 1)
            .take(contexts_per_bucket)
            .collect::<Vec<_>>();
        let candidates = groups
            .values()
            .flatten()
            .chain(
                (bucket != &TermIndex::Variable)
                    .then(|| theory.get(&TermIndex::Variable))
                    .flatten()
                    .into_iter()
                    .flat_map(|groups| groups.values().flatten()),
            )
            .filter(|stored| {
                stored
                    .index
                    .cells()
                    .iter()
                    .any(|cell| matches!(cell, crate::rule::CellIndex::Sorted(_)))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            continue;
        }
        for context in contexts {
            audit.contexts += 1;
            for (head_name, head) in &heads {
                let Some(subject) = with_k_head(&context.lhs, head) else {
                    continue;
                };
                if term_index(&subject) != *bucket {
                    continue;
                }
                let key = subject_index(definition, &subject);
                let unsorted = key.without_sorts();
                for stored in &candidates {
                    if stored.index.covers(&key) || !stored.index.covers(&unsorted) {
                        continue;
                    }
                    audit.dropped_by_sort += 1;
                    let renamed = rename_apart(&stored.rule, &subject.attributes().variables, &[]);
                    let rule = renamed
                        .as_ref()
                        .map_or(&*stored.rule, |(renamed, _)| renamed);
                    let result = match_terms_in_definition(
                        MatchMode::Rewrite,
                        definition,
                        &rule.lhs,
                        &subject,
                    );
                    if !matches!(result, MatchResult::Failed(_)) {
                        audit.failures.push(format!(
                            "{} dropped by its sorted key for the <k> head {head_name} in the \
                             context of {}, but matching gives {result:?}",
                            stored.attributes.unique_id, context.attributes.unique_id,
                        ));
                    }
                }
            }
        }
    }
    audit
}

/// Every `*.kore` file under `root` whose definition loads, with the name of its last module.
pub(crate) fn definitions_under(root: &Path) -> Vec<(String, BackendDefinition)> {
    let mut files = BTreeSet::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let Ok(entries) = std::fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path
                .extension()
                .is_some_and(|extension| extension == "kore")
                && path
                    .file_name()
                    .is_some_and(|name| name != "syntaxDefinition.kore")
            {
                files.insert(path);
            }
        }
    }
    files
        .into_iter()
        .filter_map(|path| {
            let source = std::fs::read_to_string(&path).ok()?;
            let syntax = parse_definition(&source).ok()?;
            let main = syntax.modules.last()?.name.clone();
            let definition = BackendDefinition::internalize(&syntax, main.as_str()).ok()?;
            Some((path.display().to_string(), definition))
        })
        .collect()
}

fn report(audits: &[(String, Audit)]) -> String {
    audits
        .iter()
        .map(|(name, audit)| {
            format!(
                "{name}: {} heads, {} contexts, {} dropped by a sorted key, {} sort pairs, {} \
                 failures\n",
                audit.heads,
                audit.contexts,
                audit.dropped_by_sort,
                audit.order_pairs,
                audit.failures.len()
            )
        })
        .collect()
}

/// The audit over every fixture definition of the workspace that loads.
#[test]
fn sorted_keys_drop_only_refuted_rules_in_the_fixture_definitions() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut audits = Vec::new();
    for root in ["k-rust-backend/tests/fixtures", "k-rust/tests/fixtures"] {
        for (name, definition) in definitions_under(&workspace.join(root)) {
            audits.push((name, audit(&definition, 3)));
        }
    }
    let failures = audits
        .iter()
        .flat_map(|(name, audit)| {
            audit
                .failures
                .iter()
                .map(move |failure| format!("{name}: {failure}"))
        })
        .collect::<Vec<_>>();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(audits.len() > 20, "{}", report(&audits));
}

/// The audit over the definitions under the directory `KRUST_INDEX_AUDIT_DIR` names (for
/// example a kbench `prepared` directory): run by hand, as it loads whole semantics.
#[test]
#[ignore = "loads the definitions under KRUST_INDEX_AUDIT_DIR"]
fn sorted_keys_drop_only_refuted_rules_in_the_audited_definitions() {
    let root = std::env::var_os("KRUST_INDEX_AUDIT_DIR").expect("KRUST_INDEX_AUDIT_DIR is set");
    let mut audits = Vec::new();
    for (name, definition) in definitions_under(Path::new(&root)) {
        let audit = audit(&definition, 3);
        eprint!(
            "{}",
            report(std::slice::from_ref(&(
                name.clone(),
                Audit {
                    heads: audit.heads,
                    contexts: audit.contexts,
                    dropped_by_sort: audit.dropped_by_sort,
                    order_pairs: audit.order_pairs,
                    failures: Vec::new(),
                }
            )))
        );
        audits.push((name, audit));
    }
    let failures = audits
        .iter()
        .flat_map(|(name, audit)| {
            audit
                .failures
                .iter()
                .map(move |failure| format!("{name}: {failure}"))
        })
        .collect::<Vec<_>>();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(!audits.is_empty(), "no definition loaded under {root:?}");
}
