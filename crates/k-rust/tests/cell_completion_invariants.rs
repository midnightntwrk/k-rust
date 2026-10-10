//! Metamorphic invariants of cell completion (`concretize_cells`), checked by krust against
//! itself. Each test compares spellings of a rule that denote the same thing, or a rule with its
//! mirror, and requires that they compile alike: both rejected, or both accepted with the same
//! compiled body up to the names of variables.
//!
//! These are the class tests of `draft/open-issues-2026-10/tickets/cells-tickets.md`. They fail
//! on `934d29e7` and are ignored until the tickets are implemented.

use k_rust::{
    definition::Sentence,
    kast::Term,
    kompile::{
        add_implicit_computation_cell, concretize_cells, resolve_fresh_constants,
        resolve_semantic_casts,
    },
    outer::{ResolvedSource, load},
};
use std::collections::BTreeMap;

fn parsed(source: &str) -> k_rust::definition::Definition {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    load(
        ResolvedSource::new("definition.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap()
    .into_definition()
}

/// The definition with `configuration`, the rule `rule` labelled `probe` and the productions
/// `extra`, prepared for cell completion.
fn prepared(extra: &str, configuration: &str, rule: &str) -> k_rust::definition::Definition {
    let source = format!(
        r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration {configuration}
          rule {rule} [label(probe)]
          syntax K
          syntax Map
          {extra}
        endmodule
        "#,
    );
    let definition = resolve_semantic_casts(&parsed(&source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    resolve_fresh_constants(&definition, 0).unwrap()
}

/// The body of the rule labelled `probe` in `definition`.
fn probe_body(definition: &k_rust::definition::Definition) -> Term {
    let bodies = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("probe") => Some(body.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [body] = bodies.as_slice() else {
        panic!("expected one rule labelled probe, found {bodies:?}")
    };
    body.clone()
}

/// The body of the rule labelled `probe` as written (before cell completion).
fn written_in(extra: &str, configuration: &str, rule: &str) -> Term {
    probe_body(&prepared(extra, configuration, rule))
}

/// The body of the rule labelled `probe` after cell completion, or the completion errors.
fn completed_in(extra: &str, configuration: &str, rule: &str) -> Result<Term, Vec<String>> {
    let transformed = concretize_cells(&prepared(extra, configuration, rule)).map_err(|error| {
        error
            .diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect::<Vec<_>>()
    })?;
    Ok(probe_body(&transformed))
}

fn completed(configuration: &str, rule: &str) -> Result<Term, Vec<String>> {
    completed_in("", configuration, rule)
}

/// `term` with every rewrite's sides swapped.
fn mirrored(term: &Term) -> Term {
    map(term, &mut |term| match term {
        Term::Rewrite { left, right } => Some(Term::Rewrite {
            left: Box::new(mirrored(right)),
            right: Box::new(mirrored(left)),
        }),
        _ => None,
    })
}

/// `term` with every alias `P #as V` replaced by its pattern `P`.
fn without_aliases(term: &Term) -> Term {
    map(term, &mut |term| match term {
        Term::As { pattern, .. } => Some(without_aliases(pattern)),
        _ => None,
    })
}

/// Rebuild `term` bottom-up, replacing each node for which `replace` gives a term.
fn map(term: &Term, replace: &mut impl FnMut(&Term) -> Option<Term>) -> Term {
    let term = term.unannotated();
    if let Some(replaced) = replace(term) {
        return replaced;
    }
    match term {
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| map(argument, replace))
                .collect(),
        },
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(map(left, replace)),
            right: Box::new(map(right, replace)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(map(pattern, replace)),
            alias: Box::new(map(alias, replace)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.iter().map(|item| map(item, replace)).collect())
        }
        other => other.clone(),
    }
}

/// Whether `left` and `right` are the same term, ignoring annotations.
fn same(left: &Term, right: &Term) -> bool {
    match (left.unannotated(), right.unannotated()) {
        (
            Term::Apply { label, arguments },
            Term::Apply {
                label: other_label,
                arguments: other_arguments,
            },
        ) => {
            label == other_label
                && arguments.len() == other_arguments.len()
                && arguments
                    .iter()
                    .zip(other_arguments)
                    .all(|(argument, other)| same(argument, other))
        }
        (
            Term::Rewrite { left, right },
            Term::Rewrite {
                left: other_left,
                right: other_right,
            },
        )
        | (
            Term::As {
                pattern: left,
                alias: right,
            },
            Term::As {
                pattern: other_left,
                alias: other_right,
            },
        ) => same(left, other_left) && same(right, other_right),
        (Term::Sequence(items), Term::Sequence(other_items)) => {
            items.len() == other_items.len()
                && items
                    .iter()
                    .zip(other_items)
                    .all(|(item, other)| same(item, other))
        }
        (left, right) => left == right,
    }
}

/// `term` printed with its variables renamed `V0`, `V1`, ... in order of first occurrence (their
/// sorts kept), and a rewrite of a term to itself printed as that term (it denotes the term): two
/// terms print alike exactly when they are equal up to the names of variables and such rewrites.
fn canonical(term: &Term) -> String {
    fn print(term: &Term, names: &mut BTreeMap<String, usize>, output: &mut String) {
        match term.unannotated() {
            Term::Apply { label, arguments } => {
                output.push_str(&label.name);
                output.push('(');
                for (index, argument) in arguments.iter().enumerate() {
                    if index > 0 {
                        output.push(',');
                    }
                    print(argument, names, output);
                }
                output.push(')');
            }
            Term::Variable { name, sort } => {
                let next = names.len();
                let index = *names.entry(name.clone()).or_insert(next);
                output.push_str(&format!("V{index}"));
                if let Some(sort) = sort {
                    output.push_str(&format!(":{sort}"));
                }
            }
            Term::Token { token, sort } => output.push_str(&format!("{token:?}:{sort}")),
            Term::Rewrite { left, right } if same(left, right) => print(left, names, output),
            Term::Rewrite { left, right } => {
                output.push('(');
                print(left, names, output);
                output.push_str("=>");
                print(right, names, output);
                output.push(')');
            }
            Term::As { pattern, alias } => {
                output.push('(');
                print(pattern, names, output);
                output.push_str(" #as ");
                print(alias, names, output);
                output.push(')');
            }
            Term::Sequence(items) => {
                output.push('[');
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        output.push_str("~>");
                    }
                    print(item, names, output);
                }
                output.push(']');
            }
            Term::InjectedLabel(label) => output.push_str(&format!("#klabel({})", label.name)),
            Term::Annotated { .. } => unreachable!("unannotated"),
        }
    }
    let mut output = String::new();
    print(term, &mut BTreeMap::new(), &mut output);
    output
}

/// The outcome of completing `rule`, comparable across spellings: the canonical body, or
/// rejection.
fn outcome(configuration: &str, rule: &str) -> Result<String, Vec<String>> {
    completed(configuration, rule).map(|body| canonical(&body))
}

/// Every spelling in `spellings` compiles alike: all rejected, or all accepted to one canonical
/// body. Returns the description of each failing pair.
fn disagreements(configuration: &str, spellings: &[&str]) -> Vec<String> {
    let outcomes = spellings
        .iter()
        .map(|rule| (*rule, outcome(configuration, rule)))
        .collect::<Vec<_>>();
    let (first, expected) = &outcomes[0];
    outcomes[1..]
        .iter()
        .filter(|(_, outcome)| match (expected, outcome) {
            (Ok(expected), Ok(outcome)) => expected != outcome,
            (Err(_), Err(_)) => false,
            _ => true,
        })
        .map(|(rule, outcome)| {
            format!("\n  {first}\n    -> {expected:?}\n  {rule}\n    -> {outcome:?}")
        })
        .collect()
}

fn assert_no_disagreements(cases: &[(&str, Vec<&str>)]) {
    let failures = cases
        .iter()
        .flat_map(|(configuration, spellings)| disagreements(configuration, spellings))
        .collect::<Vec<_>>();
    assert!(
        failures.is_empty(),
        "{} spellings compile differently:{}",
        failures.len(),
        failures.join("")
    );
}

/// [`assert_no_disagreements`], where the first spelling of each case must also compile: these
/// cases are over-rejections, and a change that rejected every spelling would otherwise pass.
fn assert_compile_alike(cases: &[(&str, Vec<&str>)]) {
    let failures = cases
        .iter()
        .flat_map(|(configuration, spellings)| {
            let anchor = match outcome(configuration, spellings[0]) {
                Ok(_) => Vec::new(),
                Err(errors) => vec![format!("\n  {}\n    -> rejected: {errors:?}", spellings[0])],
            };
            anchor
                .into_iter()
                .chain(disagreements(configuration, spellings))
        })
        .collect::<Vec<_>>();
    assert!(
        failures.is_empty(),
        "{} spellings compile differently:{}",
        failures.len(),
        failures.join("")
    );
}

const PLAIN: &str = "<T> <k> 0 </k> <a> <y> 0 </y> <z> 0 </z> <w> 0 </w> </a> <b> 0 </b> </T>";

/// Ticket C1 (item 3). A rule with local rewrites means its two projections: the left side with
/// every rewrite replaced by its left side, and the right side likewise. In a bag the place of a
/// rewrite is immaterial, so a rewrite of a bag of cells of distinct, non-repeated sorts denotes
/// the same rule as one rewrite per cell, and two rewrites of one non-repeated slot (one removing,
/// one adding) the same rule as one rewrite of that slot. Completion must not depend on which is
/// written, nor on whether the parent is omitted, written closed or written open.
///
/// (Stepback additions: the merged and factored forms, the cross-level form and the forms inside
/// a written `multiplicity="*"` instance.)
#[test]
#[ignore = "reproduces FOLLOWUPS: Cells: mixed-sort rewrite bags written without their parent are not completed"]
fn a_rewrite_of_several_cells_compiles_as_one_rewrite_per_cell() {
    let mut cases = Vec::new();
    let cells: &[(&str, &str, &str)] = &[("y", "1", "2"), ("z", "3", "4"), ("w", "5", "6")];
    let mixed = |cells: &[&(&str, &str, &str)]| {
        let side = |right: bool| {
            cells
                .iter()
                .map(|(name, left, right_value)| {
                    format!(
                        "<{name}> {} </{name}>",
                        if right { right_value } else { left }
                    )
                })
                .collect::<Vec<_>>()
                .join(" ")
        };
        format!("({} => {})", side(false), side(true))
    };
    let split = |cells: &[&(&str, &str, &str)]| {
        cells
            .iter()
            .map(|(name, left, right)| {
                format!("(<{name}> {left} </{name}> => <{name}> {right} </{name}>)")
            })
            .collect::<Vec<_>>()
            .join(" ")
    };
    let mut rules = Vec::new();
    for size in [2, 3] {
        for chosen in cells.iter().collect::<Vec<_>>().windows(size) {
            let (mixed, split) = (mixed(chosen), split(chosen));
            let closed_rest = cells
                .iter()
                .filter(|cell| !chosen.contains(cell))
                .map(|(name, _, _)| format!("<{name}> {} </{name}>", name.to_uppercase()))
                .collect::<Vec<_>>()
                .join(" ");
            for wrap in [
                "{}".to_owned(),
                "<a> {} ... </a>".to_owned(),
                format!("<a> {{}} {closed_rest} </a>"),
            ] {
                rules.push((wrap.replace("{}", &mixed), wrap.replace("{}", &split)));
            }
        }
    }
    // One level up: a rewrite of <k> and <b>, children of the top cell.
    rules.push((
        "(<k> 0 </k> <b> B </b> => <k> 1 </k> <b> B </b>)".to_owned(),
        "(<k> 0 </k> => <k> 1 </k>) (<b> B </b> => <b> B </b>)".to_owned(),
    ));
    rules.push((
        "<T> (<k> 0 </k> <b> B </b> => <k> 1 </k> <b> B </b>) ... </T>".to_owned(),
        "<T> (<k> 0 </k> => <k> 1 </k>) (<b> B </b> => <b> B </b>) ... </T>".to_owned(),
    ));
    // Cells of different parents, the parent of one (`<a>`) unique in the top cell.
    rules.push((
        "(<y> 1 </y> <k> 0 </k> => <y> 2 </y> <k> 1 </k>)".to_owned(),
        "(<y> 1 </y> => <y> 2 </y>) (<k> 0 </k> => <k> 1 </k>)".to_owned(),
    ));
    // A cell carried unchanged inside the rewrite.
    rules.push((
        "<a> (<y> Y </y> <z> Z </z> => <y> Y </y> <z> 1 </z>) ... </a>".to_owned(),
        "<a> <y> Y </y> (<z> Z </z> => <z> 1 </z>) ... </a>".to_owned(),
    ));
    // A bag variable carried unchanged inside the rewrite, in a closed parent.
    rules.push((
        "<a> (<y> 1 </y> B:Bag => <y> 2 </y> B:Bag) </a>".to_owned(),
        "<a> (<y> 1 </y> => <y> 2 </y>) B:Bag </a>".to_owned(),
    ));
    // One slot rewritten by a removal and an addition.
    rules.push((
        "<a> <y> Y </y> (<z> Z </z> => .Bag) (.Bag => <z> 1 </z>) ... </a>".to_owned(),
        "<a> <y> Y </y> (<z> Z </z> => <z> 1 </z>) ... </a>".to_owned(),
    ));
    for (mixed, split) in &rules {
        cases.push((PLAIN, vec![split.as_str(), mixed.as_str()]));
    }
    // Inside one written instance of a `multiplicity="*"` cell.
    cases.push((
        THREADS_OPTIONAL,
        vec![
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> => <o> <ov> 2 </ov> </o>) (<q> <qv> 1 </qv> </q> => <q> <qv> 2 </qv> </q>) ... </th>",
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> <q> <qv> 1 </qv> </q> => <o> <ov> 2 </ov> </o> <q> <qv> 2 </qv> </q>) ... </th>",
        ],
    ));
    cases.push((
        THREADS_OPTIONAL,
        vec![
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> => <o> <ov> 3 </ov> </o>) ... </th>",
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> => .Bag) (.Bag => <o> <ov> 3 </ov> </o>) ... </th>",
        ],
    ));
    assert_compile_alike(&cases);
}

const THREADS_OPTIONAL: &str = r#"<T> <k> 0 </k> <ts> <th multiplicity="*" type="Map"> <tid> 0 </tid> <o multiplicity="?"> <ov> 0 </ov> </o> <q multiplicity="?"> <qv> 0 </qv> </q> </th> </ts> </T>"#;

/// Ticket C1 (item 2). Completion decides which cells share an instance of their parent from the
/// cell structure the rule writes, which both sides of every rewrite share; it never reads the
/// direction of a rewrite. Swapping the sides of every rewrite of a rule therefore swaps them in
/// the compiled rule, and changes nothing else (the cells here are leaves or complete on every
/// side, so no side needs an initializer).
#[test]
#[ignore = "reproduces FOLLOWUPS: Cell separation compares only each rewrite's left side"]
fn completion_commutes_with_mirroring_every_rewrite() {
    let items = [
        "<o> <ov> 1 </ov> </o>",
        "<q> <qv> 1 </qv> </q>",
        "<tid> 7 </tid>",
        "(.Bag => <o> <ov> 2 </ov> </o>)",
        "(<o> <ov> 2 </ov> </o> => .Bag)",
        "(.Bag => <q> <qv> 2 </qv> </q>)",
        "(<o> <ov> 3 </ov> </o> => <o> <ov> 4 </ov> </o>)",
        "(<tid> 1 </tid> => <tid> 2 </tid>)",
    ];
    let mirror_source = |rule: &str| {
        // Every rewrite above is written `(L => R)` with no nested parentheses.
        let mut output = String::new();
        let mut rest = rule;
        while let Some(start) = rest.find('(') {
            output.push_str(&rest[..start]);
            let end = start + rest[start..].find(')').unwrap();
            let (left, right) = rest[start + 1..end].split_once(" => ").unwrap();
            output.push_str(&format!("({right} => {left})"));
            rest = &rest[end + 1..];
        }
        output.push_str(rest);
        output
    };
    let mut failures = Vec::new();
    // Stepback anchor: the rule of item 2 compiles (two `<th>`: one cannot hold two `<o>` on the
    // right), so that rejecting it and its mirror alike does not pass.
    let anchor = "<o> <ov> 1 </ov> </o> (.Bag => <o> <ov> 2 </ov> </o>)";
    if let Err(errors) = completed(THREADS_OPTIONAL, anchor) {
        failures.push(format!("\n  {anchor}\n    -> rejected: {errors:?}"));
    }
    for first in 0..items.len() {
        for second in first + 1..items.len() {
            let rule = format!("{} {}", items[first], items[second]);
            let mirror = mirror_source(&rule);
            let direct = completed(THREADS_OPTIONAL, &rule).map(|body| canonical(&mirrored(&body)));
            let swapped = outcome(THREADS_OPTIONAL, &mirror);
            let alike = match (&direct, &swapped) {
                (Ok(direct), Ok(swapped)) => direct == swapped,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            if !alike {
                failures.push(format!(
                    "\n  {rule}\n    mirrored -> {direct:?}\n  {mirror}\n    -> {swapped:?}"
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} rules compile unlike their mirror:{}",
        failures.len(),
        failures.join("")
    );
}

/// Ticket C1 (item 1, residual). A `Bag` variable written beside a cell body's `...` and used
/// nowhere else stands, with the frame, for the children the body does not write: every split of
/// those children between the variable and the frame gives the same rule, which is the rule
/// without the variable. Writing it must not change the compiled rule.
#[test]
#[ignore = "reproduces FOLLOWUPS: Cells: a `Bag` variable silently leaves the compiled rule (residual over-rejection)"]
fn a_bag_variable_beside_the_frame_names_part_of_the_frame() {
    assert_compile_alike(&[
        (
            PLAIN,
            vec![
                "<a> <y> Y </y> ... </a>",
                "<a> <y> Y </y> B:Bag ... </a>",
                "<a> B:Bag <y> Y </y> ... </a>",
            ],
        ),
        (
            PLAIN,
            vec![
                "<a> <y> Y </y> <z> Z </z> ... </a>",
                "<a> <y> Y </y> <z> Z </z> B:Bag ... </a>",
                "<a> <y> Y </y> <z> Z </z> B:Bag </a>",
            ],
        ),
    ]);
}

const LIST_IN_P: &str = r#"<T> <k> 0 </k> <a> <x> 0 </x> <z> 0 </z> <p> <y> 0 </y> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </p> </a> </T>"#;
const MAP_IN_P: &str = r#"<T> <k> 0 </k> <a> <x> 0 </x> <p> <y> 0 </y> <r multiplicity="*" type="Map"> <rid> 0 </rid> <d> 0 </d> <e> 0 </e> </r> </p> </a> </T>"#;

/// Ticket C1 (item "holder-side unknown items"). A cell written beside the only cell that can
/// hold it denotes the same rule as the cell written inside it. A `Bag` variable in the holder
/// stands only for the holder's children that no written cell occupies; when the written cells
/// occupy them all, it can hold no instance of a list below them.
#[test]
#[ignore = "reproduces FOLLOWUPS: Cells: conservative over-rejections (holder-side unknown items)"]
fn a_cell_beside_its_only_holder_compiles_as_written_inside_it_despite_a_bag_variable() {
    assert_compile_alike(&[
        (
            LIST_IN_P,
            vec![
                "<a> <x> X </x> <z> Z </z> <p> <y> Y </y> <fr> <v> 2 </v> </fr> ... </p> B2:Bag ... </a>",
                "<a> <x> X </x> <z> Z </z> <p> <y> Y </y> ... </p> B2:Bag ... </a> <fr> <v> 2 </v> </fr>",
            ],
        ),
        (
            LIST_IN_P,
            vec![
                "<a> <x> X </x> <z> Z </z> <p> <y> Y </y> (<fr> <v> 2 </v> </fr> => .Bag) ... </p> B2:Bag ... </a>",
                "<a> <x> X </x> <z> Z </z> <p> <y> Y </y> ... </p> B2:Bag ... </a> (<fr> <v> 2 </v> </fr> => .Bag)",
            ],
        ),
        (
            MAP_IN_P,
            vec![
                "<a> <x> X </x> <p> <y> 1 </y> <d> 5 => 6 </d> ... </p> B2:Bag ... </a>",
                "<a> <x> X </x> <p> <y> 1 </y> ... </p> B2:Bag ... </a> <d> 5 => 6 </d>",
            ],
        ),
    ]);
}

/// Ticket C1 (item "`#as` of cells in a bag"). An alias names the term it is written around; the
/// rule without the name is the same rule with one variable less. Completing the aliased rule
/// and then removing the alias gives the completion of the rule written without it.
#[test]
#[ignore = "reproduces FOLLOWUPS: Cells: conservative over-rejections (#as alias of cells in a bag)"]
fn an_alias_of_a_cell_does_not_change_its_completion() {
    const THREADS: &str = r#"<T> <k> 0 </k> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <env> 0 </env> </thread> </threads> </T>"#;
    let mut failures = Vec::new();
    for (configuration, aliased, plain) in [
        (
            PLAIN,
            "<a> (<y> Y </y> #as YC) ... </a>",
            "<a> <y> Y </y> ... </a>",
        ),
        (
            PLAIN,
            "<a> (<y> Y </y> #as YC) <z> Z </z> ... </a>",
            "<a> <y> Y </y> <z> Z </z> ... </a>",
        ),
        (
            THREADS,
            "<threads> (<thread> <id> 1 </id> ... </thread> #as TC) ... </threads>",
            "<threads> <thread> <id> 1 </id> ... </thread> ... </threads>",
        ),
    ] {
        let aliased_outcome =
            completed(configuration, aliased).map(|body| canonical(&without_aliases(&body)));
        let plain_outcome = outcome(configuration, plain);
        if aliased_outcome.is_err() || aliased_outcome != plain_outcome {
            failures.push(format!(
                "\n  {aliased}\n    -> {aliased_outcome:?}\n  {plain}\n    -> {plain_outcome:?}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join(""));
}

const THREADS_MAP: &str = r#"<T> <k> 0 </k> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <env> 0 </env> </thread> </threads> </T>"#;
const REPEATED_BELOW_A: &str = r#"<T> <k> 0 </k> <A> <x> 0 </x> <R multiplicity="*" type="Map"> <rid> 0 </rid> <A2> <y> 0 </y> <d> 0 </d> </A2> </R> </A> </T>"#;

/// Ticket C2 (items 4, 5 "moved pair", 6). Writing a cell's omitted ancestor when the
/// configuration allows only one instance of it there, or moving a cell into the only written
/// instance of its ancestor, writes nothing new: the configuration already places the cell there.
/// The compiled rule must not depend on it, whatever completion decides about the instance of a
/// `multiplicity="*"` cell that holds the cell.
///
/// Stepback: the cases where no written instance can hold the cell (J2: a fresh instance is the
/// only reading, so they compile under every O4 option) must compile; the others, and every List
/// case (which depends on O7, the fresh List position), may be rejected alike.
#[test]
fn writing_a_uniquely_determined_ancestor_does_not_change_the_rule() {
    let threads_list = THREADS_MAP.replace(r#"type="Map""#, r#"type="List""#);
    let list_in_p = MAP_IN_P.replace(r#"type="Map""#, r#"type="List""#);
    assert_no_disagreements(&[
        // q6mu, its spelling in <threads>, q6m (O4).
        (
            THREADS_MAP,
            vec![
                "<thread> <id> 1 </id> ... </thread> <env> E => 0 </env>",
                "<threads> <thread> <id> 1 </id> ... </thread> <env> E => 0 </env> ... </threads>",
                "<threads> <thread> <id> 1 </id> ... </thread> ... </threads> <env> E => 0 </env>",
            ],
        ),
        // The List variant (q6l): O4 and O7.
        (
            threads_list.as_str(),
            vec![
                "<thread> <id> 1 </id> ... </thread> <env> E => 0 </env>",
                "<threads> <thread> <id> 1 </id> ... </thread> <env> E => 0 </env> ... </threads>",
                "<threads> <thread> <id> 1 </id> ... </thread> ... </threads> <env> E => 0 </env>",
            ],
        ),
        // q12 against its spelling in <A> (O4: the written <A2> could hold <d>).
        (
            REPEATED_BELOW_A,
            vec![
                "<A> <x> X </x> <A2> <y> 1 </y> ... </A2> <d> 5 => 6 </d> ... </A>",
                "<A> <x> X </x> ... </A> <A2> <y> 1 </y> ... </A2> <d> 5 => 6 </d>",
            ],
        ),
        // Forced, in a List (O7): the written <thread> already holds its one <env>.
        (
            threads_list.as_str(),
            vec![
                "<thread> <id> 1 </id> <env> X </env> ... </thread> <env> E => 0 </env>",
                "<threads> <thread> <id> 1 </id> <env> X </env> ... </thread> <env> E => 0 </env> ... </threads>",
                "<threads> <thread> <id> 1 </id> <env> X </env> ... </thread> ... </threads> <env> E => 0 </env>",
            ],
        ),
        // s2l against s1l (O7): no written <r>, a List <r>.
        (
            list_in_p.as_str(),
            vec![
                "<a> <x> X </x> <d> 5 => 6 </d> ... </a>",
                "<a> <x> X </x> ... </a> <d> 5 => 6 </d>",
            ],
        ),
    ]);
    assert_compile_alike(&[
        // Forced: the written <thread> already holds its one <env>.
        (
            THREADS_MAP,
            vec![
                "<thread> <id> 1 </id> <env> X </env> ... </thread> <env> E => 0 </env>",
                "<threads> <thread> <id> 1 </id> <env> X </env> ... </thread> <env> E => 0 </env> ... </threads>",
                "<threads> <thread> <id> 1 </id> <env> X </env> ... </thread> ... </threads> <env> E => 0 </env>",
            ],
        ),
        // Forced: the written <thread> is removed, and <env> is on both sides.
        (
            THREADS_MAP,
            vec![
                "<threads> (<thread> <id> 1 </id> ... </thread> => .Bag) <env> E => 0 </env> ... </threads>",
                "<threads> (<thread> <id> 1 </id> ... </thread> => .Bag) ... </threads> <env> E => 0 </env>",
            ],
        ),
        // f4w against f4: no written <r>; <d> and <e> share one (O5).
        (
            MAP_IN_P,
            vec![
                "<a> <x> X </x> <d> 5 => 6 </d> <e> 1 </e> ... </a>",
                "<a> <x> X </x> ... </a> <d> 5 => 6 </d> <e> 1 </e>",
            ],
        ),
    ]);
}

/// Ticket C2 (item 6). When completion rejects a rule because the rule does not state which
/// instance of a `multiplicity="*"` cell holds a cell written outside every instance, the message
/// names that cell and the `multiplicity="*"` cell, so the author knows what to write.
#[test]
#[ignore = "reproduces FOLLOWUPS: Cells: `*`-cell rejections give generic messages"]
fn a_rejection_for_an_unstated_instance_names_the_cell_and_the_repeated_cell() {
    let threads_list = THREADS_MAP.replace(r#"type="Map""#, r#"type="List""#);
    let list_in_p = MAP_IN_P.replace(r#"type="Map""#, r#"type="List""#);
    let mut failures = Vec::new();
    for (configuration, rule, cell, repeated) in [
        (
            THREADS_MAP,
            "<threads> <thread> <id> 1 </id> ... </thread> ... </threads> <env> E => 0 </env>",
            "<env>",
            "<thread>",
        ),
        (
            threads_list.as_str(),
            "<threads> <thread> <id> 1 </id> ... </thread> ... </threads> <env> E => 0 </env>",
            "<env>",
            "<thread>",
        ),
        (
            REPEATED_BELOW_A,
            "<A> <x> X </x> ... </A> <A2> <y> 1 </y> ... </A2> <d> 5 => 6 </d>",
            "<d>",
            "<R>",
        ),
        (
            list_in_p.as_str(),
            "<a> <x> X </x> ... </a> <d> 5 => 6 </d>",
            "<d>",
            "<r>",
        ),
    ] {
        if let Err(errors) = completed(configuration, rule)
            && !errors
                .iter()
                .any(|error| error.contains(cell) && error.contains(repeated))
        {
            failures.push(format!("\n  {rule}\n    -> {errors:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "rejections that do not name the cell and its repeated ancestor:{}",
        failures.join("")
    );
}

/// Stepback ticket C0 (not in FOLLOWUPS). Completion places the cells a rule writes and adds the
/// cells it omits; it never removes a term the rule writes. A function of sort `Bag` on the right
/// side of a rewrite in a cell body is a written term: the compiled rule keeps it, or the rule is
/// rejected with an error that names the function. On `934d29e7` `split_rewrite_side` skips it
/// (`continue`), so `(<o> … </o> => mko(2))` compiles as the removal of `<o>`, and
/// `(.Bag => mkth(2))` vanishes from the rule.
#[test]
fn completion_keeps_every_written_function_application() {
    const EXTRA: &str = "syntax Bag\n syntax Bag ::= mko(Int) [function] | mkth(Int) [function]";
    let mut failures = Vec::new();
    for (rule, function) in [
        (
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> => mko(2)) ... </th>",
            "mko",
        ),
        ("<th> <tid> 1 </tid> (.Bag => mko(2)) ... </th>", "mko"),
        ("<ts> (.Bag => mkth(2)) ... </ts>", "mkth"),
        (
            "<ts> (<th> <tid> 1 </tid> ... </th> => mkth(2)) ... </ts>",
            "mkth",
        ),
    ] {
        match completed_in(EXTRA, THREADS_OPTIONAL, rule) {
            Ok(body) => {
                let printed = canonical(&body);
                if !printed.contains(function) {
                    failures.push(format!("\n  {rule}\n    -> {printed}"));
                }
            }
            Err(errors) => {
                if !errors.iter().any(|error| error.contains(function)) {
                    failures.push(format!("\n  {rule}\n    -> {errors:?}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "compiled rules without a written function application, or rejections not naming it:{}",
        failures.join("")
    );
}

/// The variables of `term`'s left projection (`right` false) or right projection, by name.
fn projection_variables(term: &Term, right: bool, output: &mut BTreeMap<String, Option<String>>) {
    match term.unannotated() {
        Term::Variable { name, sort } => {
            output.insert(name.clone(), sort.as_ref().map(ToString::to_string));
        }
        Term::Rewrite {
            left,
            right: right_side,
        } => projection_variables(if right { right_side } else { left }, right, output),
        Term::Apply { arguments, .. } => {
            for argument in arguments {
                projection_variables(argument, right, output);
            }
        }
        Term::As { pattern, alias } => {
            projection_variables(pattern, right, output);
            projection_variables(alias, right, output);
        }
        Term::Sequence(items) => {
            for item in items {
                projection_variables(item, right, output);
            }
        }
        _ => {}
    }
}

/// Ticket C1, invariant I0 (a guard: it holds on `934d29e7`; un-ignore it with C1's first commit).
/// Completion only renames a variable that can denote nothing but cells it writes in its place: a
/// written variable of a data sort is in the compiled rule, and a written variable on both sides
/// of the rule is on both sides of the compiled rule or on neither.
#[test]
#[ignore = "guard of cells-tickets C1 (I0): passes on 934d29e7; un-ignore with C1"]
fn a_written_variable_leaves_both_sides_together_and_data_variables_stay() {
    let rules: &[(&str, &str)] = &[
        (PLAIN, "<a> <y> Y </y> <z> Z </z> <w> W </w> B:Bag </a>"),
        (PLAIN, "<a> <y> Y </y> B:Bag </a>"),
        (
            PLAIN,
            "(<a> <y> Y </y> B:Bag </a> => <a> <y> 1 </y> B:Bag </a>)",
        ),
        (PLAIN, "<a> (<y> 1 </y> B:Bag => <y> 2 </y> B:Bag) </a>"),
        (PLAIN, "<a> <y> Y </y> (B:Bag => C:Bag) </a>"),
        (
            PLAIN,
            "<a> <y> Y </y> (<z> Z </z> => <z> Z </z>) ... </a> <b> V => V </b>",
        ),
        (PLAIN, "<k> X => Y </k> <a> <y> Y </y> ... </a>"),
        (
            PLAIN,
            "<T> <k> 0 => 1 </k> <a> <y> Y </y> <z> Z </z> <w> W </w> </a> <b> B </b> </T>",
        ),
        (
            LIST_IN_P,
            "<a> <x> X </x> <z> Z </z> <p> <y> Y </y> <fr> <v> V </v> </fr> ... </p> B2:Bag </a>",
        ),
        (
            MAP_IN_P,
            "<a> <x> X </x> <d> D => 6 </d> <e> E </e> ... </a>",
        ),
        (
            THREADS_MAP,
            "<thread> <id> I </id> ... </thread> <env> E => I </env>",
        ),
        (
            THREADS_OPTIONAL,
            "<o> <ov> V </ov> </o> (<o> <ov> W </ov> </o> => .Bag)",
        ),
    ];
    let is_cell_or_bag = |sort: &Option<String>| {
        sort.as_deref().is_none_or(|sort| {
            sort == "Bag"
                || sort.ends_with("Cell")
                || sort.contains("CellMap")
                || sort.contains("CellList")
                || sort.contains("CellSet")
                || sort.contains("CellBag")
        })
    };
    let mut failures = Vec::new();
    for (configuration, rule) in rules {
        let Ok(compiled) = completed(configuration, rule) else {
            continue;
        };
        let written = written_in("", configuration, rule);
        let [
            mut written_left,
            mut written_right,
            mut compiled_left,
            mut compiled_right,
        ] = [(); 4].map(|()| BTreeMap::new());
        projection_variables(&written, false, &mut written_left);
        projection_variables(&written, true, &mut written_right);
        projection_variables(&compiled, false, &mut compiled_left);
        projection_variables(&compiled, true, &mut compiled_right);
        for (name, sort) in written_left.iter().chain(&written_right) {
            if name.starts_with('_') {
                continue;
            }
            let both = written_left.contains_key(name) && written_right.contains_key(name);
            let kept = (
                compiled_left.contains_key(name),
                compiled_right.contains_key(name),
            );
            if both && kept.0 != kept.1 {
                failures.push(format!(
                    "\n  {rule}: {name} kept on one side only ({kept:?})"
                ));
            }
            if !is_cell_or_bag(sort) && kept == (false, false) {
                failures.push(format!("\n  {rule}: data variable {name}:{sort:?} dropped"));
            }
        }
    }
    failures.dedup();
    assert!(failures.is_empty(), "{}", failures.join(""));
}

/// Ticket C1/O5 (stepback). Loose cells that fit share one instance of their parent (O5): stated
/// precisely, the instances are the classes of "can share an instance" when that relation is an
/// equivalence. Here `<o> 2 </o>` (both sides) can share with neither `(<o> 1 </o> => .Bag)` nor
/// `(.Bag => <o> 3 </o>)`, which can share with each other: two instances, one of them rewriting
/// `<o> 1 </o>` to `<o> 3 </o>`. The rule compiles like that spelling with written instances; the
/// tickets' "otherwise ambiguous" rejects it, as `934d29e7` does.
#[test]
#[ignore = "reproduces cells-stepback: grouping of loose cells as an equivalence (O5)"]
fn loose_cells_share_an_instance_exactly_as_compatibility_partitions_them() {
    assert_compile_alike(&[(
        THREADS_OPTIONAL,
        vec![
            "<th> (<o> <ov> 1 </ov> </o> => <o> <ov> 3 </ov> </o>) ... </th> <th> <o> <ov> 2 </ov> </o> ... </th>",
            "(<o> <ov> 1 </ov> </o> => .Bag) <o> <ov> 2 </ov> </o> (.Bag => <o> <ov> 3 </ov> </o>)",
        ],
    )]);
}
