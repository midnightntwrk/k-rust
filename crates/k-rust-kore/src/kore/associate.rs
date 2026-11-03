//! Association: each maximal spine of binary applications of one symbol written as the
//! associative application it is notation for.
//!
//! In KORE, `\right-assoc{}(s(a1, …, an))` is notation for `s(a1, s(a2, … s(a(n-1), an)…))`, and
//! `\left-assoc{}(s(a1, …, an))` for `s(…s(s(a1, a2), a3)…, an)`; neither is a new pattern.
//! The right spine of an application `s(x, y)` of a symbol to two arguments is the chain of
//! applications reached from it through second arguments that are themselves applications of
//! the same symbol (`Symbol` equality, sort parameters included) to two arguments; its
//! components are the first argument of each application of the chain, in order, and the
//! second argument of the last one. The left spine is the same through first arguments, its
//! components read from the innermost application outwards.
//!
//! [`associate`] replaces an application whose longer spine has three or more components by
//! the `\right-assoc` (or, when the left spine is strictly longer, the `\left-assoc`) of the
//! components of that spine, in order, and goes on in each component. A spine is never
//! rebracketed: the replacement is the notation whose expansion is the replaced application,
//! node for node, so the result denotes the same pattern by the definition of the notation
//! alone, for any symbol, and expanding every associative application it wrote gives back the
//! input exactly. No property of the symbol (associativity, commutativity, a unit) is used, and
//! none is needed. An application of two components is left as it is, since its notation
//! would be no shallower; ties go right, the shape KORE results are written in.
//!
//! What association changes is depth: a spine of n components is n - 1 levels deep and its
//! associative application one level above its deepest component, so a pass that descends once
//! per level (`k_rust_backend::nesting`) descends a length-independent number of levels through
//! it.
//!
//! Both walks keep their pending subpatterns on a work list, so they run on a fixed amount of
//! stack whatever the depth of the pattern.

use super::ast::{Associativity, Pattern, Symbol};

/// Push the direct subpatterns of `$pattern` onto `$work`, in order, through `$iter` and
/// `$deref` (`iter` and `as_ref`, or `iter_mut` and `as_mut`), allocating nothing beyond the
/// work list's own growth: both walks visit every node, so a list per node would be one
/// allocation per node of the request.
macro_rules! push_children {
    ($pattern:expr, $work:expr, $iter:ident, $deref:ident) => {
        match $pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => $work.extend(arguments.$iter()),
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => $work.push(argument.$deref()),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                $work.push(left.$deref());
                $work.push(right.$deref());
            }
            Pattern::Exists { body, .. }
            | Pattern::Forall { body, .. }
            | Pattern::Mu { body, .. }
            | Pattern::Nu { body, .. } => $work.push(body.$deref()),
            Pattern::String(_)
            | Pattern::Variable(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    };
}

/// Write each spine of three or more components of a symbol that `spine` accepts as the
/// associative application it is notation for, in place (module docs).
///
/// Each node is visited once: a spine's applications are taken apart once when it is replaced,
/// and the shorter spine of a node, walked to compare it with the longer one, is no longer than
/// the longer one, which is replaced. The work is therefore linear in the size of `pattern`.
pub fn associate(pattern: &mut Pattern, spine: impl Fn(&Symbol) -> bool) {
    let mut work = vec![pattern];
    // Invariant: `work` holds the subpatterns not yet visited, each a component of a replaced
    // spine or a child of a visited node that was not replaced; every node is pushed at most
    // once, so the loop ends after at most |pattern| pops.
    while let Some(node) = work.pop() {
        if let Some(associativity) = longer_spine(node, &spine) {
            replace_spine(node, associativity);
        }
        push_children!(node, work, iter_mut, as_mut);
    }
}

/// Whether [`associate`] would leave `pattern` as it is: no application of a symbol that
/// `spine` accepts to two arguments has a spine of three or more components. One walk, which
/// stops at the first such application.
pub fn is_associated(pattern: &Pattern, spine: impl Fn(&Symbol) -> bool) -> bool {
    let mut work = vec![pattern];
    // Invariant: `work` holds the subpatterns not yet inspected; each pop pushes only proper
    // subpatterns of the popped one, so the loop terminates.
    while let Some(node) = work.pop() {
        if let Pattern::Application { symbol, arguments } = node
            && spine(symbol)
            && let [left, right] = arguments.as_slice()
            && (binary_of(left, symbol).is_some() || binary_of(right, symbol).is_some())
        {
            return false;
        }
        push_children!(node, work, iter, as_ref);
    }
    true
}

/// The two arguments of `pattern` when it is an application of `symbol` to two arguments.
fn binary_of<'p>(pattern: &'p Pattern, symbol: &Symbol) -> Option<(&'p Pattern, &'p Pattern)> {
    match pattern {
        Pattern::Application {
            symbol: applied,
            arguments,
        } if applied == symbol => match arguments.as_slice() {
            [left, right] => Some((left, right)),
            _ => None,
        },
        _ => None,
    }
}

/// The number of components of the spine of `node`, an application of `symbol` to two
/// arguments, on the side `associativity` names.
fn components(node: &Pattern, symbol: &Symbol, associativity: Associativity) -> usize {
    let mut applications = 0;
    let mut current = node;
    // Invariant: `applications` counts the applications of the spine from `node` to `current`
    // excluded; each step moves to a proper subpattern, so the loop terminates.
    while let Some((left, right)) = binary_of(current, symbol) {
        applications += 1;
        current = match associativity {
            Associativity::Right => right,
            Associativity::Left => left,
        };
    }
    applications + 1
}

/// The side of the longer spine of `node` when `node` is an application of a symbol that
/// `spine` accepts to two arguments and that spine has three or more components; ties go right.
fn longer_spine(node: &Pattern, spine: &impl Fn(&Symbol) -> bool) -> Option<Associativity> {
    let Pattern::Application { symbol, arguments } = node else {
        return None;
    };
    if arguments.len() != 2 || !spine(symbol) {
        return None;
    }
    let right = components(node, symbol, Associativity::Right);
    let left = components(node, symbol, Associativity::Left);
    if right.max(left) < 3 {
        None
    } else if right >= left {
        Some(Associativity::Right)
    } else {
        Some(Associativity::Left)
    }
}

/// Replace `node`, an application of a symbol to two arguments, by the associative application
/// of the components of its spine on the side `associativity` names, in order.
fn replace_spine(node: &mut Pattern, associativity: Associativity) {
    let Pattern::Application { symbol, arguments } = node else {
        unreachable!("only an application has a spine");
    };
    let symbol = std::mem::replace(
        symbol,
        Symbol {
            name: String::new(),
            sort_parameters: Vec::new(),
        },
    );
    let mut components = Vec::new();
    let mut current = std::mem::take(arguments);
    // Invariant: `components` holds, in the order the spine is walked, the components of the
    // applications taken apart so far, and `current` the two arguments of the next one; each
    // step takes apart one application of the spine, whose emptied node is dropped at once.
    loop {
        let [left, right] =
            <[Pattern; 2]>::try_from(current).expect("a spine application has two arguments");
        let (component, mut next) = match associativity {
            Associativity::Right => (left, right),
            Associativity::Left => (right, left),
        };
        components.push(component);
        match &mut next {
            Pattern::Application {
                symbol: applied,
                arguments,
            } if *applied == symbol && arguments.len() == 2 => {
                current = std::mem::take(arguments);
            }
            _ => {
                components.push(next);
                break;
            }
        }
    }
    if associativity == Associativity::Left {
        components.reverse();
    }
    *node = Pattern::AssociativeApplication {
        associativity,
        symbol,
        arguments: components,
    };
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::super::{normalize, parser::parse_pattern, printer::Printer};
    use super::*;

    /// The symbols the tests' predicate accepts: `s` and `t` at any sort parameters, not `u`.
    fn accepted(symbol: &Symbol) -> bool {
        symbol.name == "s" || symbol.name == "t"
    }

    fn pattern(source: &str) -> Pattern {
        parse_pattern(source).expect("the test pattern parses")
    }

    /// `source` associated, with the checks every case shares: the result is associated, a
    /// second association leaves it as it is, and with every associative application expanded
    /// by the normalizer's own reading, it prints as the input does.
    fn associated(source: &str) -> Pattern {
        let input = pattern(source);
        let mut result = input.clone();
        associate(&mut result, accepted);
        assert!(is_associated(&result, accepted), "{source}");
        let mut again = result.clone();
        associate(&mut again, accepted);
        assert_eq!(again, result, "association is idempotent: {source}");
        let printer = Printer::compact();
        assert_eq!(
            printer.print_pattern(&normalize::for_kast(&result)),
            printer.print_pattern(&normalize::for_kast(&input)),
            "the expansion of the associated form is the input: {source}"
        );
        result
    }

    fn assert_associates(source: &str, expected: &str) {
        assert_eq!(associated(source), pattern(expected), "{source}");
    }

    fn assert_unchanged(source: &str) {
        assert_eq!(associated(source), pattern(source), "{source}");
        assert!(is_associated(&pattern(source), accepted), "{source}");
    }

    #[test]
    fn associate_writes_a_right_spine_as_its_right_associative_application() {
        assert_associates(
            "s{}(a{}(), s{}(b{}(), s{}(c{}(), d{}())))",
            r"\right-assoc{}(s{}(a{}(), b{}(), c{}(), d{}()))",
        );
        assert!(!is_associated(
            &pattern("s{}(a{}(), s{}(b{}(), c{}()))"),
            accepted
        ));
    }

    #[test]
    fn associate_writes_a_left_spine_as_its_left_associative_application() {
        assert_associates(
            "s{}(s{}(s{}(a{}(), b{}()), c{}()), d{}())",
            r"\left-assoc{}(s{}(a{}(), b{}(), c{}(), d{}()))",
        );
        assert!(!is_associated(
            &pattern("s{}(s{}(a{}(), b{}()), c{}())"),
            accepted
        ));
    }

    #[test]
    fn associate_takes_the_longer_spine_of_a_mixed_one_and_keeps_its_components() {
        assert_associates(
            "s{}(a{}(), s{}(s{}(b{}(), c{}()), d{}()))",
            r"\right-assoc{}(s{}(a{}(), s{}(b{}(), c{}()), d{}()))",
        );
        // Both spines have three components; ties go right, and the left component is an
        // application of two components, left as it is.
        assert_associates(
            "s{}(s{}(a{}(), b{}()), s{}(c{}(), d{}()))",
            r"\right-assoc{}(s{}(s{}(a{}(), b{}()), c{}(), d{}()))",
        );
        // The left spine is longer; its components include the right one's root.
        assert_associates(
            "s{}(s{}(s{}(a{}(), b{}()), c{}()), s{}(d{}(), e{}()))",
            r"\left-assoc{}(s{}(a{}(), b{}(), c{}(), s{}(d{}(), e{}())))",
        );
        // A component that is a spine of the other side is associated in turn.
        assert_associates(
            "s{}(s{}(s{}(a{}(), b{}()), c{}()), s{}(d{}(), s{}(e{}(), s{}(f{}(), g{}()))))",
            r"\right-assoc{}(s{}(\left-assoc{}(s{}(a{}(), b{}(), c{}())), d{}(), e{}(), f{}(), g{}()))",
        );
    }

    #[test]
    fn associate_rewrites_spines_under_other_constructs() {
        assert_associates(
            r"\and{S{}}(f{}(s{}(a{}(), s{}(b{}(), c{}()))), \not{S{}}(\exists{S{}}(X:S{}, \equals{S{}, S{}}(X:S{}, s{}(s{}(a{}(), b{}()), c{}())))))",
            r"\and{S{}}(f{}(\right-assoc{}(s{}(a{}(), b{}(), c{}()))), \not{S{}}(\exists{S{}}(X:S{}, \equals{S{}, S{}}(X:S{}, \left-assoc{}(s{}(a{}(), b{}(), c{}()))))))",
        );
        // An associative application already written is kept, and its arguments are associated.
        assert_associates(
            r"\left-assoc{}(f{}(a{}(), s{}(b{}(), s{}(c{}(), d{}()))))",
            r"\left-assoc{}(f{}(a{}(), \right-assoc{}(s{}(b{}(), c{}(), d{}()))))",
        );
    }

    #[test]
    fn associate_keeps_spines_of_different_symbols_apart() {
        assert_associates(
            "s{}(a{}(), s{}(t{}(b{}(), t{}(c{}(), d{}())), e{}()))",
            r"\right-assoc{}(s{}(a{}(), \right-assoc{}(t{}(b{}(), c{}(), d{}())), e{}()))",
        );
        // The same name at other sort parameters is another symbol.
        assert_associates(
            "s{A{}}(a{}(), s{B{}}(b{}(), s{B{}}(c{}(), d{}())))",
            r"s{A{}}(a{}(), \right-assoc{}(s{B{}}(b{}(), c{}(), d{}())))",
        );
        assert_unchanged("s{}(a{}(), t{}(b{}(), s{}(c{}(), d{}())))");
    }

    #[test]
    fn associate_leaves_an_application_of_two_components_as_it_is() {
        assert_unchanged("s{}(a{}(), b{}())");
        assert_unchanged("s{}(a{}(), f{}(s{}(b{}(), c{}())))");
        // Only binary applications form a spine.
        assert_unchanged("s{}(a{}(), s{}(b{}(), c{}(), d{}()))");
        assert_unchanged("s{}(a{}(), s{}(b{}()))");
    }

    #[test]
    fn associate_leaves_a_spine_of_a_refused_symbol_as_it_is() {
        assert_unchanged("u{}(a{}(), u{}(b{}(), u{}(c{}(), d{}())))");
        assert_unchanged("u{}(u{}(u{}(a{}(), b{}()), c{}()), d{}())");
    }

    /// A spine of a million components associates on an 8 MiB thread, as does its check, and
    /// the result keeps the components in order.
    #[test]
    fn associate_writes_a_million_component_spine_on_an_8_mib_thread() {
        const COMPONENTS: usize = 1_000_000;
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(|| {
                let symbol = Symbol {
                    name: "s".into(),
                    sort_parameters: Vec::new(),
                };
                let leaf = |index: usize| Pattern::DomainValue {
                    sort: crate::kore::ast::Sort::Application {
                        name: "S".into(),
                        arguments: Vec::new(),
                    },
                    value: index.to_string().into(),
                };
                let mut spine = leaf(COMPONENTS - 1);
                for index in (0..COMPONENTS - 1).rev() {
                    spine = Pattern::Application {
                        symbol: symbol.clone(),
                        arguments: vec![leaf(index), spine],
                    };
                }
                assert!(!is_associated(&spine, accepted));
                let mut associated = spine.clone();
                associate(&mut associated, accepted);
                assert!(is_associated(&associated, accepted));
                let Pattern::AssociativeApplication {
                    associativity: Associativity::Right,
                    symbol: applied,
                    arguments,
                } = &associated
                else {
                    panic!("the spine is written as its right-associative application");
                };
                assert_eq!(*applied, symbol);
                assert_eq!(arguments.len(), COMPONENTS);
                assert!(
                    arguments
                        .iter()
                        .enumerate()
                        .all(|(index, argument)| *argument == leaf(index))
                );
                assert_eq!(normalize::for_kast(&associated), spine);
            })
            .expect("the worker spawns")
            .join()
            .expect("the worker finishes");
    }

    /// Binary trees of `s`, `t` and `u` over constants, of either symbol at each node.
    fn trees() -> impl Strategy<Value = Pattern> {
        let leaf =
            prop_oneof![Just("a"), Just("b"), Just("c")].prop_map(|name| Pattern::Application {
                symbol: Symbol {
                    name: name.into(),
                    sort_parameters: Vec::new(),
                },
                arguments: Vec::new(),
            });
        leaf.prop_recursive(8, 64, 2, |inner| {
            (
                prop_oneof![Just("s"), Just("t"), Just("u")],
                inner.clone(),
                inner,
            )
                .prop_map(|(name, left, right)| Pattern::Application {
                    symbol: Symbol {
                        name: name.into(),
                        sort_parameters: Vec::new(),
                    },
                    arguments: vec![left, right],
                })
        })
    }

    proptest! {
        /// On any tree, association leaves no spine of three components, is idempotent, and its
        /// result expands to the input.
        #[test]
        fn associate_preserves_the_expansion_of_any_tree(tree in trees()) {
            let mut result = tree.clone();
            associate(&mut result, accepted);
            prop_assert!(is_associated(&result, accepted));
            prop_assert_eq!(normalize::for_kast(&result), tree.clone());
            let mut again = result.clone();
            associate(&mut again, accepted);
            prop_assert_eq!(&again, &result);
            prop_assert_eq!(is_associated(&tree, accepted), result == tree);
        }
    }
}
