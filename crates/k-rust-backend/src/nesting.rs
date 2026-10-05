//! Stack admission for the backend's recursive passes over KORE patterns and definitions.
//!
//! Standalone verification, alias expansion, and internalization each descend once per level of
//! the pattern they read, and the helpers they call at a level rescan the levels below it the
//! same way; loading a definition runs these and further passes over its sentences. Their stack
//! therefore grows linearly with the nesting depth of the patterns and sorts they read, and a
//! pattern or module read from a client can be of any depth. Overflowing the native stack aborts
//! the whole process, which on a persistent host ends every other request it serves.
//!
//! Before those passes run, [`ensure_stack`] for a pattern and [`ensure_definition_stack`] for
//! the modules of a definition measure the nesting depth with explicit work lists and compare
//! the stack the passes need for it with what is left on the current thread. Input that does not
//! fit is refused with [`DefinitionError::InsufficientStack`], an ordinary error, whether or not
//! it is otherwise well formed. The bound is the thread's stack, not a fixed depth: the same
//! pattern is admitted on a thread with more stack.
//!
//! Alias expansion descends through the bodies of the aliases it unfolds, each below the ones
//! that apply it, so how deep it goes is known only as it proceeds; it admits each alias body
//! with [`ensure_depth_stack`] where it enters it, both when a definition is loaded and when a
//! request is internalized.
//!
//! The remaining stack is unknown on wasm32, where the engine's call-stack limit is invisible to
//! the module, and on a native thread whose bounds cannot be read; there every pattern is
//! admitted and the passes stay bounded by the stack, as the simplifier's own guard is
//! (`stop::remaining_stack`).

use k_rust_kore::kore::ast as kore;

use crate::definition::DefinitionError;
use crate::stop::{STACK_RED_ZONE, remaining_stack};

/// Upper bound on the native stack that verification, alias expansion, internalization, and the
/// loading of a definition take per level of the patterns and sorts they read.
///
/// Measured by painting the stack below the caller and running each admitted internalization
/// entry point on chains of every pattern constructor, on mixed chains, and on deep sorts: the
/// deepest level took 19,184 bytes in a debug build and 2,192 bytes in a release build, both at
/// an `\and` or `\or` level. The release bound keeps a wider margin because inlining, including
/// link-time inlining in the `dist` profile, moves frame sizes more than the unoptimized build
/// does. The fixed cost below the first level, at most 62 KiB in a debug build, is within
/// `STACK_RED_ZONE`, which also holds the non-recursive work done at the deepest level.
/// `tests::admitted_depths_fit_on_the_thread` and
/// `tests::admitted_definition_depths_fit_on_the_thread` run every measured pattern shape and
/// deep definition at the deepest depth this bound admits on a small thread.
#[cfg(debug_assertions)]
const STACK_PER_LEVEL: usize = 24 * 1024;
#[cfg(not(debug_assertions))]
const STACK_PER_LEVEL: usize = 4 * 1024;

/// Refuse `pattern` with [`DefinitionError::InsufficientStack`] when the current thread's
/// remaining stack, if known, cannot hold the recursive passes over a pattern of its nesting
/// depth.
pub(crate) fn ensure_stack(pattern: &kore::Pattern) -> Result<(), DefinitionError> {
    ensure_stack_with(|| nesting_depth(pattern))
}

/// Refuse the `modules` of a definition with [`DefinitionError::InsufficientStack`] when the
/// current thread's remaining stack, if known, cannot hold the recursive passes over their
/// deepest pattern or sort: the patterns of their sentences and attributes, and the sorts of
/// their declarations.
pub(crate) fn ensure_definition_stack(modules: &[&kore::Module]) -> Result<(), DefinitionError> {
    ensure_stack_with(|| {
        let attributes = |attributes: &kore::Attributes| {
            attributes.0.iter().map(nesting_depth).max().unwrap_or(0)
        };
        let sorts = |sorts: &[kore::Sort]| sorts.iter().map(sort_depth).max().unwrap_or(0);
        let mut deepest = 0;
        for module in modules {
            deepest = deepest.max(attributes(&module.attributes));
            for sentence in &module.sentences {
                let depth = match sentence {
                    kore::Sentence::Import {
                        attributes: own, ..
                    }
                    | kore::Sentence::SortDeclaration {
                        attributes: own, ..
                    } => attributes(own),
                    kore::Sentence::SymbolDeclaration {
                        symbol,
                        argument_sorts,
                        result_sort,
                        attributes: own,
                        ..
                    } => attributes(own)
                        .max(sorts(&symbol.sort_parameters))
                        .max(sorts(argument_sorts))
                        .max(sort_depth(result_sort)),
                    kore::Sentence::AliasDeclaration {
                        alias,
                        argument_sorts,
                        result_sort,
                        left,
                        right,
                        attributes: own,
                    } => attributes(own)
                        .max(sorts(&alias.sort_parameters))
                        .max(sorts(argument_sorts))
                        .max(sort_depth(result_sort))
                        .max(nesting_depth(left))
                        .max(nesting_depth(right)),
                    kore::Sentence::Axiom {
                        pattern,
                        attributes: own,
                        ..
                    }
                    | kore::Sentence::Claim {
                        pattern,
                        attributes: own,
                        ..
                    } => attributes(own).max(nesting_depth(pattern)),
                };
                deepest = deepest.max(depth);
            }
        }
        deepest
    })
}

/// Refuse with [`DefinitionError::InsufficientStack`] when the current thread's remaining stack,
/// if known, cannot hold the recursive passes over a pattern `depth` levels deep, such as an
/// alias body about to be unfolded at the current point of an unfolding.
pub(crate) fn ensure_depth_stack(depth: usize) -> Result<(), DefinitionError> {
    ensure_stack_with(|| depth)
}

fn ensure_stack_with(depth: impl FnOnce() -> usize) -> Result<(), DefinitionError> {
    let Some(remaining) = remaining_stack() else {
        return Ok(());
    };
    let depth = depth();
    let required = depth
        .saturating_mul(STACK_PER_LEVEL)
        .saturating_add(STACK_RED_ZONE);
    if required <= remaining {
        Ok(())
    } else {
        Err(DefinitionError::InsufficientStack {
            depth,
            required,
            remaining,
        })
    }
}

/// The number of nodes on the longest path from `pattern` to a leaf, counting a sort's nodes
/// below the pattern node that carries it, computed without recursion.
///
/// An associative application of `n` arguments counts as `n` levels above its arguments, since
/// it stands for a chain of `n - 1` binary applications.
pub(crate) fn nesting_depth(pattern: &kore::Pattern) -> usize {
    use kore::Pattern;

    let mut deepest = 0;
    let mut sorts: Vec<&kore::Sort> = Vec::new();
    let mut pending = vec![(pattern, 1_usize)];
    // Each pop pushes only proper subpatterns of the popped one, so the loop terminates.
    // Invariant: `deepest` is the greatest depth found among the nodes popped so far.
    while let Some((pattern, depth)) = pending.pop() {
        let mut below = depth.saturating_add(1);
        let children: &[Pattern] = match pattern {
            Pattern::String(_) => &[],
            Pattern::Variable(variable) => {
                sorts.push(&variable.sort);
                &[]
            }
            Pattern::Application { symbol, arguments } => {
                sorts.extend(&symbol.sort_parameters);
                arguments
            }
            Pattern::AssociativeApplication {
                symbol, arguments, ..
            } => {
                sorts.extend(&symbol.sort_parameters);
                below = depth.saturating_add(arguments.len());
                arguments
            }
            Pattern::Top { sort }
            | Pattern::Bottom { sort }
            | Pattern::DomainValue { sort, .. } => {
                sorts.push(sort);
                &[]
            }
            Pattern::And { sort, arguments } | Pattern::Or { sort, arguments } => {
                sorts.push(sort);
                arguments
            }
            Pattern::Not { sort, argument } | Pattern::Next { sort, argument } => {
                sorts.push(sort);
                std::slice::from_ref(&**argument)
            }
            Pattern::Implies { sort, left, right }
            | Pattern::Iff { sort, left, right }
            | Pattern::Rewrites { sort, left, right } => {
                sorts.push(sort);
                pending.push((left, below));
                std::slice::from_ref(&**right)
            }
            Pattern::Exists {
                sort,
                variable,
                body,
            }
            | Pattern::Forall {
                sort,
                variable,
                body,
            } => {
                sorts.push(sort);
                sorts.push(&variable.sort);
                std::slice::from_ref(&**body)
            }
            Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                sorts.push(&variable.sort);
                std::slice::from_ref(&**body)
            }
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            }
            | Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => {
                sorts.push(operand_sort);
                sorts.push(result_sort);
                std::slice::from_ref(&**argument)
            }
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            }
            | Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => {
                sorts.push(operand_sort);
                sorts.push(result_sort);
                pending.push((left, below));
                std::slice::from_ref(&**right)
            }
        };
        deepest = deepest.max(depth);
        for sort in sorts.drain(..) {
            deepest = deepest.max(depth.saturating_add(sort_depth(sort)));
        }
        pending.extend(children.iter().map(|child| (child, below)));
    }
    deepest
}

/// The number of nodes on the longest path from `sort` to a leaf, computed without recursion.
fn sort_depth(sort: &kore::Sort) -> usize {
    let mut deepest = 0;
    let mut pending = vec![(sort, 1_usize)];
    // Each pop pushes only proper subsorts of the popped one, so the loop terminates.
    // Invariant: `deepest` is the greatest depth found among the sorts popped so far.
    while let Some((sort, depth)) = pending.pop() {
        deepest = deepest.max(depth);
        if let kore::Sort::Application { arguments, .. } = sort {
            pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
        }
    }
    deepest
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::definition::BackendDefinition;

    const DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            sort SortT{} []
            sort SortL{A} []
            symbol a{}() : SortS{} [constructor{}(), functional{}()]
            symbol wrap{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            symbol wrapT{}(SortT{}) : SortS{} [constructor{}(), functional{}()]
            symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
            axiom{R} \exists{R}(Value:SortT{},
                \equals{SortT{}, R}(Value:SortT{}, inj{SortS{}, SortT{}}(From:SortS{})))
                [subsort{SortS{}, SortT{}}()]
            alias same{}(SortS{}) : SortS{} where same{}(X:SortS{}) := X:SortS{} []
            alias twice{}(SortS{}) : SortS{} where twice{}(X:SortS{}) := wrap{}(wrap{}(X:SortS{})) []
        endmodule []"#;

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(DEFINITION).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// `prefix` `count` times, then `leaf`, then `suffix` `count` times.
    fn chain(count: usize, prefix: &str, leaf: &str, suffix: &str) -> String {
        let mut text = prefix.repeat(count);
        text.push_str(leaf);
        text.push_str(&suffix.repeat(count));
        text
    }

    /// The patterns whose stack per level `STACK_PER_LEVEL` was measured on: a chain of each
    /// constructor, mixed chains, a deep sort, and alias chains, about `levels` levels deep.
    fn shapes(levels: usize) -> Vec<(&'static str, String)> {
        let constrained = |predicate: String| format!(r"\and{{SortS{{}}}}(a{{}}(), {predicate})");
        let predicate = |prefix: &str, leaf: &str| constrained(chain(levels, prefix, leaf, ")"));
        let top = r"\top{SortS{}}()";
        let half = levels / 2;
        let deep_sort = chain(levels, "SortL{", "SortS{}", "}");
        vec![
            ("application", chain(levels, "wrap{}(", "a{}()", ")")),
            ("alias", chain(levels, "same{}(", "a{}()", ")")),
            ("expanding alias", chain(levels, "twice{}(", "a{}()", ")")),
            (
                "injection",
                chain(half, "wrapT{}(inj{SortS{}, SortT{}}(", "a{}()", "))"),
            ),
            (
                "term conjunction",
                chain(levels, r"\and{SortS{}}(a{}(), ", "a{}()", ")"),
            ),
            (
                "term disjunction",
                chain(levels, r"\or{SortS{}}(a{}(), ", "a{}()", ")"),
            ),
            (
                "term existential",
                chain(
                    levels,
                    r"\exists{SortS{}}(X:SortS{}, ",
                    "wrap{}(X:SortS{})",
                    ")",
                ),
            ),
            (
                "sort",
                constrained(format!(r"\ceil{{{deep_sort}, SortS{{}}}}(V:{deep_sort})")),
            ),
            ("not", predicate(r"\not{SortS{}}(", top)),
            ("ceil", predicate(r"\ceil{SortS{}, SortS{}}(", top)),
            ("floor", predicate(r"\floor{SortS{}, SortS{}}(", top)),
            (
                "equals",
                predicate(r"\equals{SortS{}, SortS{}}(\top{SortS{}}(), ", top),
            ),
            (
                "in",
                predicate(r"\in{SortS{}, SortS{}}(\top{SortS{}}(), ", top),
            ),
            (
                "implies",
                predicate(r"\implies{SortS{}}(\top{SortS{}}(), ", top),
            ),
            ("iff", predicate(r"\iff{SortS{}}(\top{SortS{}}(), ", top)),
            ("or", predicate(r"\or{SortS{}}(\bottom{SortS{}}(), ", top)),
            ("and", predicate(r"\and{SortS{}}(\top{SortS{}}(), ", top)),
            (
                "exists",
                predicate(
                    r"\exists{SortS{}}(X:SortS{}, ",
                    r"\equals{SortS{}, SortS{}}(X:SortS{}, a{}())",
                ),
            ),
            (
                "forall",
                predicate(
                    r"\forall{SortS{}}(X:SortS{}, ",
                    r"\equals{SortS{}, SortS{}}(X:SortS{}, a{}())",
                ),
            ),
            ("mu", predicate(r"\mu{}(@X:SortS{}, ", "@X:SortS{}")),
            ("nu", predicate(r"\nu{}(@X:SortS{}, ", "@X:SortS{}")),
            ("next", predicate(r"\next{SortS{}}(", top)),
            (
                "rewrites",
                predicate(r"\rewrites{SortS{}}(\top{SortS{}}(), ", top),
            ),
            (
                "application over conjunction",
                chain(half, r"wrap{}(\and{SortS{}}(a{}(), ", "a{}()", "))"),
            ),
            (
                "application over constrained term",
                chain(
                    half,
                    r"wrap{}(\and{SortS{}}(\not{SortS{}}(\bottom{SortS{}}()), ",
                    "a{}()",
                    "))",
                ),
            ),
            (
                "conjunction over negation",
                constrained(chain(
                    half,
                    r"\and{SortS{}}(\top{SortS{}}(), \not{SortS{}}(",
                    top,
                    "))",
                )),
            ),
            (
                "equation over a deep term",
                constrained(format!(
                    r"\equals{{SortS{{}}, SortS{{}}}}({}, a{{}}())",
                    chain(levels, "wrap{}(", "a{}()", ")")
                )),
            ),
            (
                "existential over conjunction",
                constrained(chain(
                    half,
                    r"\exists{SortS{}}(X:SortS{}, \and{SortS{}}(\equals{SortS{}, SortS{}}(X:SortS{}, a{}()), ",
                    top,
                    "))",
                )),
            ),
            (
                "alias over application",
                chain(half, "same{}(wrap{}(", "a{}()", "))"),
            ),
            (
                "conjunction over injection",
                chain(
                    levels / 3,
                    r"\and{SortS{}}(wrapT{}(inj{SortS{}, SortT{}}(",
                    "a{}()",
                    ")), a{}())",
                ),
            ),
        ]
    }

    /// The entry points that admit a pattern read from outside the definition.
    const ENTRY_POINTS: &[&str] = &[
        "verify",
        "term",
        "pattern",
        "pattern or predicate",
        "predicate",
        "model predicate",
        "implication pattern",
        "disjunction",
    ];

    /// Run `entry` on `pattern`.
    fn run(
        definition: &BackendDefinition,
        entry: &str,
        pattern: &kore::Pattern,
    ) -> Result<(), DefinitionError> {
        let admitted = definition.admit_unverified(pattern, &[]);
        match entry {
            "verify" => definition.verify_standalone_pattern(pattern, &[]).map(drop),
            "term" => admitted.internalize_term().map(drop),
            "pattern" => admitted.internalize_pattern().map(drop),
            "pattern or predicate" => admitted.internalize_pattern_or_predicate().map(drop),
            "predicate" => admitted.internalize_predicate().map(drop),
            "model predicate" => admitted.internalize_model_predicate().map(drop),
            "implication pattern" => admitted.internalize_implication_pattern().map(drop),
            "disjunction" => admitted.internalize_disjunction().map(drop),
            _ => unreachable!("unknown entry point {entry}"),
        }
    }

    /// Whether `outcome` refuses the pattern for want of stack. An implication side is first
    /// checked for alias applications, without recursion, so an alias chain is rejected there
    /// before any stack is needed.
    fn refused(entry: &str, outcome: Result<(), DefinitionError>) -> bool {
        match outcome {
            Err(DefinitionError::InsufficientStack {
                depth,
                required,
                remaining,
            }) => {
                assert!(required > remaining, "{entry}: {depth} levels");
                true
            }
            Err(DefinitionError::MacroOrAliasInImplication(_)) => {
                assert_eq!(entry, "implication pattern");
                true
            }
            Ok(()) | Err(_) => false,
        }
    }

    fn on_stack(bytes: usize, work: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(bytes)
            .spawn(work)
            .expect("worker should spawn")
            .join()
            .expect("worker should finish");
    }

    #[test]
    fn nesting_depth_counts_patterns_sorts_and_associative_chains() {
        let depth = |source: &str| nesting_depth(&parse_pattern(source).unwrap());
        assert_eq!(depth("a{}()"), 1);
        assert_eq!(depth("X:SortS{}"), 2);
        assert_eq!(depth(r"\top{SortL{SortL{SortS{}}}}()"), 4);
        assert_eq!(depth("wrap{}(wrap{}(a{}()))"), 3);
        assert_eq!(
            depth(r#"\and{SortS{}}(a{}(), wrap{}(\dv{SortS{}}("1")))"#),
            4
        );
        assert_eq!(
            depth(r"\implies{SortS{}}(wrap{}(wrap{}(a{}())), \top{SortS{}}())"),
            4
        );
        assert_eq!(
            depth(r"\exists{SortS{}}(X:SortL{SortL{SortS{}}}, a{}())"),
            4
        );
        assert_eq!(depth(r"\left-assoc{}(c{}(a{}(), wrap{}(a{}()), a{}()))"), 5);
    }

    /// Every shape the bound was measured on, at the deepest depth that each entry point admits
    /// on a thread sized for about 160 levels, runs to completion; a pattern one level deeper is
    /// refused. A shape whose passes outgrew `STACK_PER_LEVEL` overflows here and aborts the
    /// test binary. The thread has under 4 MiB of stack, and the patterns take a few MB of heap.
    #[test]
    fn admitted_depths_fit_on_the_thread() {
        const STACK: usize = STACK_RED_ZONE + 160 * STACK_PER_LEVEL;
        on_stack(STACK, || {
            let definition = definition();
            let most = STACK / STACK_PER_LEVEL + 1;
            let refused_at = |shape: usize, entry: &str, levels: usize| {
                let (_, source) = shapes(levels).swap_remove(shape);
                let pattern = parse_pattern(&source).expect("shape should parse");
                refused(entry, run(&definition, entry, &pattern))
            };
            for (shape, (name, _)) in shapes(2).into_iter().enumerate() {
                for entry in ENTRY_POINTS {
                    if *entry == "implication pattern" && name.contains("alias") {
                        continue;
                    }
                    assert!(
                        refused_at(shape, entry, most),
                        "{name} at {most} levels is admitted by {entry}"
                    );
                    // Invariant: `low` is admitted, or 0, and `high` is refused.
                    let (mut low, mut high) = (0, most);
                    while high - low > 1 {
                        let middle = low + (high - low) / 2;
                        if refused_at(shape, entry, middle) {
                            high = middle;
                        } else {
                            low = middle;
                        }
                    }
                    assert!(low > 2, "{name} is refused by {entry} at {high} levels");
                }
            }
        });
    }

    /// Definitions whose sentences are about `levels` levels deep: rules, equations and claims
    /// over deep terms and conditions, a deep alias body, a deep attribute, and a deep sort.
    fn deep_definitions(levels: usize) -> Vec<(&'static str, String)> {
        let term = |leaf: &str| chain(levels, "wrap{}(", leaf, ")");
        let deep_sort = chain(levels, "SortL{", "SortS{}", "}");
        let condition = chain(levels, r"\not{R}(", r"\bottom{R}()", ")");
        let module = |sentences: String| {
            format!(
                r#"[]
                module MAIN
                    sort SortS{{}} []
                    sort SortL{{A}} []
                    symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                    symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                    symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                    {sentences}
                endmodule []"#
            )
        };
        let rewrite = |left: &str, right: &str| {
            format!(
                r#"axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({left}, \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}())
                ) [label{{}}("rule")]"#
            )
        };
        let equation = |requires: &str, right: &str| {
            format!(
                r#"axiom{{R}} \implies{{R}}(
                    {requires},
                    \equals{{SortS{{}}, R}}(f{{}}(X:SortS{{}}), \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}()))
                ) [label{{}}("equation"), simplification{{}}()]"#
            )
        };
        vec![
            (
                "rule left side",
                module(rewrite(&term("X:SortS{}"), "a{}()")),
            ),
            (
                "rule right side",
                module(rewrite("X:SortS{}", &term("X:SortS{}"))),
            ),
            (
                "equation right side",
                module(equation(r"\top{R}()", &term("X:SortS{}"))),
            ),
            (
                "equation condition",
                module(equation(
                    &format!(r"\and{{R}}({condition}, \top{{R}}())"),
                    "X:SortS{}",
                )),
            ),
            (
                "claim",
                module(format!(
                    r"claim{{}} \implies{{SortS{{}}}}(
                        \and{{SortS{{}}}}(\top{{SortS{{}}}}(), {}),
                        \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}())
                    ) []",
                    term("a{}()")
                )),
            ),
            (
                "alias body",
                module(format!(
                    "alias deep{{}}(SortS{{}}) : SortS{{}} where deep{{}}(X:SortS{{}}) := {} []",
                    term("X:SortS{}")
                )),
            ),
            (
                "attribute",
                module(format!("sort SortT{{}} [note{{}}({})]", term("a{}()"))),
            ),
            (
                "declared sort",
                module(format!(
                    "symbol g{{}}({deep_sort}) : SortS{{}} [function{{}}()]"
                )),
            ),
        ]
    }

    /// Every deep definition shape, at the deepest depth that loading admits on a thread sized
    /// for about 160 levels, loads to completion; one level deeper is refused. The thread has
    /// under 4 MiB of stack, and the definitions take a few MB of heap.
    #[test]
    fn admitted_definition_depths_fit_on_the_thread() {
        const STACK: usize = STACK_RED_ZONE + 160 * STACK_PER_LEVEL;
        on_stack(STACK, || {
            let most = STACK / STACK_PER_LEVEL + 1;
            let refused_at = |shape: usize, levels: usize| {
                let (_, source) = deep_definitions(levels).swap_remove(shape);
                let syntax = parse_definition(&source).expect("definition should parse");
                match BackendDefinition::internalize(&syntax, "MAIN") {
                    Err(DefinitionError::InsufficientStack {
                        required,
                        remaining,
                        ..
                    }) => {
                        assert!(required > remaining);
                        true
                    }
                    Ok(_) | Err(_) => false,
                }
            };
            for (shape, (name, _)) in deep_definitions(2).into_iter().enumerate() {
                let syntax = parse_definition(&deep_definitions(2).swap_remove(shape).1).unwrap();
                if let Err(error) = BackendDefinition::internalize(&syntax, "MAIN") {
                    panic!("{name} at 2 levels: {error}");
                }
                assert!(
                    refused_at(shape, most),
                    "{name} at {most} levels is admitted"
                );
                // Invariant: `low` is admitted and `high` is refused.
                let (mut low, mut high) = (2, most);
                while high - low > 1 {
                    let middle = low + (high - low) / 2;
                    if refused_at(shape, middle) {
                        high = middle;
                    } else {
                        low = middle;
                    }
                }
            }
        });
    }

    /// A module whose aliases `al0` .. `al{count - 1}` each unfold into `levels` applications of
    /// `wrap` around the next alias, the last around its parameter, and whose alias `bind`
    /// places its parameter under an existential.
    fn alias_chain(count: usize, levels: usize) -> String {
        let aliases = (0..count)
            .map(|index| {
                let leaf = if index + 1 == count {
                    "X:SortS{}".to_owned()
                } else {
                    format!("al{}{{}}(X:SortS{{}})", index + 1)
                };
                format!(
                    "alias al{index}{{}}(SortS{{}}) : SortS{{}} where al{index}{{}}(X:SortS{{}}) := {} []\n",
                    chain(levels, "wrap{}(", &leaf, ")")
                )
            })
            .collect::<String>();
        format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                alias bind{{}}(SortS{{}}) : SortS{{}} where bind{{}}(X:SortS{{}}) :=
                    \exists{{SortS{{}}}}(Y:SortS{{}}, \and{{SortS{{}}}}(X:SortS{{}}, Y:SortS{{}})) []
                {aliases}
            endmodule []"#
        )
    }

    fn load(source: &str) -> Result<BackendDefinition, DefinitionError> {
        let syntax = parse_definition(source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
    }

    /// Every sentence of a chain of 20 aliases, each body 100 levels deep, fits on a thread
    /// sized for about 160 levels, but checking that the first alias unfolds descends through
    /// all 2,000 levels. Loading the module there is refused once an alias body no longer fits
    /// below the ones that enclose it, instead of overflowing the thread. A chain whose whole
    /// unfolding fits still loads and unfolds. The modules take well under 1 MB of heap.
    #[test]
    fn alias_chains_are_admitted_as_they_unfold_at_load() {
        const STACK: usize = STACK_RED_ZONE + 160 * STACK_PER_LEVEL;
        on_stack(STACK, || {
            assert!(matches!(
                load(&alias_chain(20, 100)),
                Err(DefinitionError::InsufficientStack { .. })
            ));
            let definition = load(&alias_chain(3, 20)).expect("a shallow chain should load");
            let pattern = parse_pattern("al0{}(a{}())").unwrap();
            run(&definition, "term", &pattern).expect("a shallow chain should unfold");
        });
    }

    /// A chain of 20 aliases, each body 100 levels deep, loads on a 64 MiB thread (under 50 MB
    /// of stack in a debug build). Unfolding `al0` in a request on a thread sized for about 160
    /// levels is refused once an alias body no longer fits below the ones enclosing it, as is
    /// the same request under 100 further levels, which the request's own admission accepts.
    /// The definition takes well under 1 MB of heap.
    #[test]
    fn alias_chains_are_admitted_as_they_unfold_in_requests() {
        const STACK: usize = STACK_RED_ZONE + 160 * STACK_PER_LEVEL;
        let definition = std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| load(&alias_chain(20, 100)).expect("the chain should load"))
            .expect("loader should spawn")
            .join()
            .expect("loader should finish");
        on_stack(STACK, move || {
            for source in [
                "al0{}(a{}())".to_owned(),
                chain(100, "wrap{}(", "al0{}(a{}())", ")"),
            ] {
                let pattern = parse_pattern(&source).unwrap();
                // Standalone verification reads alias applications without unfolding them.
                for entry in &ENTRY_POINTS[1..] {
                    assert!(refused(entry, run(&definition, entry, &pattern)), "{entry}");
                }
            }
        });
    }

    /// Alias bodies inline their arguments without descending into them, so 200 nested
    /// applications of an alias whose body is 200 levels deep unfold, on a thread sized for
    /// about 400 levels, into a 40,000-level argument of `bind`. Placing it under `bind`'s
    /// existential scans its free variables, which stays within the thread, and the
    /// 40,000-level expansion is then refused. The unfolding clones about 4 million nodes; the
    /// test peaks under 100 MB of resident memory and takes about 1 s in a debug build.
    #[test]
    fn deep_alias_arguments_are_scanned_without_recursion() {
        const STACK: usize = STACK_RED_ZONE + 400 * STACK_PER_LEVEL;
        on_stack(STACK, || {
            let definition = load(&alias_chain(1, 200)).expect("the alias should load");
            let source = format!("bind{{}}({})", chain(200, "al0{}(", "a{}()", ")"));
            let pattern = parse_pattern(&source).unwrap();
            let outcome = run(&definition, "pattern", &pattern);
            assert!(
                matches!(outcome, Err(DefinitionError::InsufficientStack { depth, .. }) if depth > 40_000),
                "{outcome:?}"
            );
        });
    }

    /// A pattern far deeper than the thread could recurse over is refused before any recursive
    /// pass runs, by every entry point, whatever it would otherwise be rejected for. One
    /// 200,000-level pattern is held at a time; the nesting tests together peak under 200 MB of
    /// resident memory and finish in about 3 s in a debug build.
    #[test]
    fn deep_patterns_are_refused_before_any_recursive_pass() {
        on_stack(8 << 20, || {
            let definition = definition();
            let levels = 200_000;
            for source in [
                chain(levels, r"\not{SortS{}}(", "undefined{}()", ")"),
                chain(levels, "nosuch{}(", "a{}()", ")"),
                chain(levels, "wrap{}(", "V:SortMissing{}", ")"),
                format!(
                    r"\top{{{}}}()",
                    chain(levels, "SortMissing{", "SortS{}", "}")
                ),
                chain(levels, "same{}(", "a{}()", ")"),
            ] {
                let pattern = parse_pattern(&source).expect("deep pattern should parse");
                for entry in ENTRY_POINTS {
                    assert!(refused(entry, run(&definition, entry, &pattern)), "{entry}");
                }
            }
        });
    }
}
