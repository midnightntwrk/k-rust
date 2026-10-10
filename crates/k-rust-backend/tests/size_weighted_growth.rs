//! Size-weighted growth checks: the bytes a computation allocates, not only how many events it
//! counts.
//!
//! The event counters of `k_rust_kore::measure` count one constructed term, one equation
//! attempt or one rewrite step whatever the size of what the event touches, so a step that
//! copies an `n`-entry collection, or a level of a recursion that copies everything its
//! subterm produced, counts the same as one that copies nothing (`measure_ratchet.rs` keeps
//! `simplifier_work_per_step_stays_flat_with_cached_closed_collections` green on a map that is
//! rebuilt whole at every step). Allocated bytes are weighted by size: a copy of `n` entries
//! allocates `n` entries.
//!
//! Two kinds of check:
//!
//! - A step on a collection (adding one element, reading one binding) is compared with the
//!   same step on a collection 8 times as large (`assert_step_independent_of_size`). The step
//!   needs one element and its place, so what it pays for the elements it does not touch must
//!   not grow in proportion to them.
//! - A nested input (a recursion's levels, nested templates) runs at `n` and at `8n` levels, and
//!   the bytes allocated beyond the `0`-level run are compared (`assert_linear`). Work that is
//!   linear in the levels allocates about 8 times as much at `8n`; a vector that doubles as it
//!   grows can at most double that, so a linear computation stays within 16 times. A
//!   computation that copies at each level what the levels below built allocates about 64 times
//!   as much. The bound is the linear class with its doubling allowance, not a budget.
//!
//! A walk that allocates nothing is not seen by bytes. The predicate walks (which variables a
//! predicate mentions, matching a predicate equation's left-hand side) are counted instead, by
//! `Counter::SimplifyPredicateNodesVisited`, with the same linear-class check over a chain of one
//! connective (`assert_linear`).
//!
//! The allocator counts every thread of the test binary, so the checks take one lock and run one
//! at a time.

const _: () = assert!(cfg!(feature = "measure"));

use std::sync::Mutex;

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, Pattern, execute},
    simplify::{SimplificationOptions, simplify, simplify_pattern_with_solver},
    smt::{NoSolver, TranslationState},
    term::Term,
};
use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{Counter, CountingAllocator, set_allocation_counters, snapshot},
};

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

/// How many times the units of the larger run exceed those of the smaller.
const SCALE: u64 = 8;

/// Linear work allocates `SCALE` times as much at `SCALE` times the units, and amortized vector
/// growth can double that.
const LINEAR_WITH_DOUBLING: u64 = 2 * SCALE;

fn allocated_bytes() -> u64 {
    let mut now = snapshot();
    set_allocation_counters(&mut now);
    now.get(Counter::AllocatedBytes)
}

fn bytes_of<T>(work: impl FnOnce() -> T) -> u64 {
    let before = allocated_bytes();
    let result = work();
    let after = allocated_bytes();
    drop(result);
    after - before
}

/// Asserts that `measured(units)` beyond `measured(0)` is in the linear class between `units`
/// and `SCALE * units`; `quantity` names what is measured (bytes, or a counter's visits).
///
/// Both quantities are held to [`LINEAR_WITH_DOUBLING`]. The question the check answers is
/// whether a level costs what it adds (about `SCALE` times at `SCALE` times the levels) or
/// redoes what the levels below it did (about `SCALE * SCALE` times), and any bound between the
/// two classes answers it. A counter's visits do not double as a vector does, so a linear walk
/// stays near `SCALE` times; its own bound could be lower, but one at `SCALE` itself would leave
/// no margin for the work of a run that is not proportional to its levels and that subtracting
/// `measured(0)` does not remove, and the doubled bound is still a factor `SCALE / 2` below the
/// quadratic class. So one bound states the class boundary for both quantities.
///
/// The runs go a few thousand levels deep, and the term readers and the SMT translation recurse
/// once per level on the caller's stack, so they run on a thread with room for that.
fn assert_linear(shape: &str, quantity: &str, units: u64, measured: impl Fn(u64) -> u64 + Sync) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, || {
                assert_linear_here(shape, quantity, units, &measured)
            })
            .expect("the thread starts")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    });
}

fn assert_linear_here(shape: &str, quantity: &str, units: u64, measured: &dyn Fn(u64) -> u64) {
    let base = measured(0);
    let small = measured(units).saturating_sub(base);
    let large = measured(SCALE * units).saturating_sub(base);
    eprintln!(
        "{shape}: {small} {quantity} at {units}, {large} at {}, ratio {:.1}",
        SCALE * units,
        large as f64 / small.max(1) as f64
    );
    assert!(small > 0, "{shape}: the measured work has no {quantity}");
    assert!(
        large <= LINEAR_WITH_DOUBLING * small,
        "{shape}: {large} {quantity} at {} units against {small} at {units}: more than {LINEAR_WITH_DOUBLING} times",
        SCALE * units
    );
}

fn definition(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    definition
        .admit_unverified(&parse_pattern(source).expect("pattern should parse"), &[])
        .internalize_pattern()
        .expect("pattern should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .admit_unverified(&parse_pattern(source).expect("term should parse"), &[])
        .internalize_term()
        .expect("term should internalize")
}

fn nested(head: &str, depth: u64, leaf: &str) -> String {
    let depth = depth as usize;
    format!(
        "{}{leaf}{}",
        format!("{head}(").repeat(depth),
        ")".repeat(depth)
    )
}

// ---------- collections: one element added per step ----------

/// Three counters, each with a collection that gains one element per step: `M[N <- N]`,
/// `L ListItem(N)` and `S SetItem(N)`.
const COLLECTIONS: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-sort SortList{}
        [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
    hooked-sort SortSet{}
        [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
    sort SortState{} []
    hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{}
        [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-symbol mapUpdate{}(SortMap{}, SortInt{}, SortInt{}) : SortMap{}
        [function{}(), total{}(), hook{}("MAP.update")]
    hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
    hooked-symbol listItem{}(SortInt{}) : SortList{}
        [function{}(), total{}(), hook{}("LIST.element")]
    hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
        [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
    hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
    hooked-symbol setItem{}(SortInt{}) : SortSet{}
        [function{}(), total{}(), hook{}("SET.element")]
    hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
        [function{}(), hook{}("SET.concat"), assoc{}(), comm{}()]
    symbol mstate{}(SortInt{}, SortMap{}) : SortState{} [constructor{}()]
    symbol lstate{}(SortInt{}, SortList{}) : SortState{} [constructor{}()]
    symbol sstate{}(SortInt{}, SortSet{}) : SortState{} [constructor{}()]
    symbol rstate{}(SortInt{}, SortMap{}) : SortState{} [constructor{}()]
    symbol cmstate{}(SortInt{}, SortMap{}) : SortState{} [constructor{}()]
    symbol clstate{}(SortInt{}, SortList{}) : SortState{} [constructor{}()]
    symbol csstate{}(SortInt{}, SortSet{}) : SortState{} [constructor{}()]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(mstate{}(N:SortInt{}, M:SortMap{}), \top{SortState{}}()),
        mstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            mapUpdate{}(M:SortMap{}, N:SortInt{}, N:SortInt{})
        )
    ) [label{}("map")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(lstate{}(N:SortInt{}, L:SortList{}), \top{SortState{}}()),
        lstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            listConcat{}(L:SortList{}, listItem{}(N:SortInt{}))
        )
    ) [label{}("list")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(sstate{}(N:SortInt{}, S:SortSet{}), \top{SortState{}}()),
        sstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            setConcat{}(S:SortSet{}, setItem{}(N:SortInt{}))
        )
    ) [label{}("set")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(
            rstate{}(N:SortInt{}, mapConcat{}(mapItem{}(N:SortInt{}, V:SortInt{}), M:SortMap{})),
            \top{SortState{}}()
        ),
        rstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            mapConcat{}(mapItem{}(N:SortInt{}, V:SortInt{}), M:SortMap{})
        )
    ) [label{}("read")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(cmstate{}(N:SortInt{}, C:SortMap{}), \top{SortState{}}()),
        cmstate{}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")), C:SortMap{})
    ) [label{}("carry-cmstate")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(clstate{}(N:SortInt{}, C:SortList{}), \top{SortState{}}()),
        clstate{}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")), C:SortList{})
    ) [label{}("carry-clstate")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(csstate{}(N:SortInt{}, C:SortSet{}), \top{SortState{}}()),
        csstate{}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")), C:SortSet{})
    ) [label{}("carry-csstate")]
endmodule []"#;

/// `n` elements `0 .. n` of a collection, as nested `concat` applications of `element`s, or
/// `unit` when `n` is 0. `element` is given the index and returns the element's text.
fn collection_text(concat: &str, unit: &str, n: u64, element: impl Fn(u64) -> String) -> String {
    if n == 0 {
        return format!("{unit}()");
    }
    let mut text = String::new();
    for index in 0..n - 1 {
        text.push_str(&format!("{concat}({}, ", element(index)));
    }
    text.push_str(&element(n - 1));
    text.push_str(&")".repeat((n - 1) as usize));
    text
}

fn map_of(n: u64) -> String {
    collection_text("mapConcat{}", "mapUnit{}", n, |index| {
        format!(r#"mapItem{{}}(\dv{{SortInt{{}}}}("{index}"), \dv{{SortInt{{}}}}("{index}"))"#)
    })
}

fn list_of(n: u64) -> String {
    collection_text("listConcat{}", "listUnit{}", n, |index| {
        format!(r#"listItem{{}}(\dv{{SortInt{{}}}}("{index}"))"#)
    })
}

fn set_of(n: u64) -> String {
    collection_text("setConcat{}", "setUnit{}", n, |index| {
        format!(r#"setItem{{}}(\dv{{SortInt{{}}}}("{index}"))"#)
    })
}

/// How many steps each measurement counts. The collection the baseline steps start from has
/// `2 * STEPS` elements, so that every key the read shape reads is present.
const STEPS: u64 = 64;

/// Bytes allocated by steps `STEPS + 1 ..= 2 * STEPS` from `state(start, collection of size)`,
/// where `start` is the first index the steps add or read: the bytes of a `2 * STEPS`-step
/// execution minus those of a `STEPS`-step one, so that what an execution pays once for its
/// initial state, which is proportional to the collection, cancels.
fn steps_from(
    definition: &BackendDefinition,
    state: &str,
    collection: &dyn Fn(u64) -> String,
    size: u64,
    start: u64,
) -> u64 {
    let initial = pattern(
        definition,
        &format!(
            r#"{state}{{}}(\dv{{SortInt{{}}}}("{start}"), {})"#,
            collection(size)
        ),
    );
    let run = |steps: u64| {
        let initial = initial.clone();
        bytes_of(|| {
            let result = execute(
                definition,
                initial,
                ExecutionOptions {
                    max_depth: steps,
                    ..ExecutionOptions::default()
                },
            );
            assert_eq!(result.leaves.len(), 1, "{result:#?}");
            assert_eq!(result.leaves[0].depth, steps);
            result
        })
    };
    run(2 * STEPS).saturating_sub(run(STEPS))
}

/// [`steps_from`] for `state`, minus the same for `carry`, whose steps carry the same
/// collection untouched. What a step pays for the configuration whatever it does with the
/// collection cancels: nothing in a release build, and in a debug build the checks that walk
/// the whole configuration at every step, which would otherwise make every shape here, and its
/// fix, grow with the collection.
fn shape_steps(
    definition: &BackendDefinition,
    state: &str,
    carry: &str,
    collection: &dyn Fn(u64) -> String,
    size: u64,
    start: u64,
) -> u64 {
    steps_from(definition, state, collection, size, start)
        .saturating_sub(steps_from(definition, carry, collection, size, start))
}

/// Asserts that a step which adds or reads one element of a collection does work that does not
/// grow in proportion to the collection.
///
/// `step_bytes(size)` is the bytes `STEPS` steps allocate on a collection of about `size`
/// elements; the same steps on a collection of `2 * STEPS` elements are subtracted, which leaves
/// what the steps pay for the elements they do not touch. A step that copies, re-synthesizes or
/// rebuilds the collection pays for every element beyond the baseline's: `SCALE * size - 128`
/// against `size - 128`, 15 times between 256 and 2048 elements. A step that touches one
/// element and the path to it pays at most a logarithmic factor (11/8 between 256 and 2048
/// elements, under 3 even doubled for node splits). The check asks for at most `SCALE / 2`, with
/// an eighth of what the baseline steps allocate as a floor, so that a step that pays almost
/// nothing for the collection at either size is not judged by the ratio of two small numbers.
///
/// This compares steps with steps, so the per-step costs that do not depend on the collection
/// (matching the state, the counter, the step's own logs) cancel, unlike a total over `n` and
/// `SCALE * n` steps, whose quadratic part a large per-step constant can hide at test sizes: on
/// a release build the totals of the map and set shapes stay within 16 times while each step
/// copies the whole collection.
fn assert_step_independent_of_size(shape: &str, size: u64, step_bytes: impl Fn(u64) -> u64 + Sync) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, || {
                let base = step_bytes(2 * STEPS);
                let small = step_bytes(size).saturating_sub(base);
                let large = step_bytes(SCALE * size).saturating_sub(base);
                eprintln!(
                    "{shape}: {STEPS} steps pay {small} bytes for {size} elements, {large} for {}, ratio {:.1}",
                    SCALE * size,
                    large as f64 / small.max(1) as f64
                );
                assert!(
                    2 * large <= SCALE * small + base / SCALE,
                    "{shape}: {STEPS} steps on {} elements pay {large} bytes for the elements they do not touch, against {small} on {size}: the step grows with the collection",
                    SCALE * size
                );
            })
            .expect("the thread starts")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    });
}

#[test]
#[ignore = "K22: a step still copies the whole map, which the local fixes leave; un-ignore with the persistent representation"]
fn adding_one_map_entry_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("map, one MAP.update per step", 256, |size| {
        shape_steps(&definition, "mstate", "cmstate", &map_of, size, size)
    });
}

#[test]
#[ignore = "K22: a step still copies the whole list, which the local fixes leave; un-ignore with the persistent representation"]
fn adding_one_list_element_costs_the_same_on_a_larger_list() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("list, one element appended per step", 256, |size| {
        shape_steps(&definition, "lstate", "clstate", &list_of, size, size)
    });
}

#[test]
#[ignore = "K22: a step still copies the whole set, which the local fixes leave; un-ignore with the persistent representation"]
fn adding_one_set_element_costs_the_same_on_a_larger_set() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("set, one element added per step", 256, |size| {
        shape_steps(&definition, "sstate", "csstate", &set_of, size, size)
    });
}

/// Reading one binding by matching `K |-> V M` and writing the map back, the K idiom
/// `<m> ... K |-> V ... </m>`: the step needs the binding of `K` and nothing else of the map.
#[test]
#[ignore = "K22: the frame still copies the map without the binding, which the local fixes leave; un-ignore with the persistent representation"]
fn reading_one_map_binding_by_matching_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("map, one binding matched per step", 256, |size| {
        shape_steps(&definition, "rstate", "cmstate", &map_of, size, 0)
    });
}

// ---------- chains: one level of a nested input per unit ----------

/// `size(c^n(z)) = n` by the non-tail recursion `size(c(T)) = 1 + size(T)` (`fn.k`).
const NON_TAIL: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortT{} []
    hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    symbol z{}() : SortT{} [constructor{}()]
    symbol c{}(SortT{}) : SortT{} [constructor{}()]
    symbol size{}(SortT{}) : SortInt{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, z{}()), \top{R}())),
        \equals{SortInt{}, R}(size{}(X0:SortT{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
    ) [label{}("size-z")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, c{}(T:SortT{})), \top{R}())),
        \equals{SortInt{}, R}(
            size{}(X0:SortT{}),
            \and{SortInt{}}(plusInt{}(\dv{SortInt{}}("1"), size{}(T:SortT{})), \top{SortInt{}}())
        )
    ) [label{}("size-c")]
endmodule []"#;

#[test]
fn a_non_tail_recursion_allocates_linearly_in_its_depth() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(NON_TAIL);
    assert_linear("size(c^n(z))", "bytes", 500, |depth| {
        let subject = term(
            &definition,
            &format!("size{{}}({})", nested("c{}", depth, "z{}()")),
        );
        bytes_of(|| {
            let result = simplify(&definition, &subject, SimplificationOptions::default())
                .expect("no stop")
                .expect("simplifies");
            assert_eq!(
                result.term,
                term(&definition, &format!("\\dv{{SortInt{{}}}}(\"{depth}\")"))
            );
            result
        })
    });
}

/// `absInt`, whose `smt-hook` template names its argument three times.
const TEMPLATES: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    symbol absInt{}(SortInt{}) : SortInt{}
        [function{}(), total{}(), smt-hook{}("(ite (< #1 0) (- 0 #1) #1)")]
endmodule []"#;

#[test]
fn translating_nested_hook_templates_allocates_linearly_in_their_depth() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(TEMPLATES);
    assert_linear("absInt^n(X) to SMT-LIB", "bytes", 250, |depth| {
        let subject = term(&definition, &nested("absInt{}", depth, "X:SortInt{}"));
        bytes_of(|| {
            TranslationState::new()
                .translate_term(&subject)
                .expect("translates")
        })
    });
}

// ---------- predicate chains: one level of one connective per unit ----------

/// Two partial functions `f` and `g` for the chains, and predicate equations of every top
/// connective the chains have, over a third partial function `h` that no chain mentions, so none
/// applies: at each level of a chain the simplifier tries the equations of that level's
/// connective, and only those.
const PREDICATE_CHAINS: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    symbol f{}(SortInt{}) : SortInt{} [function{}()]
    symbol g{}(SortInt{}) : SortInt{} [function{}()]
    symbol h{}(SortInt{}) : SortInt{} [function{}()]
    axiom{R, Q} \implies{R}(
        \top{R}(),
        \equals{Q, R}(\ceil{SortInt{}, Q}(h{}(Z:SortInt{})), \and{Q}(\top{Q}(), \top{Q}()))
    ) [label{}("ceil-h"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \top{R}(),
        \equals{Q, R}(
            \exists{Q}(Y:SortInt{}, \equals{SortInt{}, Q}(h{}(Y:SortInt{}), Z:SortInt{})),
            \and{Q}(\top{Q}(), \top{Q}())
        )
    ) [label{}("exists-h"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \top{R}(),
        \equals{Q, R}(
            \forall{Q}(Y:SortInt{}, \equals{SortInt{}, Q}(h{}(Y:SortInt{}), Z:SortInt{})),
            \and{Q}(\top{Q}(), \top{Q}())
        )
    ) [label{}("forall-h"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \top{R}(),
        \equals{Q, R}(
            \implies{Q}(\ceil{SortInt{}, Q}(h{}(Z:SortInt{})), \ceil{SortInt{}, Q}(h{}(W:SortInt{}))),
            \and{Q}(\top{Q}(), \top{Q}())
        )
    ) [label{}("implies-h"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \top{R}(),
        \equals{Q, R}(
            \or{Q}(\ceil{SortInt{}, Q}(h{}(Z:SortInt{})), \ceil{SortInt{}, Q}(h{}(W:SortInt{}))),
            \and{Q}(\top{Q}(), \top{Q}())
        )
    ) [label{}("or-h"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \top{R}(),
        \equals{Q, R}(
            \not{Q}(\ceil{SortInt{}, Q}(h{}(Z:SortInt{}))),
            \and{Q}(\top{Q}(), \top{Q}())
        )
    ) [label{}("not-h"), simplification{}()]
endmodule []"#;

/// `X /\ \floor(f(X)) /\ chain`, the chain `depth` levels of `shape`'s connective over
/// `\ceil(f(X))`: `\exists` or `\forall` binding a fresh variable per level, `\implies` and `\or`
/// with `\ceil(g(X))` as the other operand (the `\or` over a `\not`), `\not` alone, or `\and`
/// and `\or` alternating with `\ceil(g(Ai))` over a fresh variable `Ai` at level `i` as the
/// other operand, so that no operand is implied by another.
fn predicate_chain(shape: &str, depth: u64) -> String {
    let ceil = |function: &str| {
        format!("\\ceil{{SortInt{{}}, SortInt{{}}}}({function}{{}}(X:SortInt{{}}))")
    };
    let mut chain = ceil("f");
    for level in 0..depth {
        chain = match shape {
            "andor" => format!(
                "\\{}{{SortInt{{}}}}(\\ceil{{SortInt{{}}, SortInt{{}}}}(g{{}}(A{level}:SortInt{{}})), {chain})",
                if level % 2 == 0 { "and" } else { "or" }
            ),
            "exists" | "forall" => {
                format!("\\{shape}{{SortInt{{}}}}(Y{level}:SortInt{{}}, {chain})")
            }
            "implies" => format!("\\implies{{SortInt{{}}}}({}, {chain})", ceil("g")),
            "ornot" => format!(
                "\\or{{SortInt{{}}}}({}, \\not{{SortInt{{}}}}({chain}))",
                ceil("g")
            ),
            "not" => format!("\\not{{SortInt{{}}}}({chain})"),
            _ => unreachable!("no chain shape {shape}"),
        };
    }
    format!(
        "\\and{{SortInt{{}}}}(X:SortInt{{}}, \\and{{SortInt{{}}}}(\\floor{{SortInt{{}}, SortInt{{}}}}(f{{}}(X:SortInt{{}})), {chain}))"
    )
}

/// Asserts that simplifying the `shape` chain visits predicate nodes linearly in its depth.
///
/// Whether a predicate mentions a variable is a fact a parent derives from its children, and a
/// predicate equation of another connective does not match, so trying the equations at a level
/// needs that level, not the chain below it: the walks of one simplification of the chain visit
/// a number of nodes linear in its depth.
fn assert_predicate_walks_linear(shape: &str, depth: u64) {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(PREDICATE_CHAINS);
    assert_linear(
        &format!("{shape} chain"),
        "predicate nodes visited",
        depth,
        |depth| {
            let subject = pattern(&definition, &predicate_chain(shape, depth));
            let before = snapshot();
            let result = simplify_pattern_with_solver(
                &definition,
                &subject,
                SimplificationOptions::default(),
                &NoSolver,
            )
            .expect("no stop")
            .expect("simplifies");
            let visited = snapshot()
                .delta(&before)
                .get(Counter::SimplifyPredicateNodesVisited);
            drop(result);
            visited
        },
    );
}

#[test]
fn an_existential_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("exists", 200);
}

#[test]
fn a_universal_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("forall", 200);
}

#[test]
fn an_implication_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("implies", 200);
}

#[test]
fn a_disjunction_negation_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("ornot", 100);
}

/// Normalizing a conjunction or a disjunction whose operands are already normalized takes them
/// as they are, so a chain alternating the two is not normalized again below each level.
#[test]
fn an_alternating_conjunction_disjunction_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("andor", 100);
}

/// The control: a negation chain, linear before the predicate equations were indexed by
/// connective, stays linear.
#[test]
fn a_negation_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("not", 400);
}
