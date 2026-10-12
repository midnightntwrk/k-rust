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
    externalize::constrained_pattern,
    rewrite::{ExecutionOptions, Pattern, execute},
    simplify::{SimplificationOptions, simplify, simplify_pattern_with_solver},
    smt::{NoSolver, TranslationState},
    term::Term,
};
#[cfg(feature = "z3")]
use k_rust_backend::{
    rule::Predicate,
    smt::{SmtSolver, Z3Solver},
    substitution::Substitution,
    term::Variable,
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
    hooked-symbol listUpdate{}(SortList{}, SortInt{}, SortInt{}) : SortList{}
        [function{}(), hook{}("LIST.update")]
    hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
    hooked-symbol setItem{}(SortInt{}) : SortSet{}
        [function{}(), total{}(), hook{}("SET.element")]
    hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
        [function{}(), hook{}("SET.concat"), assoc{}(), comm{}()]
    symbol mstate{}(SortInt{}, SortMap{}) : SortState{} [constructor{}()]
    symbol lstate{}(SortInt{}, SortList{}) : SortState{} [constructor{}()]
    symbol sstate{}(SortInt{}, SortSet{}) : SortState{} [constructor{}()]
    symbol rstate{}(SortInt{}, SortMap{}) : SortState{} [constructor{}()]
    symbol qstate{}(SortInt{}, SortSet{}) : SortState{} [constructor{}()]
    symbol fstate{}(SortInt{}, SortList{}) : SortState{} [constructor{}()]
    symbol bstate{}(SortInt{}, SortList{}) : SortState{} [constructor{}()]
    symbol ustate{}(SortInt{}, SortList{}) : SortState{} [constructor{}()]
    symbol nstate{}(SortInt{}, SortMap{}) : SortState{} [constructor{}()]
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
        \and{SortState{}}(
            qstate{}(N:SortInt{}, setConcat{}(setItem{}(N:SortInt{}), S:SortSet{})),
            \top{SortState{}}()
        ),
        qstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            setConcat{}(setItem{}(N:SortInt{}), S:SortSet{})
        )
    ) [label{}("read-set")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(
            fstate{}(N:SortInt{}, listConcat{}(listItem{}(X:SortInt{}), L:SortList{})),
            \top{SortState{}}()
        ),
        fstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            listConcat{}(L:SortList{}, listItem{}(X:SortInt{}))
        )
    ) [label{}("rotate-front")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(
            bstate{}(N:SortInt{}, listConcat{}(L:SortList{}, listItem{}(X:SortInt{}))),
            \top{SortState{}}()
        ),
        bstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            listConcat{}(listItem{}(X:SortInt{}), L:SortList{})
        )
    ) [label{}("rotate-back")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(ustate{}(N:SortInt{}, L:SortList{}), \top{SortState{}}()),
        ustate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            listUpdate{}(L:SortList{}, \dv{SortInt{}}("0"), N:SortInt{})
        )
    ) [label{}("list-update")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(nstate{}(N:SortInt{}, M:SortMap{}), \top{SortState{}}()),
        nstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            mapUpdate{}(M:SortMap{}, N:SortInt{}, Y:SortInt{})
        )
    ) [label{}("map-new-name")]
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

/// `n` bindings `index |-> V<index>`: ground keys, each bound to a variable of its own.
fn symbolic_map_of(n: u64) -> String {
    collection_text("mapConcat{}", "mapUnit{}", n, |index| {
        format!(r#"mapItem{{}}(\dv{{SortInt{{}}}}("{index}"), V{index}:SortInt{{}})"#)
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

/// How many steps each measurement counts. Every collection measured has at least `2 * STEPS`
/// elements, so that every key the read shapes read is present.
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
    // Debug builds check the initial state's definedness claims once and mark what passed
    // (`definedness::check_ceil_free`); the marks stay on the shared state, so the first run
    // would pay that check alone. A first run pays it here, outside the measured ones.
    if cfg!(debug_assertions) {
        run(1);
    }
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
/// elements beyond what the carry's steps allocate on it ([`shape_steps`]). The same steps on a
/// collection of `SCALE * size` elements do the same work apart from the collection, which
/// cancels in the difference of the two measurements; what is left is what the larger
/// collection makes the steps pay.
///
/// A step that copies, rebuilds or re-synthesizes the elements it does not touch holds at least one
/// handle (`size_of::<Term>()`) for each element it copies, whatever the representation it copies
/// them into, so on the larger collection it allocates at least `(SCALE - 1) * size` handles more
/// per step. The bound is half of that: a step that copies at least half of the elements it does
/// not touch fails, however much its other work costs; since both the copy and the bound grow with
/// `size`, that holds at any size. A step that touches one element and the paths to it pays, on the
/// larger collection, for the levels the larger tree adds to those paths and for the nodes on them
/// being wider, up to the branching factor, a cost that does not grow with the elements; the bound
/// does, so the sizes are chosen large enough for it to exceed that cost by a wide margin. At 1024
/// and 8192 elements the shapes here pay at most about a tenth of the bound, in release and debug
/// builds. At 256 and 2048 the symbolic map paid 6 KiB a step more against a bound of 7 KiB: its
/// variable sets are trees of nodes up to 64 wide (the crate's `VARIABLE_BRANCHING`), and between
/// those sizes they keep their height while their roots widen, on each of the several variable sets
/// a step edits.
///
/// The check is a difference of two measurements, not a ratio, so it does not depend on where
/// the trees' heights change. An earlier form compared each size's steps with those on a
/// `2 * STEPS`-element collection, whose tree has the height of the smaller size's: a
/// logarithmic step then paid next to nothing at the smaller size, the ratio had nothing to
/// divide by, and the check needed a floor (the baseline steps' whole allocation) that also
/// admitted a copying step whose work apart from the collection was large enough.
///
/// `step_bytes(size)` must be positive: a shape whose steps allocate no more than its carry's
/// measures nothing beyond the carry, and the check would hold whatever the steps cost.
///
/// This compares steps with steps, so the per-step costs that do not depend on the collection
/// (matching the state, the counter, the step's own logs) cancel, unlike a total over `n` and
/// `SCALE * n` steps, whose quadratic part a large per-step constant can hide at test sizes: on
/// a release build the totals of the map and set shapes stay within 16 times while each step
/// copies the whole collection.
fn assert_step_independent_of_size(shape: &str, size: u64, step_bytes: impl Fn(u64) -> u64 + Sync) {
    assert!(
        size >= 2 * STEPS,
        "the read shapes read keys 0 .. 2 * STEPS"
    );
    let handle = std::mem::size_of::<Term>() as u64;
    let allowed = STEPS * (SCALE - 1) * size * handle / 2;
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, || {
                let small = step_bytes(size);
                let large = step_bytes(SCALE * size);
                let more = large.saturating_sub(small);
                eprintln!(
                    "{shape}: {STEPS} steps pay {small} bytes beyond the carry on {size} elements, {large} on {}: {more} more, bound {allowed}",
                    SCALE * size,
                );
                assert!(
                    small > 0,
                    "{shape}: the steps allocate no more than the carry's, so the check measures nothing"
                );
                assert!(
                    more <= allowed,
                    "{shape}: {STEPS} steps on {} elements pay {more} bytes more than on {size}, at least half a handle for each element added: the step grows with the collection",
                    SCALE * size
                );
            })
            .expect("the thread starts")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    });
}

#[test]
fn adding_one_map_entry_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("map, one MAP.update per step", 1024, |size| {
        shape_steps(&definition, "mstate", "cmstate", &map_of, size, size)
    });
}

#[test]
fn adding_one_list_element_costs_the_same_on_a_larger_list() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("list, one element appended per step", 1024, |size| {
        shape_steps(&definition, "lstate", "clstate", &list_of, size, size)
    });
}

#[test]
fn adding_one_set_element_costs_the_same_on_a_larger_set() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("set, one element added per step", 1024, |size| {
        shape_steps(&definition, "sstate", "csstate", &set_of, size, size)
    });
}

/// Taking the item at one end of a list by matching `ListItem(X) L` (or `L ListItem(X)`) and
/// putting it back at the other end, the K idiom of a queue: the step needs the one item, the
/// rest of the list is bound to `L` and put back unread.
#[test]
fn rotating_a_list_by_matching_one_end_costs_the_same_on_a_larger_list() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("list, first item moved last per step", 1024, |size| {
        shape_steps(&definition, "fstate", "clstate", &list_of, size, 0)
    });
    assert_step_independent_of_size("list, last item moved first per step", 1024, |size| {
        shape_steps(&definition, "bstate", "clstate", &list_of, size, 0)
    });
}

/// Overwriting one item of a list by `LIST.update`, the K idiom of an array.
#[test]
fn updating_one_list_item_costs_the_same_on_a_larger_list() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("list, one LIST.update per step", 1024, |size| {
        shape_steps(&definition, "ustate", "clstate", &list_of, size, 0)
    });
}

/// Reading one binding by matching `K |-> V M` and writing the map back, the K idiom
/// `<m> ... K |-> V ... </m>`: the step needs the binding of `K` and nothing else of the map.
#[test]
fn reading_one_map_binding_by_matching_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("map, one binding matched per step", 1024, |size| {
        shape_steps(&definition, "rstate", "cmstate", &map_of, size, 0)
    });
}

/// Reading one element by matching `SetItem(N) S` and writing the set back, the K idiom
/// `<s> ... SetItem(N) ... </s>`: the step needs to know that the set holds `N`, and the rest of the
/// set is bound to `S` and put back unread.
#[test]
fn reading_one_set_element_by_matching_costs_the_same_on_a_larger_set() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size("set, one element matched per step", 1024, |size| {
        shape_steps(&definition, "qstate", "csstate", &set_of, size, 0)
    });
}

/// A map whose values are distinct variables, so that the map and every term above it carry as
/// many variables as the map has bindings. Each step overwrites the binding of a present key,
/// `N |-> V<N>` by `N |-> N`, so it removes one variable from the map's and the configuration's
/// variable sets: the step changes one binding and one variable, and what it pays for the other
/// bindings and variables must not grow with them.
///
/// The steps subtracted are those carrying a ground map (`cmstate` on `map_of`), not the
/// symbolic one: a carry of the symbolic map is itself a step on a configuration of as many
/// variables, so any per-step cost in the number of variables would cancel in the difference
/// and the check would pass whatever that cost is.
#[test]
fn overwriting_one_symbolic_map_binding_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size(
        "symbolic map, one variable binding overwritten per step",
        1024,
        |size| {
            steps_from(&definition, "mstate", &symbolic_map_of, size, 0).saturating_sub(steps_from(
                &definition,
                "cmstate",
                &map_of,
                size,
                0,
            ))
        },
    );
}

/// A rule that introduces a variable: each step overwrites the binding of a present key,
/// `N |-> V<N>`, by `N |-> Y` for a `Y` the left-hand side does not bind, which the step names
/// apart from every variable of the state. The map and every term above it carry as many
/// variables as the map has bindings, and the new name must differ from all of them; what the
/// step pays to find one must not grow with them. The carry subtracted is a ground map's, as for
/// [`overwriting_one_symbolic_map_binding_costs_the_same_on_a_larger_map`].
#[test]
fn naming_a_new_variable_beside_a_symbolic_map_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(COLLECTIONS);
    assert_step_independent_of_size(
        "symbolic map, one binding overwritten by a new variable per step",
        1024,
        |size| {
            steps_from(&definition, "nstate", &symbolic_map_of, size, 0).saturating_sub(steps_from(
                &definition,
                "cmstate",
                &map_of,
                size,
                0,
            ))
        },
    );
}

/// A cell map as kompile builds a `multiplicity="*"` cell of type `Map`: instances
/// `instance(id(I), V)` keyed by their key cell `id(I)`, a free constructor application. `istate`
/// carries the map untouched; `gstate` reads instance `N` by matching it and writes the map back,
/// the K idiom `<r> <id> N </id> <v> V </v> </r>`.
const CELL_MAP: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortId{} []
    sort SortInstance{} []
    hooked-sort SortInstanceMap{}
        [hook{}("MAP.Map"), unit{}(instanceUnit{}()), element{}(instanceItem{}()),
         concat{}(instanceConcat{}())]
    sort SortState{} []
    hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    symbol id{}(SortInt{}) : SortId{} [constructor{}()]
    symbol instance{}(SortId{}, SortInt{}) : SortInstance{} [constructor{}()]
    hooked-symbol instanceUnit{}() : SortInstanceMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol instanceItem{}(SortId{}, SortInstance{}) : SortInstanceMap{}
        [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol instanceConcat{}(SortInstanceMap{}, SortInstanceMap{}) : SortInstanceMap{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    symbol istate{}(SortInt{}, SortInstanceMap{}) : SortState{} [constructor{}()]
    symbol gstate{}(SortInt{}, SortInstanceMap{}) : SortState{} [constructor{}()]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(istate{}(N:SortInt{}, M:SortInstanceMap{}), \top{SortState{}}()),
        istate{}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")), M:SortInstanceMap{})
    ) [label{}("carry-instances")]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(
            gstate{}(
                N:SortInt{},
                instanceConcat{}(
                    instanceItem{}(id{}(N:SortInt{}), instance{}(id{}(N:SortInt{}), V:SortInt{})),
                    M:SortInstanceMap{}
                )
            ),
            \top{SortState{}}()
        ),
        gstate{}(
            plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")),
            instanceConcat{}(
                instanceItem{}(id{}(N:SortInt{}), instance{}(id{}(N:SortInt{}), V:SortInt{})),
                M:SortInstanceMap{}
            )
        )
    ) [label{}("read-instance")]
endmodule []"#;

/// `n` instances `id(index) |-> instance(id(index), index)`.
fn instances_of(n: u64) -> String {
    collection_text("instanceConcat{}", "instanceUnit{}", n, |index| {
        let key = format!(r#"id{{}}(\dv{{SortInt{{}}}}("{index}"))"#);
        format!(r#"instanceItem{{}}({key}, instance{{}}({key}, \dv{{SortInt{{}}}}("{index}")))"#)
    })
}

/// A step on a configuration holding a cell map, which leaves the map as it is: what the step pays
/// for the configuration, its definedness among it, must not grow with the instances. The keys
/// are distinct applications of one free constructor to integers, so every two of them are apart
/// and the map states no obligation; the map's summary says so (one key header, no repeated
/// key) without reading the instances.
///
/// No carry is subtracted: the carry is the step measured.
#[test]
fn carrying_a_cell_map_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(CELL_MAP);
    assert_step_independent_of_size("cell map, carried per step", 1024, |size| {
        steps_from(&definition, "istate", &instances_of, size, 0)
    });
}

/// Reading one instance of a cell map by matching it and writing the map back, beside the carry
/// of [`carrying_a_cell_map_costs_the_same_on_a_larger_map`]: the step needs one instance and
/// its place, and the map it writes back keeps the summary that decides its keys apart.
#[test]
fn reading_one_cell_map_instance_costs_the_same_on_a_larger_map() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(CELL_MAP);
    assert_step_independent_of_size("cell map, one instance matched per step", 1024, |size| {
        steps_from(&definition, "gstate", &instances_of, size, 0).saturating_sub(steps_from(
            &definition,
            "istate",
            &instances_of,
            size,
            0,
        ))
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
    assert_predicate_chain_linear(
        shape,
        depth,
        "predicate nodes visited",
        Counter::SimplifyPredicateNodesVisited,
    );
}

/// Asserts that simplifying the `shape` chain counts `quantity` on `counter` linearly in its
/// depth.
fn assert_predicate_chain_linear(shape: &str, depth: u64, quantity: &str, counter: Counter) {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(PREDICATE_CHAINS);
    assert_linear(&format!("{shape} chain"), quantity, depth, |depth| {
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
        let counted = snapshot().delta(&before).get(counter);
        drop(result);
        counted
    });
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

/// A level of the chain normalizes to a conjunction nested in its parent's, and a nested
/// conjunction is simplified under its parent's assumptions. Those assumptions do not grow with
/// the depth: the parent's conjunct being simplified, which is not an assumption, holds `\top`
/// in its slot meanwhile, and `\top` states nothing, so it is not copied into the nested
/// conjunction's assumptions.
#[test]
fn a_disjunction_negation_chain_copies_known_predicates_linearly_in_its_depth() {
    assert_predicate_chain_linear(
        "ornot",
        100,
        "known predicates copied",
        Counter::SimplifyKnownPredicates,
    );
}

/// Each nested conjunction takes its conjuncts as its input, and the chain below a level is one
/// of them: a conjunction simplification that copies its input conjuncts copies the chain below
/// it at every level. Linear needs the copies replaced by borrowed views (K24 step 4b).
#[test]
#[ignore = "K24 4b: one clone per conjunction level remains"]
fn a_disjunction_negation_chain_copies_its_conjuncts_linearly_in_its_depth() {
    assert_predicate_chain_linear(
        "ornot",
        100,
        "input conjunct nodes",
        Counter::SimplifyConjunctNodes,
    );
}

/// Normalizing a conjunction or a disjunction whose operands are already normalized takes them
/// as they are, so a chain alternating the two is not normalized again below each level.
#[test]
fn an_alternating_conjunction_disjunction_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("andor", 100);
}

/// Printing an existential chain walks it a bounded number of times, not once per binder.
///
/// A binder is renamed for printing only when it prints like another variable of its body, so a
/// chain whose binders and free variable all print differently is printed as it is: deciding
/// that reads each node of the chain a bounded number of times, not the body of every binder.
#[test]
fn printing_an_existential_chain_visits_its_predicates_linearly_in_its_depth() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(PREDICATE_CHAINS);
    assert_linear(
        "printed exists chain",
        "predicate nodes visited",
        200,
        |depth| {
            let subject = pattern(&definition, &predicate_chain("exists", depth));
            let before = snapshot();
            let printed = constrained_pattern(&subject);
            let visited = snapshot()
                .delta(&before)
                .get(Counter::SimplifyPredicateNodesVisited);
            drop(printed);
            visited
        },
    );
}

/// The control: a negation chain, linear before the predicate equations were indexed by
/// connective, stays linear.
#[test]
fn a_negation_chain_visits_its_predicates_linearly_in_its_depth() {
    assert_predicate_walks_linear("not", 400);
}

// ---------- SMT queries: which conjuncts a validity check sends ----------

/// The variables `X0` to `Xn` of sort `Int`, read from `TEMPLATES`.
#[cfg(feature = "z3")]
fn int_variables(definition: &BackendDefinition, n: u64) -> Vec<Variable> {
    let sort = term(definition, "X:SortInt{}").sort();
    (0..=n)
        .map(|index| Variable::new(format!("X{index}"), sort.clone()))
        .collect()
}

/// The bytes one validity check of `checked` under `known` allocates, on a fresh solver so that
/// no cached answer is read.
#[cfg(feature = "z3")]
fn validity_check_bytes(
    definition: &BackendDefinition,
    known: &[Predicate],
    checked: &[Predicate],
) -> u64 {
    let solver = Z3Solver::new(definition).expect("the solver starts");
    bytes_of(|| {
        solver
            .check_predicates(known, &Substitution::new(), checked)
            .expect("no stop")
            .expect("the check translates")
    })
}

/// Checking an existential chain reads the SMT constants of its translation once.
///
/// Which known facts a check needs is decided by the constants the checked predicate mentions;
/// a binder's constant is one of them, and the constants under a binder are those of its body,
/// so collecting them is one walk of the translation, not one walk of the body per binder.
#[cfg(feature = "z3")]
#[test]
fn checking_an_existential_chain_allocates_linearly_in_its_depth() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(TEMPLATES);
    assert_linear("SMT check of an exists chain", "bytes", 200, |depth| {
        let variables = int_variables(&definition, depth);
        let sort = variables[0].sort.clone();
        let mut chain = Predicate::Equals(
            Term::variable(variables[0].clone()),
            Term::domain_value(sort, "1"),
        );
        for bound in &variables[1..] {
            chain = Predicate::Exists(bound.clone(), Box::new(chain));
        }
        validity_check_bytes(&definition, &[], &[chain])
    });
}

/// Selecting the known conjuncts linked to a check reads each conjunct's constants once.
///
/// The known facts `Xi = X(i+1)` are linked to a check of `X0` one after the other. The facts a
/// check needs are those reachable from its constants through shared constants, and a search
/// that indexes each fact by its constants reaches every fact once, however long the chain of
/// links that reaches it.
#[cfg(feature = "z3")]
#[test]
fn selecting_linked_known_conjuncts_allocates_linearly_in_their_number() {
    let _one = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let definition = definition(TEMPLATES);
    assert_linear(
        "SMT selection of linked known facts",
        "bytes",
        200,
        |links| {
            let variables = int_variables(&definition, links);
            let sort = variables[0].sort.clone();
            let known = variables
                .windows(2)
                .map(|pair| {
                    Predicate::Equals(
                        Term::variable(pair[0].clone()),
                        Term::variable(pair[1].clone()),
                    )
                })
                .collect::<Vec<_>>();
            let checked = Predicate::Equals(
                Term::variable(variables[0].clone()),
                Term::domain_value(sort, "1"),
            );
            validity_check_bytes(&definition, &known, &[checked])
        },
    );
}
