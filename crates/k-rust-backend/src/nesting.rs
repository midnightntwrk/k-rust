//! Native stack for the backend's recursive passes over KORE patterns, definitions, and the
//! terms built from them.
//!
//! Standalone verification, alias expansion, and internalization descend once per level of the
//! pattern they read, and so do the passes over the internal terms they build: matching,
//! simplification, rewriting, externalization, and the destruction of the terms. Loading a
//! definition runs the same passes over its sentences. The stack an operation takes therefore
//! grows linearly with the nesting depth of what it reads, and a pattern or module read from a
//! client can be of any depth, while overflowing the native stack aborts the whole process.
//!
//! The depth is measured before the work starts (`height`), by a recursion of bounded depth
//! that hands deeper subpatterns to explicit work lists, so an operation knows the stack it
//! needs before it takes any more than a fixed amount. [`with_stack`] runs the work on the
//! current thread when the thread's remaining stack covers that need, as before, and otherwise
//! on a new stack segment of the needed size, which `stacker` maps for the duration of the work
//! and unmaps afterwards. A segment is address space: its pages are committed only as the work
//! touches them, so the memory an operation uses is the stack it actually descends through, as it
//! would be on a thread that large. Because a segment is only provided when the thread has less
//! than the measured need, the work always has at least the stack it would have had on the thread.
//!
//! The segment is bounded by [`STACK_LIMIT`], a fixed reservation far above any thread an
//! embedder runs the backend on; work that would need more is refused with
//! [`DefinitionError::InsufficientStack`] before any of it runs. Mapping a segment can also fail
//! when the system refuses the reservation, which is refused the same way.
//!
//! The work must include everything that recurses over the deep terms: an operation returns only
//! external results built inside the segment, and its internal terms are dropped inside it.
//!
//! On wasm32 the engine's call-stack limit is invisible to the module and its stack cannot be
//! switched, and on a native thread whose bounds `stacker` cannot read the remaining stack is
//! unknown; there the work runs on the current stack unchanged, bounded by that stack as the
//! simplifier's own guard is (`stop::remaining_stack`).

use std::collections::BTreeMap;

use k_rust_kore::kore::ast as kore;

use crate::definition::DefinitionError;
use crate::stop::STACK_RED_ZONE;

/// Upper bound on the native stack that verification, alias expansion, internalization, the
/// passes over the internal terms, and the loading of a definition take per level of the
/// patterns and sorts they read, as counted by [`height`].
///
/// Measured by painting the stack below the caller and running each internalization entry
/// point on chains of every pattern constructor, on mixed chains, and on deep sorts: the
/// deepest level took 19,184 bytes unoptimized and 2,192 bytes in a release build, both at
/// an `\and` or `\or` level. Whole facade operations (execution, simplification, and
/// implication over application chains, and simplification of a negation chain), measured by
/// the pages they touched on a fresh segment, took at most 18.9 KiB per level unoptimized
/// and 2.7 KiB in a release build, both simplifying the negation chain. Simplifying ground
/// function chains (applications without equations, an equation that moves under a
/// constructor, and a list length added up with `INT.add`), the passes that take the most in
/// optimized builds, took at most 17.3 KiB per level unoptimized, 4,096 bytes at opt-level 1
/// with debug assertions (the `dev` profile), and 3,136 bytes in a release build, found as the
/// smallest bound under which 10,000-level chains still simplified. The fixed cost below the
/// first level, at most 62 KiB unoptimized, is within `STACK_RED_ZONE`, which also holds the
/// non-recursive work done at the deepest level.
///
/// The frames a level takes are decided by the code the crate is compiled to: the optimization
/// level, and debug assertions, which add checks and the data they read to the frames; so the
/// bound follows both (`build.rs`). It is 24 KiB unoptimized, 6 KiB at opt-level 1 or with
/// debug assertions, and 4 KiB in an optimized build without them: at least 1.25 times the most
/// any measured pass took per level in each. A build that does not report its optimization
/// level gets the unoptimized bound, the largest one.
///
/// `tests::every_shape_runs_on_the_stack_it_is_given` and
/// `tests::every_deep_definition_loads_on_the_stack_it_is_given` run every measured shape on a
/// stack of exactly the size this bound gives, and so does
/// `backend::tests::deep_function_chains_simplify_on_the_stack_the_backend_provides` in `k-rust`
/// for the function chains, through the facade, so a pass whose frames outgrow the bound
/// overflows there or stops for want of stack.
const STACK_PER_LEVEL: usize = if !OPTIMIZED {
    24 * 1024
} else if cfg!(any(debug_assertions, k_rust_opt_level = "1")) {
    6 * 1024
} else {
    4 * 1024
};

/// Whether the crate is compiled at an optimizing level, as `build.rs` reports it.
const OPTIMIZED: bool = cfg!(any(
    k_rust_opt_level = "1",
    k_rust_opt_level = "2",
    k_rust_opt_level = "3",
    k_rust_opt_level = "s",
    k_rust_opt_level = "z"
));

/// The largest stack segment [`with_stack`] maps for one piece of work.
///
/// A segment is reserved address space whose pages are committed only when touched, so the
/// limit bounds the reservation, not the memory used. 4 GiB is 64 times the 64 MiB worker threads
/// of the CLI and RPC server and 512 times Node's main thread, so no input that ran on such a
/// thread is refused; it admits about a million levels in a release build, 700,000 in the `dev`
/// profile, and about 170,000 in an unoptimized build. It stays well under the address space of
/// a 64-bit process and under the physical memory and swap that Linux's default overcommit
/// heuristic compares a single reservation against. A 32-bit process has a few GiB of address
/// space in all, so its limit is 256 MiB, four times the largest thread above.
#[cfg(target_pointer_width = "64")]
pub const STACK_LIMIT: usize = 4 << 30;
#[cfg(not(target_pointer_width = "64"))]
pub const STACK_LIMIT: usize = 256 << 20;

/// The most native stack, beyond the stack it starts on, that the simplifier's recursion takes on
/// one thread: 1 GiB on 64-bit targets, [`STACK_LIMIT`] on narrower ones.
///
/// [`with_stack`] sizes an operation's stack from the depth of what it reads, but evaluation can
/// recurse far deeper than its input: a recursive function over a list of n elements, or over a
/// term the execution built step by step, descends n levels in the simplifier. Each level of that
/// recursion checks the stack left (`stop::with_stack_headroom`); when less than the red zone
/// remains, the recursion goes on on a new 16 MiB segment, until the segments it holds would
/// exceed this budget, where it stops with `StackExhausted`. A recursion that stays within its
/// thread's stack maps nothing, so the budget costs nothing until it is used.
///
/// 1 GiB holds about 200,000 levels of a recursive function in a release build (`size(c(T)) =
/// 1 +Int size(T)`, about 5 KiB per level), where an 8 MiB thread alone held about 1,700. The
/// segments are reserved address space whose pages are committed as the recursion touches them,
/// so a runaway recursion commits up to the budget before it stops. 1 GiB is a quarter of
/// [`STACK_LIMIT`], so it stays under the same reservation bounds.
#[cfg(target_pointer_width = "64")]
pub const SIMPLIFICATION_STACK_BUDGET: usize = 1 << 30;
#[cfg(not(target_pointer_width = "64"))]
pub const SIMPLIFICATION_STACK_BUDGET: usize = STACK_LIMIT;

/// Run `work` with `bytes` as the budget of [`SIMPLIFICATION_STACK_BUDGET`] on this thread, and
/// restore the previous budget afterwards. A smaller budget stops a deep recursion sooner and
/// commits less memory before it does; 0 confines the simplifier to the stack it starts on.
pub fn with_simplification_stack_budget<R>(bytes: usize, work: impl FnOnce() -> R) -> R {
    crate::stop::with_segment_budget(bytes, work)
}

/// The deepest patterns and sorts, as counted by `height`, that [`with_stack`] provides the
/// stack for: about a million levels in a release build, 700,000 in the `dev` profile, and
/// 170,000 in an unoptimized build.
pub fn max_depth() -> usize {
    (STACK_LIMIT - STACK_RED_ZONE) / STACK_PER_LEVEL
}

/// The native stack, in bytes, that the backend's passes over patterns `depth` levels deep, as
/// counted by `height`, take at most.
pub fn stack_for_depth(depth: usize) -> usize {
    depth
        .saturating_mul(STACK_PER_LEVEL)
        .saturating_add(STACK_RED_ZONE)
}

/// Run `work`, whose recursive passes go over patterns and terms at most `depth` levels deep as
/// counted by `height`, on a stack that holds them.
///
/// The work runs on the current thread's stack when its remaining stack is unknown or covers
/// [`stack_for_depth`]`(depth)`, and otherwise on a segment of that size. It is refused with
/// [`DefinitionError::InsufficientStack`], without running, when the segment would exceed
/// [`STACK_LIMIT`] or cannot be mapped.
pub fn with_stack<R>(depth: usize, work: impl FnOnce() -> R) -> Result<R, DefinitionError> {
    #[cfg(target_family = "wasm")]
    {
        let _ = depth;
        Ok(work())
    }
    #[cfg(not(target_family = "wasm"))]
    {
        let required = stack_for_depth(depth);
        let Some(remaining) = crate::stop::remaining_stack() else {
            return Ok(work());
        };
        if required <= remaining {
            return Ok(work());
        }
        let refused = || DefinitionError::InsufficientStack {
            depth,
            required,
            limit: STACK_LIMIT.max(remaining),
        };
        if required > STACK_LIMIT {
            return Err(refused());
        }
        // `stacker` maps the segment before it runs the work and panics when the mapping
        // fails. A panic before `work` started is that failure, an ordinary refusal; a panic
        // from `work` itself continues to unwind as it would have without the segment.
        let mut started = false;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            stacker::grow(required, || {
                started = true;
                work()
            })
        }));
        match outcome {
            Ok(result) => Ok(result),
            Err(_) if !started => Err(refused()),
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }
}

/// The refusal that [`with_stack`] gives, before running any of it, to work over patterns
/// `depth` levels deep on the current thread because no segment it maps holds that depth;
/// `None` when it would run the work, or would refuse it only if the system declined to map the
/// segment.
pub(crate) fn refusal(depth: usize) -> Option<DefinitionError> {
    #[cfg(target_family = "wasm")]
    {
        let _ = depth;
        None
    }
    #[cfg(not(target_family = "wasm"))]
    {
        let required = stack_for_depth(depth);
        let remaining = crate::stop::remaining_stack()?;
        (required > remaining && required > STACK_LIMIT).then(|| {
            DefinitionError::InsufficientStack {
                depth,
                required,
                limit: STACK_LIMIT.max(remaining),
            }
        })
    }
}

/// What [`height`] knows about the definition a pattern is read in: which applications unfold
/// into deeper patterns, and how deep the chains that associative applications fold into are.
pub(crate) trait Unfolding {
    /// The height of the body of alias `name` with every alias in it unfolded, counting each of
    /// its parameters as a leaf; `None` when `name` is not an alias.
    fn alias_height(&self, name: &str) -> Option<usize>;

    /// The number of levels the chain that an associative application of `symbol` to
    /// `arguments` folds into adds above its arguments.
    fn associative_levels(&self, symbol: &kore::Symbol, arguments: &[kore::Pattern]) -> usize {
        let _ = symbol;
        arguments.len()
    }
}

/// A pattern read without a definition: no application unfolds, and an associative application
/// of `n` arguments is a chain of `n` levels.
pub(crate) struct Syntactic;

impl Unfolding for Syntactic {
    fn alias_height(&self, _name: &str) -> Option<usize> {
        None
    }
}

/// Aliases whose unfolded heights are known, read without the rest of a definition.
pub(crate) struct Aliases<'a>(pub(crate) &'a BTreeMap<String, usize>);

impl Unfolding for Aliases<'_> {
    fn alias_height(&self, name: &str) -> Option<usize> {
        self.0.get(name).copied()
    }
}

/// The number of levels of `pattern`, as the backend's passes descend through it: an upper
/// bound on the depth of `pattern` with its aliases unfolded and of every internal term or
/// predicate internalized from it.
///
/// A node carrying sorts is one level above the deepest of them. An alias application is the
/// unfolded height of the alias body above its deepest argument or sort argument, since the
/// arguments replace parameters inside the body. An `\and` with `k` arguments that have term
/// components, which internalization folds into a chain of `k - 1` binary conjunctions, is `k`
/// levels; its predicate arguments are internalized side by side. An associative application is
/// as many levels as `unfolding` says the chain it folds into has, and an associative
/// application of an alias unfolds that many alias applications, one in the other.
///
/// Loading measures every sentence of a definition this way, so the walk must cost no more than
/// visiting each node: the top [`RECURSION_LIMIT`] levels are measured by recursion, which
/// allocates nothing, and each subpattern below them with explicit work lists, so the stack the
/// measurement takes is bounded whatever the depth of `pattern`.
pub(crate) fn height(pattern: &kore::Pattern, unfolding: &impl Unfolding) -> usize {
    measure(pattern, unfolding, 0).0
}

/// Levels of a pattern or sort measured by recursion before the rest is measured with explicit
/// work lists. A recursive level takes well under 1 KiB of stack even unoptimized, so the
/// recursion stays within a small fraction of `STACK_RED_ZONE`, and almost every pattern and
/// sort a definition holds is measured without allocating.
const RECURSION_LIMIT: usize = 64;

/// The (height, whether it has a term component) of `pattern`, `depth` levels below where the
/// measurement started.
fn measure(pattern: &kore::Pattern, unfolding: &impl Unfolding, depth: usize) -> (usize, bool) {
    if depth >= RECURSION_LIMIT {
        return measure_iteratively(pattern, unfolding);
    }
    let (first, second) = children(pattern);
    let mut deepest_child = 0;
    let mut term_children = 0;
    for child in first.iter().chain(second) {
        let (height, term) = measure(child, unfolding, depth + 1);
        deepest_child = deepest_child.max(height);
        term_children += usize::from(term);
    }
    level(pattern, unfolding, deepest_child, term_children)
}

/// [`measure`] with explicit work lists, for a subpattern of any depth.
fn measure_iteratively(pattern: &kore::Pattern, unfolding: &impl Unfolding) -> (usize, bool) {
    use kore::Pattern;

    enum Visit<'a> {
        Enter(&'a Pattern),
        Exit(&'a Pattern),
    }

    // Invariant: after the `Exit` of a node is handled, `done` ends with that node's
    // (height, whether it has a term component), and the entries of its children, pushed in
    // order before it, have been replaced by it.
    let mut done: Vec<(usize, bool)> = Vec::new();
    let mut pending = vec![Visit::Enter(pattern)];
    // Each `Enter` pushes one `Exit` and an `Enter` per proper subpattern, so the loop
    // terminates.
    while let Some(visit) = pending.pop() {
        match visit {
            Visit::Enter(pattern) => {
                pending.push(Visit::Exit(pattern));
                let (first, second) = children(pattern);
                pending.extend(first.iter().chain(second).rev().map(Visit::Enter));
            }
            Visit::Exit(pattern) => {
                let (first, second) = children(pattern);
                let start = done.len() - first.len() - second.len();
                let below = &done[start..];
                let deepest_child = below.iter().map(|(height, _)| *height).max().unwrap_or(0);
                let term_children = below.iter().filter(|(_, term)| *term).count();
                done.truncate(start);
                done.push(level(pattern, unfolding, deepest_child, term_children));
            }
        }
    }
    done.pop().unwrap_or((0, false))
}

/// The (height, whether it has a term component) of `pattern`, whose deepest direct
/// subpattern is `deepest_child` levels high and `term_children` of whose direct subpatterns
/// have term components.
fn level(
    pattern: &kore::Pattern,
    unfolding: &impl Unfolding,
    deepest_child: usize,
    term_children: usize,
) -> (usize, bool) {
    use kore::Pattern;

    let deepest_sort = sorts(pattern).map(sort_height).max().unwrap_or(0);
    let below = deepest_child.max(deepest_sort);
    let (levels, term) = match pattern {
        Pattern::Application { symbol, .. } => {
            (unfolding.alias_height(&symbol.name).unwrap_or(1), true)
        }
        Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            let levels = match unfolding.alias_height(&symbol.name) {
                Some(alias) => alias.saturating_mul(arguments.len()),
                None => unfolding.associative_levels(symbol, arguments),
            };
            (levels, true)
        }
        Pattern::String(_) | Pattern::Variable(_) | Pattern::DomainValue { .. } => (1, true),
        Pattern::And { .. } => (term_children.max(1), term_children > 0),
        Pattern::Exists { .. } | Pattern::Forall { .. } => (1, term_children > 0),
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::Or { .. }
        | Pattern::Not { .. }
        | Pattern::Next { .. }
        | Pattern::Implies { .. }
        | Pattern::Iff { .. }
        | Pattern::Rewrites { .. }
        | Pattern::Mu { .. }
        | Pattern::Nu { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. } => (1, false),
    };
    (levels.max(1).saturating_add(below), term)
}

/// The direct subpatterns of `pattern`, in order.
pub(crate) fn children(pattern: &kore::Pattern) -> (&[kore::Pattern], &[kore::Pattern]) {
    use kore::Pattern;
    use std::slice::from_ref;

    match pattern {
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => (&[], &[]),
        Pattern::Application { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. } => (arguments, &[]),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => (from_ref(&**argument), &[]),
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => (from_ref(&**body), &[]),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => (from_ref(&**left), from_ref(&**right)),
    }
}

/// The sorts that `pattern` carries itself, not those of its subpatterns.
pub(crate) fn sorts(pattern: &kore::Pattern) -> impl Iterator<Item = &kore::Sort> {
    use kore::Pattern;
    use std::slice::from_ref;

    let (first, second): (&[kore::Sort], &[kore::Sort]) = match pattern {
        Pattern::String(_) => (&[], &[]),
        Pattern::Variable(variable) => (from_ref(&variable.sort), &[]),
        Pattern::Application { symbol, .. } | Pattern::AssociativeApplication { symbol, .. } => {
            (&symbol.sort_parameters, &[])
        }
        Pattern::Top { sort }
        | Pattern::Bottom { sort }
        | Pattern::DomainValue { sort, .. }
        | Pattern::And { sort, .. }
        | Pattern::Or { sort, .. }
        | Pattern::Not { sort, .. }
        | Pattern::Next { sort, .. }
        | Pattern::Implies { sort, .. }
        | Pattern::Iff { sort, .. }
        | Pattern::Rewrites { sort, .. } => (from_ref(sort), &[]),
        Pattern::Exists { sort, variable, .. } | Pattern::Forall { sort, variable, .. } => {
            (from_ref(sort), from_ref(&variable.sort))
        }
        Pattern::Mu { variable, .. } | Pattern::Nu { variable, .. } => {
            (from_ref(&variable.sort), &[])
        }
        Pattern::Ceil {
            operand_sort,
            result_sort,
            ..
        }
        | Pattern::Floor {
            operand_sort,
            result_sort,
            ..
        }
        | Pattern::Equals {
            operand_sort,
            result_sort,
            ..
        }
        | Pattern::In {
            operand_sort,
            result_sort,
            ..
        } => (from_ref(&**operand_sort), from_ref(result_sort)),
    };
    first.iter().chain(second)
}

/// The number of nodes on the longest path from `sort` to a leaf: by recursion for the top
/// [`RECURSION_LIMIT`] levels, as almost every sort is, and with an explicit work list below.
pub(crate) fn sort_height(sort: &kore::Sort) -> usize {
    sort_height_from(sort, 0)
}

/// [`sort_height`] of `sort`, `depth` levels below where the measurement started.
fn sort_height_from(sort: &kore::Sort, depth: usize) -> usize {
    let kore::Sort::Application { arguments, .. } = sort else {
        return 1;
    };
    if depth >= RECURSION_LIMIT {
        return sort_height_iteratively(sort);
    }

    1 + arguments
        .iter()
        .map(|argument| sort_height_from(argument, depth + 1))
        .max()
        .unwrap_or(0)
}

/// [`sort_height`] computed without recursion, for a sort of any depth.
fn sort_height_iteratively(sort: &kore::Sort) -> usize {
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

/// The unfolded height ([`Unfolding::alias_height`]) of each alias of `aliases`, given as its
/// name and body, with associative applications counted by `unfolding` and every other alias
/// unknown to it.
///
/// Each body is measured after the bodies of the aliases it applies, in a topological order of
/// the application relation found with explicit work lists. The body of an alias on a cycle,
/// which loading refuses (`alias::collect`), is measured with the aliases on the cycle counted
/// as one level.
pub(crate) fn alias_heights<'a>(
    aliases: impl IntoIterator<Item = (&'a str, &'a kore::Pattern)>,
) -> BTreeMap<String, usize> {
    let aliases = aliases.into_iter().collect::<Vec<_>>();
    let index = aliases
        .iter()
        .enumerate()
        .map(|(position, (name, _))| (*name, position))
        .collect::<BTreeMap<_, _>>();
    let mut dependents = vec![Vec::new(); aliases.len()];
    let mut waiting = vec![0_usize; aliases.len()];
    for (position, (_, body)) in aliases.iter().enumerate() {
        let mut applied = std::collections::BTreeSet::new();
        let mut pending = vec![*body];
        // Each pop pushes only proper subpatterns of the popped one, so the loop terminates.
        while let Some(pattern) = pending.pop() {
            if let kore::Pattern::Application { symbol, .. }
            | kore::Pattern::AssociativeApplication { symbol, .. } = pattern
                && let Some(&callee) = index.get(symbol.name.as_str())
            {
                applied.insert(callee);
            }
            let (first, second) = children(pattern);
            pending.extend(first.iter().chain(second));
        }
        waiting[position] = applied.len();
        for callee in applied {
            dependents[callee].push(position);
        }
    }
    let mut heights = BTreeMap::new();
    let mut ready = (0..aliases.len())
        .filter(|&position| waiting[position] == 0)
        .collect::<Vec<_>>();
    // Invariant: every alias in `ready` has all the aliases its body applies in `heights`, and
    // each alias enters `ready` at most once, when its last callee is measured.
    while let Some(position) = ready.pop() {
        let (name, body) = aliases[position];
        let measured = height(body, &Aliases(&heights));
        heights.insert(name.to_owned(), measured);
        for &dependent in &dependents[position] {
            waiting[dependent] -= 1;
            if waiting[dependent] == 0 {
                ready.push(dependent);
            }
        }
    }
    // The aliases left are on or below a cycle.
    for (position, (name, body)) in aliases.iter().enumerate() {
        if waiting[position] > 0 {
            let measured = height(body, &Aliases(&heights));
            heights.insert((*name).to_owned(), measured);
        }
    }
    heights
}

/// The height (`height`) of the deepest pattern or sort of `module` as it is written, its
/// alias applications not unfolded.
pub fn module_depth(module: &kore::Module) -> usize {
    definition_height(&[module], &Syntactic)
}

/// The height of the deepest pattern or sort in `modules`, the modules of a definition: the
/// patterns of their sentences and attributes, with the aliases of `aliases` unfolded, and the
/// sorts of their declarations.
pub(crate) fn definition_height(modules: &[&kore::Module], aliases: &impl Unfolding) -> usize {
    modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter(|sentence| is_rule_or_claim(sentence))
        .map(|sentence| sentence_height(sentence, aliases))
        .fold(declarations_height(modules, aliases), usize::max)
}

/// [`definition_height`] of everything in `modules` but their axioms and claims: the module
/// attributes and the declarations, with their attributes.
///
/// Loading reads axioms and claims only at their roots and attributes until it verifies them,
/// so it measures each of them just before verifying it ([`sentence_height`]), when the
/// measurement loads the sentence into the cache for its verification. Measured up front, they
/// would be walked once more in full, after parsing has evicted them.
pub(crate) fn declarations_height(modules: &[&kore::Module], aliases: &impl Unfolding) -> usize {
    modules
        .iter()
        .map(|module| {
            module
                .sentences
                .iter()
                .filter(|sentence| !is_rule_or_claim(sentence))
                .map(|sentence| sentence_height(sentence, aliases))
                .fold(attributes_height(&module.attributes, aliases), usize::max)
        })
        .max()
        .unwrap_or(0)
}

/// Whether `sentence` is an axiom or a claim, measured where it is verified rather than with
/// the declarations ([`declarations_height`]).
pub(crate) fn is_rule_or_claim(sentence: &kore::Sentence) -> bool {
    matches!(
        sentence,
        kore::Sentence::Axiom { .. } | kore::Sentence::Claim { .. }
    )
}

/// The height of the deepest pattern of `attributes`.
fn attributes_height(attributes: &kore::Attributes, aliases: &impl Unfolding) -> usize {
    attributes
        .0
        .iter()
        .map(|pattern| height(pattern, aliases))
        .max()
        .unwrap_or(0)
}

/// The height of the deepest pattern or sort of `sentence`: its patterns and attributes, with
/// the aliases of `aliases` unfolded, and the sorts it declares.
pub(crate) fn sentence_height(sentence: &kore::Sentence, aliases: &impl Unfolding) -> usize {
    let attributes = |attributes: &kore::Attributes| attributes_height(attributes, aliases);
    let sorts = |sorts: &[kore::Sort]| sorts.iter().map(sort_height).max().unwrap_or(0);
    match sentence {
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
            .max(sort_height(result_sort)),
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
            .max(sort_height(result_sort))
            .max(height(left, aliases))
            .max(height(right, aliases)),
        kore::Sentence::Axiom {
            pattern,
            attributes: own,
            ..
        }
        | kore::Sentence::Claim {
            pattern,
            attributes: own,
            ..
        } => attributes(own).max(height(pattern, aliases)),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::definition::BackendDefinition;
    use crate::stop::remaining_stack;

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

    fn on_stack<R: Send + 'static>(bytes: usize, work: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new()
            .stack_size(bytes)
            .spawn(work)
            .expect("worker should spawn")
            .join()
            .expect("worker should finish")
    }

    /// The stack of the threads the tests below run on, far below what their patterns need:
    /// 512 KiB, the smallest stack embedders commonly give a thread. It is more than four times
    /// the 64 KiB thread of `stop::tests`, so glibc never hands one of these stacks, cached when
    /// its thread exits, to that thread.
    const SMALL_STACK: usize = 512 * 1024;

    /// Levels of the shapes and definitions that the tests below run: deep enough that their
    /// passes need several times `SMALL_STACK` at the optimization level the crate is compiled
    /// at (`build.rs`), which they are given on a segment of exactly the size `stack_for_depth`
    /// gives. Unoptimized passes take about 14 to 17 KiB per level of these shapes and passes at
    /// opt-level 1 about 1.5 to 2.2 KiB, where 300 levels would fit `SMALL_STACK` and a pass run
    /// without its segment would go unnoticed.
    const LEVELS: usize = if OPTIMIZED { 1_500 } else { 300 };

    #[test]
    fn height_counts_levels_as_the_passes_descend_through_them() {
        let syntactic = |source: &str| height(&parse_pattern(source).unwrap(), &Syntactic);
        assert_eq!(syntactic("a{}()"), 1);
        assert_eq!(syntactic("X:SortS{}"), 2);
        assert_eq!(syntactic(r"\top{SortL{SortL{SortS{}}}}()"), 4);
        assert_eq!(syntactic("wrap{}(wrap{}(a{}()))"), 3);
        assert_eq!(
            syntactic(r"\implies{SortS{}}(wrap{}(wrap{}(a{}())), \top{SortS{}}())"),
            4
        );
        assert_eq!(
            syntactic(r"\exists{SortS{}}(X:SortL{SortL{SortS{}}}, a{}())"),
            4
        );
        // An associative application folds into a chain as long as its arguments.
        assert_eq!(
            syntactic(r"\left-assoc{}(c{}(a{}(), wrap{}(a{}()), a{}()))"),
            5
        );
        // A conjunction folds its term arguments into a chain and keeps predicates beside it.
        assert_eq!(
            syntactic(r#"\and{SortS{}}(a{}(), wrap{}(\dv{SortS{}}("1")))"#),
            5
        );
        assert_eq!(
            syntactic(r"\and{SortS{}}(a{}(), \top{SortS{}}(), \top{SortS{}}(), a{}(), a{}())"),
            5
        );
        assert_eq!(
            syntactic(r"\and{SortS{}}(\top{SortS{}}(), \top{SortS{}}(), \top{SortS{}}())"),
            3
        );
        let conjuncts = vec!["a{}()"; 1000].join(", ");
        assert_eq!(syntactic(&format!(r"\and{{SortS{{}}}}({conjuncts})")), 1001);

        // An alias application counts the unfolded height of the alias body, its parameter a
        // two-level leaf, above its argument.
        let definition = definition();
        let unfolded = |source: &str| height(&parse_pattern(source).unwrap(), &definition);
        assert_eq!(unfolded("same{}(a{}())"), 3);
        assert_eq!(unfolded("twice{}(wrap{}(a{}()))"), 6);
        assert_eq!(unfolded("twice{}(twice{}(a{}()))"), 9);
    }

    /// The recursion that measures the top levels hands each subpattern and subsort below them
    /// to the work lists, and both give every shape the same height, whichever level the
    /// handover happens at.
    #[test]
    fn recursion_and_work_lists_measure_alike() {
        let definition = definition();
        for (name, source) in shapes(3 * RECURSION_LIMIT) {
            let pattern = parse_pattern(&source).expect("shape should parse");
            let iterative = measure_iteratively(&pattern, &definition);
            for start in [0, RECURSION_LIMIT / 2, RECURSION_LIMIT - 1, RECURSION_LIMIT] {
                assert_eq!(measure(&pattern, &definition, start), iterative, "{name}");
            }
            for sort in sorts(&pattern) {
                let iterative = sort_height_iteratively(sort);
                for start in [0, RECURSION_LIMIT - 1, RECURSION_LIMIT] {
                    assert_eq!(sort_height_from(sort, start), iterative, "{name}");
                }
            }
        }
        let deep_sort = parse_pattern(&format!(
            r"\top{{{}}}()",
            chain(3 * RECURSION_LIMIT, "SortL{", "SortS{}", "}")
        ))
        .unwrap();
        let sort = sorts(&deep_sort).next().unwrap();
        assert_eq!(sort_height(sort), 3 * RECURSION_LIMIT + 1);
        assert_eq!(sort_height_iteratively(sort), 3 * RECURSION_LIMIT + 1);
    }

    #[test]
    fn alias_heights_unfold_the_aliases_their_bodies_apply() {
        let syntax = parse_definition(&alias_chain(3, 10)).unwrap();
        let module = &syntax.modules[0];
        let heights = alias_heights(module.sentences.iter().filter_map(
            |sentence| match sentence {
                kore::Sentence::AliasDeclaration { alias, right, .. } => {
                    Some((alias.name.as_str(), right.as_ref()))
                }
                _ => None,
            },
        ));
        // `al2` is 10 levels of `wrap` over its parameter, a leaf two levels high with its sort.
        // An application counts the unfolded height of the alias over its argument, here the
        // parameter of the alias above, so each alias above adds 12 levels to the one it applies.
        assert_eq!(heights["al2"], 12);
        assert_eq!(heights["al1"], 24);
        assert_eq!(heights["al0"], 36);
    }

    /// Work runs on the current stack when it fits there, and otherwise on a segment of the
    /// size measured for it, whatever stack its thread has.
    #[test]
    fn work_gets_the_stack_measured_for_it() {
        on_stack(SMALL_STACK, || {
            let before = remaining_stack().unwrap();
            let fits = with_stack(1, || remaining_stack().unwrap()).unwrap();
            assert!(
                fits < before && before - fits < 64 * 1024,
                "{before} {fits}"
            );
            let depth = 1000;
            let given = with_stack(depth, || remaining_stack().unwrap()).unwrap();
            assert!(given > before, "{before} {given}");
            assert!(given <= stack_for_depth(depth), "{given}");
            assert!(given + 64 * 1024 > stack_for_depth(depth), "{given}");
            // The thread's own stack is used again afterwards.
            assert!(remaining_stack().unwrap() <= before + 64 * 1024);
        });
    }

    /// Work deeper than the largest segment is refused before it runs; a panic in the work on
    /// a segment unwinds to the caller as it would on the thread.
    #[test]
    fn work_too_deep_for_any_segment_is_refused_and_panics_propagate() {
        on_stack(SMALL_STACK, || {
            let depth = max_depth();
            assert!(stack_for_depth(depth) <= STACK_LIMIT);
            assert!(stack_for_depth(depth + 1) > STACK_LIMIT);
            let mut ran = false;
            let outcome = with_stack(depth + 1, || ran = true);
            assert!(!ran);
            assert!(matches!(
                outcome,
                Err(DefinitionError::InsufficientStack { depth: refused, required, limit })
                    if refused == depth + 1 && required > limit && limit == STACK_LIMIT
            ));
            let panic = std::panic::catch_unwind(|| with_stack(1000, || panic!("from the work")));
            let payload = panic.expect_err("the work's panic propagates");
            assert_eq!(payload.downcast_ref::<&str>(), Some(&"from the work"));
        });
    }

    /// Every shape the bound was measured on runs every entry point on a thread whose stack
    /// is far smaller than the shape needs, on a segment of exactly the size `stack_for_depth`
    /// gives for its height: a pass whose frames outgrew `STACK_PER_LEVEL` overflows the segment
    /// and aborts the test binary. The segments reserve under 40 MB each, of which the work
    /// touches a few MB, and the test takes a few seconds.
    #[test]
    fn every_shape_runs_on_the_stack_it_is_given() {
        on_stack(SMALL_STACK, || {
            let definition = definition();
            for (name, source) in shapes(LEVELS) {
                let pattern = parse_pattern(&source).expect("shape should parse");
                let depth = height(&pattern, &definition);
                assert!(stack_for_depth(depth) > 2 * SMALL_STACK, "{name}");
                for entry in ENTRY_POINTS {
                    let outcome = definition
                        .with_stack_for(&[&pattern], || run(&definition, entry, &pattern))
                        .unwrap_or_else(|error| panic!("{name} by {entry}: {error}"));
                    if let Err(error) = outcome {
                        assert!(
                            !matches!(error, DefinitionError::InsufficientStack { .. }),
                            "{name} by {entry}: {error}"
                        );
                    }
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

    /// Every deep definition shape loads, and is dropped, on a thread whose stack is far
    /// smaller than its sentences need: loading measures them and provides the stack. The
    /// definitions take a few MB of heap.
    #[test]
    fn every_deep_definition_loads_on_the_stack_it_is_given() {
        on_stack(SMALL_STACK, || {
            for (name, source) in deep_definitions(LEVELS) {
                let syntax = parse_definition(&source).expect("definition should parse");
                let definition = BackendDefinition::internalize(&syntax, "MAIN")
                    .unwrap_or_else(|error| panic!("{name}: {error}"));
                assert!(stack_for_depth(definition.operation_depth(&[])) > 2 * SMALL_STACK);
                drop(definition);
            }
        });
    }

    /// A definition whose rule is 6,000 levels deep is loaded and dropped on a thread whose
    /// stack holds neither: the internal rule's destruction recurses once per level, and the
    /// definition provides the stack for it when it is dropped. Unoptimized (opt-level 0, the
    /// `debugging` profile), the load touches about 80 MB of stack and takes a second or two.
    #[test]
    fn deep_definitions_are_dropped_on_the_stack_they_need() {
        on_stack(SMALL_STACK, || {
            let (_, source) = deep_definitions(6_000).swap_remove(0);
            let definition = load(&source).expect("the definition should load");
            drop(definition);
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

    /// A chain of 20 aliases, each body 100 levels deep, unfolds into 2,000 levels: it loads,
    /// and a request applying it, alone or under 100 further levels, internalizes, on a thread
    /// whose stack holds about 20 levels unoptimized (opt-level 0, the `debugging` profile). The
    /// modules take well under 1 MB of heap; the unfolding touches about 25 MB of stack
    /// unoptimized.
    #[test]
    fn alias_chains_get_the_stack_of_their_unfolding() {
        on_stack(SMALL_STACK, || {
            let definition = load(&alias_chain(20, 100)).expect("the chain should load");
            for source in [
                "al0{}(a{}())".to_owned(),
                chain(100, "wrap{}(", "al0{}(a{}())", ")"),
            ] {
                let pattern = parse_pattern(&source).unwrap();
                assert!(definition.operation_depth(&[&pattern]) > 2_000);
                for entry in &ENTRY_POINTS[1..] {
                    if *entry == "implication pattern" {
                        continue;
                    }
                    definition
                        .with_stack_for(&[&pattern], || run(&definition, entry, &pattern))
                        .unwrap()
                        .unwrap_or_else(|error| panic!("{entry}: {error}"));
                }
            }
        });
    }

    /// Unfolding an alias chain provides the stack for each body where it enters it, so the
    /// unfolding alone, run without the stack an operation measures for it, does not overflow
    /// a small thread either.
    #[test]
    fn alias_bodies_get_their_stack_where_unfolding_enters_them() {
        let definition = load(&alias_chain(20, 100)).expect("the chain should load");
        let definition = std::sync::Arc::new(definition);
        let shared = definition.clone();
        let expanded = on_stack(SMALL_STACK, move || {
            let pattern = parse_pattern("al0{}(a{}())").unwrap();
            let expanded =
                crate::alias::expand(&pattern, shared.aliases()).expect("the chain should unfold");
            height(&expanded, &Syntactic)
        });
        assert_eq!(expanded, 2_001);
        drop(definition);
    }

    /// Alias bodies inline their arguments without descending into them, so 40 nested
    /// applications of an alias whose body is 40 levels deep unfold into a 1,600-level argument
    /// of `bind`, whose free variables are scanned without recursion. The unfolding, and every
    /// entry point over it, runs on the stack measured for it.
    #[test]
    fn deep_alias_arguments_unfold_on_the_stack_measured_for_them() {
        on_stack(SMALL_STACK, || {
            let definition = load(&alias_chain(1, 40)).expect("the alias should load");
            let source = format!("bind{{}}({})", chain(40, "al0{}(", "a{}()", ")"));
            let pattern = parse_pattern(&source).unwrap();
            let depth = definition.operation_depth(&[&pattern]);
            let expanded = definition
                .with_stack_for(&[&pattern], || {
                    crate::alias::expand(&pattern, definition.aliases())
                        .map(|expanded| height(&expanded, &Syntactic))
                })
                .unwrap()
                .expect("the aliases should unfold");
            assert!(expanded > 1_600 && expanded <= depth, "{expanded} {depth}");
            for entry in &ENTRY_POINTS[1..] {
                let outcome = definition
                    .with_stack_for(&[&pattern], || run(&definition, entry, &pattern))
                    .unwrap();
                assert!(
                    !matches!(outcome, Err(DefinitionError::InsufficientStack { .. })),
                    "{entry}"
                );
            }
        });
    }

    /// A pattern deeper than the largest segment provides for is refused before any pass over
    /// it runs, whatever it would otherwise be rejected for. One pattern that deep (about 700,000
    /// levels at opt-level 1, a million in a release build, 175,000 unoptimized) is held at a
    /// time; at opt-level 1 the test peaks at about 550 MB of resident memory.
    #[test]
    fn patterns_deeper_than_any_segment_are_refused_before_any_pass() {
        on_stack(SMALL_STACK, || {
            let definition = definition();
            let levels = max_depth() + 1;
            for source in [
                chain(levels, r"\not{SortS{}}(", "undefined{}()", ")"),
                chain(levels, "nosuch{}(", "a{}()", ")"),
                format!(
                    r"\top{{{}}}()",
                    chain(levels, "SortMissing{", "SortS{}", "}")
                ),
                chain(levels / 2, "same{}(", "a{}()", ")"),
            ] {
                let pattern = parse_pattern(&source).expect("deep pattern should parse");
                for entry in ENTRY_POINTS {
                    let mut ran = false;
                    let outcome = definition.with_stack_for(&[&pattern], || {
                        ran = true;
                        run(&definition, entry, &pattern)
                    });
                    assert!(!ran, "{entry}");
                    assert!(
                        matches!(outcome, Err(DefinitionError::InsufficientStack { .. })),
                        "{entry}"
                    );
                }
            }
        });
    }

    /// A definition of one module `MAIN` holding `sentences`, a sort `SortS` with a constant `a`,
    /// a parametric sort `SortL`, a constructor `c` of any sort, and sort injections.
    fn module_with(sentences: &str) -> String {
        format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                sort SortL{{A}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol c{{S}}() : S [constructor{{}}(), functional{{}}()]
                symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
                {sentences}
            endmodule []"#
        )
    }

    /// A load that fails on a sort 20,000 levels deep returns an error that the caller drops,
    /// formats, and compares on its own small thread: a rule writes an injection from that sort,
    /// which no subsort declaration licenses. The error holds the sort in its KORE form, whose
    /// traits use explicit work lists; the internal form's recursive destruction overflowed this
    /// thread. The sort's text takes about 200 KB.
    #[test]
    fn errors_naming_deep_sorts_are_handled_on_any_thread() {
        let deep = chain(20_000, "SortL{", "SortS{}", "}");
        let source = module_with(&format!(
            r#"axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}()),
                \and{{SortS{{}}}}(inj{{{deep}, SortS{{}}}}(c{{{deep}}}()), \top{{SortS{{}}}}())
            ) [label{{}}("deep")]"#
        ));
        on_stack(SMALL_STACK, move || {
            let Err(error) = load(&source) else {
                panic!("the injection is unlicensed");
            };
            let DefinitionError::UnlicensedInjection {
                source: written, ..
            } = &error
            else {
                panic!("the load fails on the injection");
            };
            assert_eq!(sort_height(written), 20_001);
            assert!(error.clone() == error);
            let text = error.to_string();
            assert!(text.starts_with("Unlicensed injection from SortL{SortL{"));
            assert!(text.contains(&deep), "the error names the written sort");
            assert!(format!("{error:?}").contains(r#"name: "SortL""#));
            drop(error);
        });
    }

    /// A definition with a sentence deeper than any segment provides for is refused with
    /// `InsufficientStack`, at the depth of its deepest sentence, whatever else is wrong with it
    /// and wherever that is, although the declarations are read and earlier sentences verified
    /// before the deep sentence is measured. One definition that deep (about 700,000 levels at
    /// opt-level 1, a million in a release build, 175,000 unoptimized) is held at a time.
    #[test]
    fn definitions_deeper_than_any_segment_are_refused_whatever_else_they_hold() {
        on_stack(SMALL_STACK, || {
            let levels = max_depth() + 1;
            let deep = format!(
                r#"axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(a{{}}(), {}),
                    \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}())
                ) []"#,
                chain(levels, r"\not{SortS{}}(", r"\top{SortS{}}()", ")")
            );
            let unknown_head = r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(nosuch{}(), \top{SortS{}}()),
                \and{SortS{}}(a{}(), \top{SortS{}}())
            ) []"#;
            for (name, sentences) in [
                ("alone", deep.clone()),
                (
                    "after an unknown sort",
                    format!("symbol bad{{}}(SortMissing{{}}) : SortS{{}} []\n{deep}"),
                ),
                (
                    "before an unknown sort",
                    format!("{deep}\nsymbol bad{{}}(SortMissing{{}}) : SortS{{}} []"),
                ),
                ("after an invalid axiom", format!("{unknown_head}\n{deep}")),
            ] {
                let Err(error) = load(&module_with(&sentences)) else {
                    panic!("{name}: the definition is refused");
                };
                assert!(
                    matches!(
                        error,
                        DefinitionError::InsufficientStack { depth, .. } if depth > levels
                    ),
                    "{name}: {error}"
                );
            }
        });
    }
}
