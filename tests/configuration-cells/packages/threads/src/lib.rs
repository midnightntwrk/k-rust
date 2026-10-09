//! A Map cell collection (KF-023): K's lesson 1.17-B, fork and join.
//!
//! `<thread>` is a `multiplicity = "*"` collection of whole cells, keyed by
//! its first child `<id>`. The field keeps its instance type `Thread`; the
//! init value is the template of one thread, and `initial` makes the
//! configuration start with that thread, the main thread running `$PGM`.
//!
//! A rule names threads in braces: `{ me @ Thread { .. }, .. }` matches
//! *some* thread and labels it `me`; `..` is every other thread. In the
//! result, `Thread { k: [n, ..], ..me }` updates `me` in place and
//! `Thread { id: n, k: [ss], .. }` creates a thread whose other children
//! take their template defaults. A subject instance left out of the result
//! is removed. Rules over `k` alone, such as `assign` and the strictness
//! rules, match the computation cell of any thread.
//!
//! - `spawn { s }` creates a thread running `s` and evaluates to its id;
//! - `join t` waits until thread `t` reaches `return i;`, removes it, and
//!   evaluates to `i`.

use k::KResult;
use k::builtin::{Id, Int, KSequence, Map, int, map};

k::sorts! {
    #[k::bracket("(", ")")]
    Exp;
    impl Exp for Id;

    Value: Exp + KResult;
    impl Value for Int;

    Stmt;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left add (Add) > thread (Spawn, Join))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Exp, rhs: Exp },
    #[k::syntax("spawn {{{body}}}")]
    Spawn { body: Stmt },
    #[k::syntax("join {thread}")] #[k::strict]
    Join { thread: Exp },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(stmt (Assign, Return) > right seq (Seq))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("{name} = {value};")] #[k::strict(value)]
    Assign { name: Id, value: Exp },
    #[k::syntax("return {value};")] #[k::strict]
    Return { value: Exp },
    #[k::syntax("{first} {second}")]
    Seq { first: Stmt, second: Stmt },
}

/// The thread collection's parent.
#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub thread: Thread,
}

/// One thread; its first child `id` is the Map key.
#[k::cell]
pub struct Thread {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub k: KSequence,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(nested)]
    pub threads: Threads,
    #[k::cell]
    pub state: Map<Id, Int>,
    #[k::cell(name = "nextId")]
    pub next_id: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            threads: Threads {
                thread: Thread {
                    id: 0,
                    k: k::k![pgm],
                },
            },
            state: k::map![],
            next_id: 1,
        }
    }
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    add: Add(a, b) => int::add(a, b) where a: Int, b: Int;
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    /// Read a variable.
    var: {
        k: [name, ..],
        state: { name -> value, .. },
    } => {
        k: [value, ..],
    }
    where name: Id;

    /// Assign a value.
    assign: {
        k: [StmtSyntax::Assign(name, value), ..],
        state: s,
    } => {
        k: [..],
        state: map::update(s, name, value),
    }
    where value: Int;

    /// Start a thread running `body`; the spawning thread receives its id.
    spawn: {
        thread: { me @ Thread { k: [Spawn(body), ..], .. }, .. },
        next_id: n,
    } => {
        thread: { Thread { k: [n, ..], .. me }, Thread { id: n, k: [body], .. }, .. },
        next_id: int::add(n, 1),
    };
}

/// Wait for thread `t` to return `i`, then remove that thread: the
/// reference spelling `krs expand` prints for a readable collection rule.
#[k::rule(label = "join")]
pub fn join(
    t: k::Term<Int>,
    i: k::Term<Int>,
    k::cells! {
        Threads::thread: {
            me @ k::fragment![crate::Thread { k: k::k![crate::ExpSyntax::Join(t), tail0 @ ..], .. }],
            done @ k::fragment![crate::Thread { id: t, k: k::k![crate::StmtSyntax::Return(i), ..], .. }],
            instances0 @ ..
        },
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        Threads::thread: { k::fragment![crate::Thread { k: k::k![i, ..tail0], ..me }], ..instances0 },
        ..state
    }
}
