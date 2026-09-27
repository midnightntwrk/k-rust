//! ```toml algorithm
//! id = "kore.pattern.source"
//! name = "node-at-a-time reading of KORE patterns: order, flattening, and materialization"
//! sites = ["PatternNode::split", "PatternNode::fill", "PatternNode::into_pattern", "PatternNode::discriminant", "PatternNode::compare_scalars", "compare", "flatten_at", "materialize"]
//! variable = "p = pattern nodes the operation reaches"
//! counters = []
//! no_counter = "reading a pattern source has no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "one comparison, flattening, or materialization"
//! bound = "O(p)"
//! ```
//!
//! A [`PatternSource`] yields a pattern one node at a time: [`PatternSource::node`] returns the
//! root's variant and scalar fields together with its sub-patterns as further sources. A
//! `&Pattern` is a source, and so is anything that can build a pattern's nodes on demand, such
//! as a backend term that shares its subterms: a reader that expands only the nodes it reaches
//! never holds the whole tree.
//!
//! [`compare`] is the total order of [`Pattern`]'s `Ord`, [`flatten_at`] is
//! `Pattern::conjuncts_at`/`disjuncts_at` over sources, and
//! [`materialize`] builds the [`Pattern`] a source denotes. Each reads a node only through
//! `node`, so it gives the same answer on a source as on the pattern `materialize` builds from
//! it. Comparison stops at the first difference; flattening expands only the connectives it
//! removes; materialization expands every node once, with an explicit stack.

use std::{borrow::Cow, cmp::Ordering};

use super::ast::{Associativity, KoreString, Pattern, Sort, Symbol, Variable};

/// One pattern node: its variant and scalar fields, with each sub-pattern as an `S`.
///
/// The variants and fields are those of [`Pattern`], in the same order.
#[derive(Clone, Debug)]
pub enum PatternNode<'a, S> {
    String(Cow<'a, KoreString>),
    Variable(Cow<'a, Variable>),
    Application {
        symbol: Cow<'a, Symbol>,
        arguments: Vec<S>,
    },
    Top {
        sort: Cow<'a, Sort>,
    },
    Bottom {
        sort: Cow<'a, Sort>,
    },
    And {
        sort: Cow<'a, Sort>,
        arguments: Vec<S>,
    },
    Or {
        sort: Cow<'a, Sort>,
        arguments: Vec<S>,
    },
    Not {
        sort: Cow<'a, Sort>,
        argument: S,
    },
    Next {
        sort: Cow<'a, Sort>,
        argument: S,
    },
    Implies {
        sort: Cow<'a, Sort>,
        left: S,
        right: S,
    },
    Iff {
        sort: Cow<'a, Sort>,
        left: S,
        right: S,
    },
    Rewrites {
        sort: Cow<'a, Sort>,
        left: S,
        right: S,
    },
    Exists {
        sort: Cow<'a, Sort>,
        variable: Cow<'a, Variable>,
        body: S,
    },
    Forall {
        sort: Cow<'a, Sort>,
        variable: Cow<'a, Variable>,
        body: S,
    },
    Mu {
        variable: Cow<'a, Variable>,
        body: S,
    },
    Nu {
        variable: Cow<'a, Variable>,
        body: S,
    },
    Ceil {
        operand_sort: Cow<'a, Sort>,
        result_sort: Cow<'a, Sort>,
        argument: S,
    },
    Floor {
        operand_sort: Cow<'a, Sort>,
        result_sort: Cow<'a, Sort>,
        argument: S,
    },
    Equals {
        operand_sort: Cow<'a, Sort>,
        result_sort: Cow<'a, Sort>,
        left: S,
        right: S,
    },
    In {
        operand_sort: Cow<'a, Sort>,
        result_sort: Cow<'a, Sort>,
        left: S,
        right: S,
    },
    DomainValue {
        sort: Cow<'a, Sort>,
        value: Cow<'a, KoreString>,
    },
    AssociativeApplication {
        associativity: Associativity,
        symbol: Cow<'a, Symbol>,
        arguments: Vec<S>,
    },
}

/// A pattern that can be read one node at a time.
pub trait PatternSource<'a>: Clone {
    /// The root node, with its sub-patterns as sources.
    fn node(self) -> PatternNode<'a, Self>;

    /// True only when `self` and `other` are known to denote equal patterns without reading
    /// them; `false` claims nothing. [`compare`] skips a pair for which this holds.
    fn same_pattern(&self, _other: &Self) -> bool {
        false
    }
}

impl<'a> PatternSource<'a> for &'a Pattern {
    fn node(self) -> PatternNode<'a, Self> {
        match self {
            Pattern::String(value) => PatternNode::String(Cow::Borrowed(value)),
            Pattern::Variable(variable) => PatternNode::Variable(Cow::Borrowed(variable)),
            Pattern::Application { symbol, arguments } => PatternNode::Application {
                symbol: Cow::Borrowed(symbol),
                arguments: arguments.iter().collect(),
            },
            Pattern::Top { sort } => PatternNode::Top {
                sort: Cow::Borrowed(sort),
            },
            Pattern::Bottom { sort } => PatternNode::Bottom {
                sort: Cow::Borrowed(sort),
            },
            Pattern::And { sort, arguments } => PatternNode::And {
                sort: Cow::Borrowed(sort),
                arguments: arguments.iter().collect(),
            },
            Pattern::Or { sort, arguments } => PatternNode::Or {
                sort: Cow::Borrowed(sort),
                arguments: arguments.iter().collect(),
            },
            Pattern::Not { sort, argument } => PatternNode::Not {
                sort: Cow::Borrowed(sort),
                argument,
            },
            Pattern::Next { sort, argument } => PatternNode::Next {
                sort: Cow::Borrowed(sort),
                argument,
            },
            Pattern::Implies { sort, left, right } => PatternNode::Implies {
                sort: Cow::Borrowed(sort),
                left,
                right,
            },
            Pattern::Iff { sort, left, right } => PatternNode::Iff {
                sort: Cow::Borrowed(sort),
                left,
                right,
            },
            Pattern::Rewrites { sort, left, right } => PatternNode::Rewrites {
                sort: Cow::Borrowed(sort),
                left,
                right,
            },
            Pattern::Exists {
                sort,
                variable,
                body,
            } => PatternNode::Exists {
                sort: Cow::Borrowed(sort),
                variable: Cow::Borrowed(variable),
                body,
            },
            Pattern::Forall {
                sort,
                variable,
                body,
            } => PatternNode::Forall {
                sort: Cow::Borrowed(sort),
                variable: Cow::Borrowed(variable),
                body,
            },
            Pattern::Mu { variable, body } => PatternNode::Mu {
                variable: Cow::Borrowed(variable),
                body,
            },
            Pattern::Nu { variable, body } => PatternNode::Nu {
                variable: Cow::Borrowed(variable),
                body,
            },
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => PatternNode::Ceil {
                operand_sort: Cow::Borrowed(operand_sort),
                result_sort: Cow::Borrowed(result_sort),
                argument,
            },
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => PatternNode::Floor {
                operand_sort: Cow::Borrowed(operand_sort),
                result_sort: Cow::Borrowed(result_sort),
                argument,
            },
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => PatternNode::Equals {
                operand_sort: Cow::Borrowed(operand_sort),
                result_sort: Cow::Borrowed(result_sort),
                left,
                right,
            },
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => PatternNode::In {
                operand_sort: Cow::Borrowed(operand_sort),
                result_sort: Cow::Borrowed(result_sort),
                left,
                right,
            },
            Pattern::DomainValue { sort, value } => PatternNode::DomainValue {
                sort: Cow::Borrowed(sort),
                value: Cow::Borrowed(value),
            },
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => PatternNode::AssociativeApplication {
                associativity: *associativity,
                symbol: Cow::Borrowed(symbol),
                arguments: arguments.iter().collect(),
            },
        }
    }

    fn same_pattern(&self, other: &Self) -> bool {
        std::ptr::eq(*self, *other)
    }
}

impl<'a, S> PatternNode<'a, S> {
    /// The variant's rank in declaration order, the first key of the order.
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::String(_) => 0,
            Self::Variable(_) => 1,
            Self::Application { .. } => 2,
            Self::Top { .. } => 3,
            Self::Bottom { .. } => 4,
            Self::And { .. } => 5,
            Self::Or { .. } => 6,
            Self::Not { .. } => 7,
            Self::Next { .. } => 8,
            Self::Implies { .. } => 9,
            Self::Iff { .. } => 10,
            Self::Rewrites { .. } => 11,
            Self::Exists { .. } => 12,
            Self::Forall { .. } => 13,
            Self::Mu { .. } => 14,
            Self::Nu { .. } => 15,
            Self::Ceil { .. } => 16,
            Self::Floor { .. } => 17,
            Self::Equals { .. } => 18,
            Self::In { .. } => 19,
            Self::DomainValue { .. } => 20,
            Self::AssociativeApplication { .. } => 21,
        }
    }

    /// The scalar fields of two nodes of the same variant, compared in declaration order under
    /// their own `Ord` (strings byte-wise); `Equal` for nodes of different variants.
    pub fn compare_scalars<T>(&self, other: &PatternNode<'_, T>) -> Ordering {
        use PatternNode as N;
        match (self, other) {
            (N::String(left), N::String(right)) => left.as_ref().cmp(right.as_ref()),
            (N::Variable(left), N::Variable(right)) => left.as_ref().cmp(right.as_ref()),
            (N::Application { symbol: ls, .. }, N::Application { symbol: rs, .. }) => {
                ls.as_ref().cmp(rs.as_ref())
            }
            (N::Top { sort: ls }, N::Top { sort: rs })
            | (N::Bottom { sort: ls }, N::Bottom { sort: rs })
            | (N::And { sort: ls, .. }, N::And { sort: rs, .. })
            | (N::Or { sort: ls, .. }, N::Or { sort: rs, .. })
            | (N::Not { sort: ls, .. }, N::Not { sort: rs, .. })
            | (N::Next { sort: ls, .. }, N::Next { sort: rs, .. })
            | (N::Implies { sort: ls, .. }, N::Implies { sort: rs, .. })
            | (N::Iff { sort: ls, .. }, N::Iff { sort: rs, .. })
            | (N::Rewrites { sort: ls, .. }, N::Rewrites { sort: rs, .. }) => {
                ls.as_ref().cmp(rs.as_ref())
            }
            (
                N::Exists {
                    sort: ls,
                    variable: lv,
                    ..
                },
                N::Exists {
                    sort: rs,
                    variable: rv,
                    ..
                },
            )
            | (
                N::Forall {
                    sort: ls,
                    variable: lv,
                    ..
                },
                N::Forall {
                    sort: rs,
                    variable: rv,
                    ..
                },
            ) => ls
                .as_ref()
                .cmp(rs.as_ref())
                .then_with(|| lv.as_ref().cmp(rv.as_ref())),
            (N::Mu { variable: lv, .. }, N::Mu { variable: rv, .. })
            | (N::Nu { variable: lv, .. }, N::Nu { variable: rv, .. }) => {
                lv.as_ref().cmp(rv.as_ref())
            }
            (
                N::Ceil {
                    operand_sort: lo,
                    result_sort: lr,
                    ..
                },
                N::Ceil {
                    operand_sort: ro,
                    result_sort: rr,
                    ..
                },
            )
            | (
                N::Floor {
                    operand_sort: lo,
                    result_sort: lr,
                    ..
                },
                N::Floor {
                    operand_sort: ro,
                    result_sort: rr,
                    ..
                },
            )
            | (
                N::Equals {
                    operand_sort: lo,
                    result_sort: lr,
                    ..
                },
                N::Equals {
                    operand_sort: ro,
                    result_sort: rr,
                    ..
                },
            )
            | (
                N::In {
                    operand_sort: lo,
                    result_sort: lr,
                    ..
                },
                N::In {
                    operand_sort: ro,
                    result_sort: rr,
                    ..
                },
            ) => lo
                .as_ref()
                .cmp(ro.as_ref())
                .then_with(|| lr.as_ref().cmp(rr.as_ref())),
            (
                N::DomainValue {
                    sort: ls,
                    value: lv,
                },
                N::DomainValue {
                    sort: rs,
                    value: rv,
                },
            ) => ls
                .as_ref()
                .cmp(rs.as_ref())
                .then_with(|| lv.as_ref().cmp(rv.as_ref())),
            (
                N::AssociativeApplication {
                    associativity: la,
                    symbol: ls,
                    ..
                },
                N::AssociativeApplication {
                    associativity: ra,
                    symbol: rs,
                    ..
                },
            ) => la.cmp(ra).then_with(|| ls.as_ref().cmp(rs.as_ref())),
            _ => Ordering::Equal,
        }
    }

    /// The node without its sub-patterns (each replaced by `()`), and the sub-patterns in field
    /// order: arguments left to right, `left` before `right`, and a binder's `body`.
    pub fn split(self) -> (PatternNode<'a, ()>, Vec<S>) {
        use PatternNode as N;
        let arguments_shape = |arguments: &Vec<S>| vec![(); arguments.len()];
        match self {
            N::String(value) => (N::String(value), Vec::new()),
            N::Variable(variable) => (N::Variable(variable), Vec::new()),
            N::Application { symbol, arguments } => (
                N::Application {
                    symbol,
                    arguments: arguments_shape(&arguments),
                },
                arguments,
            ),
            N::Top { sort } => (N::Top { sort }, Vec::new()),
            N::Bottom { sort } => (N::Bottom { sort }, Vec::new()),
            N::And { sort, arguments } => (
                N::And {
                    sort,
                    arguments: arguments_shape(&arguments),
                },
                arguments,
            ),
            N::Or { sort, arguments } => (
                N::Or {
                    sort,
                    arguments: arguments_shape(&arguments),
                },
                arguments,
            ),
            N::Not { sort, argument } => (N::Not { sort, argument: () }, vec![argument]),
            N::Next { sort, argument } => (N::Next { sort, argument: () }, vec![argument]),
            N::Implies { sort, left, right } => (
                N::Implies {
                    sort,
                    left: (),
                    right: (),
                },
                vec![left, right],
            ),
            N::Iff { sort, left, right } => (
                N::Iff {
                    sort,
                    left: (),
                    right: (),
                },
                vec![left, right],
            ),
            N::Rewrites { sort, left, right } => (
                N::Rewrites {
                    sort,
                    left: (),
                    right: (),
                },
                vec![left, right],
            ),
            N::Exists {
                sort,
                variable,
                body,
            } => (
                N::Exists {
                    sort,
                    variable,
                    body: (),
                },
                vec![body],
            ),
            N::Forall {
                sort,
                variable,
                body,
            } => (
                N::Forall {
                    sort,
                    variable,
                    body: (),
                },
                vec![body],
            ),
            N::Mu { variable, body } => (N::Mu { variable, body: () }, vec![body]),
            N::Nu { variable, body } => (N::Nu { variable, body: () }, vec![body]),
            N::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => (
                N::Ceil {
                    operand_sort,
                    result_sort,
                    argument: (),
                },
                vec![argument],
            ),
            N::Floor {
                operand_sort,
                result_sort,
                argument,
            } => (
                N::Floor {
                    operand_sort,
                    result_sort,
                    argument: (),
                },
                vec![argument],
            ),
            N::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => (
                N::Equals {
                    operand_sort,
                    result_sort,
                    left: (),
                    right: (),
                },
                vec![left, right],
            ),
            N::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => (
                N::In {
                    operand_sort,
                    result_sort,
                    left: (),
                    right: (),
                },
                vec![left, right],
            ),
            N::DomainValue { sort, value } => (N::DomainValue { sort, value }, Vec::new()),
            N::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => (
                N::AssociativeApplication {
                    associativity,
                    symbol,
                    arguments: arguments_shape(&arguments),
                },
                arguments,
            ),
        }
    }
}

impl<'a> PatternNode<'a, ()> {
    /// The node with its sub-patterns taken from `children` in the order [`PatternNode::split`]
    /// lists them; `children` must hold exactly as many as the node has.
    pub fn fill<T>(self, children: Vec<T>) -> PatternNode<'a, T> {
        use PatternNode as N;
        // A node with a list of sub-patterns has no other sub-pattern: the list is `children`.
        let list = |shape: Vec<()>, children: Vec<T>| {
            assert_eq!(
                shape.len(),
                children.len(),
                "fill receives one child per sub-pattern"
            );
            children
        };
        let shape = match self {
            N::Application { symbol, arguments } => {
                return N::Application {
                    symbol,
                    arguments: list(arguments, children),
                };
            }
            N::And { sort, arguments } => {
                return N::And {
                    sort,
                    arguments: list(arguments, children),
                };
            }
            N::Or { sort, arguments } => {
                return N::Or {
                    sort,
                    arguments: list(arguments, children),
                };
            }
            N::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                return N::AssociativeApplication {
                    associativity,
                    symbol,
                    arguments: list(arguments, children),
                };
            }
            shape => shape,
        };
        let mut children = children.into_iter();
        let mut child = || {
            children
                .next()
                .expect("fill receives one child per sub-pattern")
        };
        let node = match shape {
            N::Application { .. }
            | N::And { .. }
            | N::Or { .. }
            | N::AssociativeApplication { .. } => unreachable!("lists were filled above"),
            N::String(value) => N::String(value),
            N::Variable(variable) => N::Variable(variable),
            N::Top { sort } => N::Top { sort },
            N::Bottom { sort } => N::Bottom { sort },
            N::Not { sort, .. } => N::Not {
                sort,
                argument: child(),
            },
            N::Next { sort, .. } => N::Next {
                sort,
                argument: child(),
            },
            N::Implies { sort, .. } => N::Implies {
                sort,
                left: child(),
                right: child(),
            },
            N::Iff { sort, .. } => N::Iff {
                sort,
                left: child(),
                right: child(),
            },
            N::Rewrites { sort, .. } => N::Rewrites {
                sort,
                left: child(),
                right: child(),
            },
            N::Exists { sort, variable, .. } => N::Exists {
                sort,
                variable,
                body: child(),
            },
            N::Forall { sort, variable, .. } => N::Forall {
                sort,
                variable,
                body: child(),
            },
            N::Mu { variable, .. } => N::Mu {
                variable,
                body: child(),
            },
            N::Nu { variable, .. } => N::Nu {
                variable,
                body: child(),
            },
            N::Ceil {
                operand_sort,
                result_sort,
                ..
            } => N::Ceil {
                operand_sort,
                result_sort,
                argument: child(),
            },
            N::Floor {
                operand_sort,
                result_sort,
                ..
            } => N::Floor {
                operand_sort,
                result_sort,
                argument: child(),
            },
            N::Equals {
                operand_sort,
                result_sort,
                ..
            } => N::Equals {
                operand_sort,
                result_sort,
                left: child(),
                right: child(),
            },
            N::In {
                operand_sort,
                result_sort,
                ..
            } => N::In {
                operand_sort,
                result_sort,
                left: child(),
                right: child(),
            },
            N::DomainValue { sort, value } => N::DomainValue { sort, value },
        };
        debug_assert!(children.next().is_none(), "fill uses every child");
        node
    }
}

impl PatternNode<'_, Pattern> {
    /// The pattern with this node at its root.
    pub fn into_pattern(self) -> Pattern {
        use PatternNode as N;
        match self {
            N::String(value) => Pattern::String(value.into_owned()),
            N::Variable(variable) => Pattern::Variable(variable.into_owned()),
            N::Application { symbol, arguments } => Pattern::Application {
                symbol: symbol.into_owned(),
                arguments,
            },
            N::Top { sort } => Pattern::Top {
                sort: sort.into_owned(),
            },
            N::Bottom { sort } => Pattern::Bottom {
                sort: sort.into_owned(),
            },
            N::And { sort, arguments } => Pattern::And {
                sort: sort.into_owned(),
                arguments,
            },
            N::Or { sort, arguments } => Pattern::Or {
                sort: sort.into_owned(),
                arguments,
            },
            N::Not { sort, argument } => Pattern::Not {
                sort: sort.into_owned(),
                argument: Box::new(argument),
            },
            N::Next { sort, argument } => Pattern::Next {
                sort: sort.into_owned(),
                argument: Box::new(argument),
            },
            N::Implies { sort, left, right } => Pattern::Implies {
                sort: sort.into_owned(),
                left: Box::new(left),
                right: Box::new(right),
            },
            N::Iff { sort, left, right } => Pattern::Iff {
                sort: sort.into_owned(),
                left: Box::new(left),
                right: Box::new(right),
            },
            N::Rewrites { sort, left, right } => Pattern::Rewrites {
                sort: sort.into_owned(),
                left: Box::new(left),
                right: Box::new(right),
            },
            N::Exists {
                sort,
                variable,
                body,
            } => Pattern::Exists {
                sort: sort.into_owned(),
                variable: Box::new(variable.into_owned()),
                body: Box::new(body),
            },
            N::Forall {
                sort,
                variable,
                body,
            } => Pattern::Forall {
                sort: sort.into_owned(),
                variable: Box::new(variable.into_owned()),
                body: Box::new(body),
            },
            N::Mu { variable, body } => Pattern::Mu {
                variable: Box::new(variable.into_owned()),
                body: Box::new(body),
            },
            N::Nu { variable, body } => Pattern::Nu {
                variable: Box::new(variable.into_owned()),
                body: Box::new(body),
            },
            N::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => Pattern::Ceil {
                operand_sort: Box::new(operand_sort.into_owned()),
                result_sort: result_sort.into_owned(),
                argument: Box::new(argument),
            },
            N::Floor {
                operand_sort,
                result_sort,
                argument,
            } => Pattern::Floor {
                operand_sort: Box::new(operand_sort.into_owned()),
                result_sort: result_sort.into_owned(),
                argument: Box::new(argument),
            },
            N::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => Pattern::Equals {
                operand_sort: Box::new(operand_sort.into_owned()),
                result_sort: result_sort.into_owned(),
                left: Box::new(left),
                right: Box::new(right),
            },
            N::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => Pattern::In {
                operand_sort: Box::new(operand_sort.into_owned()),
                result_sort: result_sort.into_owned(),
                left: Box::new(left),
                right: Box::new(right),
            },
            N::DomainValue { sort, value } => Pattern::DomainValue {
                sort: sort.into_owned(),
                value: value.into_owned(),
            },
            N::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => Pattern::AssociativeApplication {
                associativity,
                symbol: symbol.into_owned(),
                arguments,
            },
        }
    }
}

/// Total order on patterns given by sources: the order of [`Pattern`]'s `Ord`. That order is
/// variant rank in declaration order, then the variant's scalar fields in declaration order under
/// their own `Ord` (strings byte-wise), then sub-patterns left to right, then their count, which
/// is lexicographic order on the preorder sequence of (rank, scalars) with the child count
/// breaking ties between a node and a longer sibling list. This function walks the same
/// sequence with an explicit work list: [`PatternNode::discriminant`] is `Pattern`'s rank,
/// [`PatternNode::compare_scalars`] compares the fields `Pattern`'s order compares, in the same
/// order, and [`PatternNode::split`] lists the sub-patterns in the order `walk::children` does.
///
/// It reads each node only through [`PatternSource::node`], so `compare(a, b)` equals
/// `materialize(a).cmp(&materialize(b))`: the node of `&materialize(s)` has the variant and
/// scalars of `s.node()`, with the materialized sub-patterns. A pair for which
/// [`PatternSource::same_pattern`] holds is equal and is not read.
pub fn compare<'a, S: PatternSource<'a>>(left: S, right: S) -> Ordering {
    enum Step<S> {
        Compare(S, S),
        PrefixLength(Ordering),
    }

    let mut work = vec![Step::Compare(left, right)];
    // Invariant: every `Compare` popped so far found its two nodes equal in rank and scalars (or skipped as the same pattern), and `work` holds, in comparison order, the unvisited child pairs of the open pairs and each open pair's `PrefixLength`; each `Compare` pairs the nodes at one position common to both sides and is pushed once, so `work` empties.
    while let Some(step) = work.pop() {
        let (left, right) = match step {
            Step::PrefixLength(ordering) => {
                if !ordering.is_eq() {
                    return ordering;
                }
                continue;
            }
            Step::Compare(left, right) => (left, right),
        };
        if left.same_pattern(&right) {
            continue;
        }
        let (left, right) = (left.node(), right.node());
        let ordering = left
            .discriminant()
            .cmp(&right.discriminant())
            .then_with(|| left.compare_scalars(&right));
        if !ordering.is_eq() {
            return ordering;
        }
        let (_, left_children) = left.split();
        let (_, right_children) = right.split();
        work.push(Step::PrefixLength(
            left_children.len().cmp(&right_children.len()),
        ));
        work.extend(
            left_children
                .into_iter()
                .zip(right_children)
                .rev()
                .map(|(left, right)| Step::Compare(left, right)),
        );
    }
    Ordering::Equal
}

/// The operands of `root` as a conjunction (`conjunction`) or disjunction at `sort`, as
/// `Pattern::conjuncts_at`/`disjuncts_at` give them: nested `\and` (`\or`) nodes at `sort` are
/// flattened left to right and their unit `\top` (`\bottom`) at `sort` is dropped. Only the
/// nodes it removes are expanded; every other operand is returned as the source it was.
pub fn flatten_at<'a, S: PatternSource<'a>>(root: S, sort: &Sort, conjunction: bool) -> Vec<S> {
    let mut result = Vec::new();
    let mut work = vec![root];
    // Invariant: `result` holds, left to right, the popped operands that are neither a matching `\and`/`\or` at `sort` nor its unit, and `work` holds the unvisited operands in reverse order; each operand is popped once.
    while let Some(source) = work.pop() {
        match source.clone().node() {
            PatternNode::And {
                sort: node_sort,
                arguments,
            } if conjunction && node_sort.as_ref() == sort => {
                work.extend(arguments.into_iter().rev());
            }
            PatternNode::Or {
                sort: node_sort,
                arguments,
            } if !conjunction && node_sort.as_ref() == sort => {
                work.extend(arguments.into_iter().rev());
            }
            PatternNode::Top { sort: node_sort } if conjunction && node_sort.as_ref() == sort => {}
            PatternNode::Bottom { sort: node_sort }
                if !conjunction && node_sort.as_ref() == sort => {}
            _ => result.push(source),
        }
    }
    result
}

/// The pattern `root` denotes, built with an explicit stack so that depth is not limited by the
/// call stack. Each node is read once through [`PatternSource::node`].
pub fn materialize<'a, S: PatternSource<'a>>(root: S) -> Pattern {
    struct Frame<'a, S> {
        shape: PatternNode<'a, ()>,
        children: std::vec::IntoIter<S>,
        built: Vec<Pattern>,
    }

    impl<'a, S: PatternSource<'a>> Frame<'a, S> {
        fn new(source: S) -> Self {
            let (shape, children) = source.node().split();
            Self {
                built: Vec::with_capacity(children.len()),
                shape,
                children: children.into_iter(),
            }
        }
    }

    let mut stack = vec![Frame::new(root)];
    // Invariant: `stack` holds one frame per node on the path from `root` to the current node, and each frame's `built` holds its finished sub-patterns in order; each node's frame is pushed and popped once.
    loop {
        let frame = stack
            .last_mut()
            .expect("the root frame remains until return");
        if let Some(child) = frame.children.next() {
            stack.push(Frame::new(child));
            continue;
        }
        let frame = stack.pop().expect("the completed frame is present");
        let pattern = frame.shape.fill(frame.built).into_pattern();
        match stack.last_mut() {
            Some(parent) => parent.built.push(pattern),
            None => return pattern,
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::kore::{parser::parse_pattern, printer::tests::streaming::pattern};

    const SOURCES: [&str; 22] = [
        "\"A\"",
        "A:A{}",
        "A{}(\\dv{A{}}(\"A\"), A:A{})",
        "\\top{A{}}()",
        "\\bottom{A{}}()",
        "\\and{A{}}(\\top{A{}}(), \\bottom{A{}}())",
        "\\or{A{}}(\\top{A{}}(), \\bottom{A{}}())",
        "\\not{A{}}(\\top{A{}}())",
        "\\next{A{}}(\\top{A{}}())",
        "\\implies{A{}}(\\top{A{}}(), \\bottom{A{}}())",
        "\\iff{A{}}(\\top{A{}}(), \\bottom{A{}}())",
        "\\rewrites{A{}}(A{}(), A:A{})",
        "\\exists{A{}}(A:A{}, A{}())",
        "\\forall{A{}}(A:A{}, A{}())",
        "\\mu{}(@A:A{}, A{}())",
        "\\nu{}(@A:A{}, A{}())",
        "\\ceil{A{}, A{}}(A{}())",
        "\\floor{A{}, A{}}(A{}())",
        "\\equals{A{}, A{}}(A{}(), A{}())",
        "\\in{A{}, A{}}(A{}(), A{}())",
        "\\dv{A{}}(\"A\")",
        "\\left-assoc{}(A{}(A:A{}, A:A{}))",
    ];

    /// Materializing a `&Pattern` source rebuilds the pattern, for every variant.
    #[test]
    fn materialize_rebuilds_every_variant() {
        for source in SOURCES {
            let pattern = parse_pattern(source).unwrap();
            assert_eq!(materialize(&pattern), pattern, "{source}");
            assert_eq!(materialize(&pattern).to_string(), pattern.to_string());
        }
    }

    /// The node rank of each variant is its declaration rank.
    #[test]
    fn node_rank_follows_declaration_order() {
        let ranks = SOURCES
            .into_iter()
            .map(|source| parse_pattern(source).unwrap())
            .map(|pattern| (&pattern).node().discriminant())
            .collect::<Vec<_>>();
        assert_eq!(ranks, (0..22).collect::<Vec<u8>>());
    }

    #[test]
    fn flatten_matches_the_owned_flattening() {
        let pattern = parse_pattern(
            "\\and{A{}}(\\and{A{}}(a{}(), \\top{A{}}()), \\or{A{}}(b{}(), \\and{B{}}(c{}(), d{}())))",
        )
        .unwrap();
        let sort = Sort::Application {
            name: "A".into(),
            arguments: Vec::new(),
        };
        let flattened = flatten_at(&pattern, &sort, true)
            .into_iter()
            .map(materialize)
            .collect::<Vec<_>>();
        assert_eq!(flattened, pattern.clone().into_conjuncts_at(&sort));
        let flattened = flatten_at(&pattern, &sort, false)
            .into_iter()
            .map(materialize)
            .collect::<Vec<_>>();
        assert_eq!(flattened, pattern.into_disjuncts_at(&sort));
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(512))]

        /// `compare` on `&Pattern` is `Pattern`'s order, on unrelated patterns and on patterns
        /// that share a long prefix (a common left sibling under one root) and differ after it.
        #[test]
        fn compare_is_the_pattern_order(
            left in pattern(),
            right in pattern(),
            shared in pattern(),
        ) {
            prop_assert_eq!(compare(&left, &right), left.cmp(&right));
            prop_assert_eq!(compare(&left, &left.clone()), Ordering::Equal);
            let root = |arguments: Vec<Pattern>| Pattern::Application {
                symbol: Symbol {
                    name: "root".into(),
                    sort_parameters: Vec::new(),
                },
                arguments,
            };
            let (short, left, right) = (
                root(vec![shared.clone()]),
                root(vec![shared.clone(), left]),
                root(vec![shared, right]),
            );
            prop_assert_eq!(compare(&left, &right), left.cmp(&right));
            prop_assert_eq!(compare(&short, &left), short.cmp(&left));
            prop_assert_eq!(compare(&left, &short), left.cmp(&short));
        }

        /// Materializing a `&Pattern` source rebuilds the pattern.
        #[test]
        fn materialize_rebuilds_generated_patterns(pattern in pattern()) {
            prop_assert_eq!(materialize(&pattern), pattern);
        }
    }
}
