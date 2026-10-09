//! Syntax tree for textual KORE.

use std::{fmt, sync::Arc};

use smallvec::SmallVec;

/// The code points of a KORE string literal, stored as `string::LiteralEncoding` says: one byte
/// per code point (the byte's value) for a domain value of `SortBytes`, and the UTF-8 encoding
/// for every other literal. Each value has exactly one payload, so equal payloads are equal
/// values. Every reader (text, JSON and binary KORE) stores a literal so; console input becomes a
/// string through `string::text_from_bytes`.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KoreString(Arc<[u8]>);

impl KoreString {
    pub fn from_bytes(value: impl Into<Arc<[u8]>>) -> Self {
        Self(value.into())
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn as_utf8(&self) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(&self.0)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Debug for KoreString {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.as_utf8() {
            Ok(value) => fmt::Debug::fmt(value, formatter),
            Err(_) => formatter
                .debug_tuple("KoreString")
                .field(&self.0.as_ref())
                .finish(),
        }
    }
}

impl From<&str> for KoreString {
    fn from(value: &str) -> Self {
        Self::from_bytes(Arc::<[u8]>::from(value.as_bytes()))
    }
}

impl From<String> for KoreString {
    fn from(value: String) -> Self {
        Self::from_bytes(Arc::<[u8]>::from(value.into_bytes()))
    }
}

impl From<Vec<u8>> for KoreString {
    fn from(value: Vec<u8>) -> Self {
        Self::from_bytes(Arc::<[u8]>::from(value))
    }
}

impl From<Arc<[u8]>> for KoreString {
    fn from(value: Arc<[u8]>) -> Self {
        Self::from_bytes(value)
    }
}

impl From<Arc<str>> for KoreString {
    fn from(value: Arc<str>) -> Self {
        Self::from_bytes(Arc::<[u8]>::from(value.as_bytes()))
    }
}

impl PartialEq<str> for KoreString {
    fn eq(&self, other: &str) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl PartialEq<&str> for KoreString {
    fn eq(&self, other: &&str) -> bool {
        self == *other
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub attributes: Attributes,
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    pub name: String,
    pub sentences: Vec<Sentence>,
    pub attributes: Attributes,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sentence {
    Import {
        module: String,
        attributes: Attributes,
    },
    SortDeclaration {
        hooked: bool,
        name: String,
        parameters: Vec<String>,
        attributes: Attributes,
    },
    SymbolDeclaration {
        hooked: bool,
        symbol: Symbol,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
        attributes: Attributes,
    },
    AliasDeclaration {
        alias: Symbol,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
        attributes: Attributes,
    },
    Axiom {
        parameters: Vec<String>,
        pattern: Box<Pattern>,
        attributes: Attributes,
    },
    Claim {
        parameters: Vec<String>,
        pattern: Box<Pattern>,
        attributes: Attributes,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Attributes(pub Vec<Pattern>);

pub enum Sort {
    Variable(String),
    Application { name: String, arguments: Vec<Sort> },
}

impl Sort {
    /// The sort's name and, for an application, its arguments.
    ///
    /// `Sort` implements `Drop`, so a by-value pattern cannot move its fields out; this takes
    /// them instead.
    pub fn into_parts(mut self) -> (String, Option<Vec<Sort>>) {
        match &mut self {
            Sort::Variable(name) => (std::mem::take(name), None),
            Sort::Application { name, arguments } => {
                (std::mem::take(name), Some(std::mem::take(arguments)))
            }
        }
    }

    /// Whether the sort has no sort arguments that themselves have arguments, so its derived
    /// structural operations would recurse at most one level.
    fn is_shallow(&self) -> bool {
        match self {
            Sort::Variable(_) => true,
            Sort::Application { arguments, .. } => arguments.iter().all(|argument| {
                matches!(argument, Sort::Variable(_))
                    || matches!(argument, Sort::Application { arguments, .. } if arguments.is_empty())
            }),
        }
    }

    /// The variant's rank in declaration order, the first key of [`Ord`].
    const fn discriminant(&self) -> u8 {
        match self {
            Sort::Variable(_) => 0,
            Sort::Application { .. } => 1,
        }
    }

    fn arguments(&self) -> &[Sort] {
        match self {
            Sort::Variable(_) => &[],
            Sort::Application { arguments, .. } => arguments,
        }
    }
}

/// Levels of a sort that [`Clone`], [`PartialEq`], and [`Ord`] handle by recursion, which
/// allocates nothing; the subsorts below them are handled with explicit work lists. The sorts of
/// K definitions are a few levels deep, so they never reach the work lists, while the recursion
/// takes a bounded amount of stack whatever the depth of the sort.
const SORT_RECURSION_LIMIT: usize = 32;

impl Clone for Sort {
    fn clone(&self) -> Self {
        self.clone_from_depth(0)
    }
}

impl Sort {
    /// A copy of the sort, which is `depth` levels below the sort being copied.
    fn clone_from_depth(&self, depth: usize) -> Self {
        match self {
            Sort::Variable(name) => Sort::Variable(name.clone()),
            Sort::Application { .. } if depth >= SORT_RECURSION_LIMIT => self.clone_iteratively(),
            Sort::Application { name, arguments } => Sort::Application {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| argument.clone_from_depth(depth + 1))
                    .collect(),
            },
        }
    }

    /// A copy of the sort, built with an explicit work list.
    fn clone_iteratively(&self) -> Self {
        struct Frame<'a> {
            name: &'a str,
            arguments: &'a [Sort],
            built: Vec<Sort>,
        }

        let Sort::Application { name, arguments } = self else {
            let Sort::Variable(name) = self else {
                unreachable!()
            };
            return Sort::Variable(name.clone());
        };
        let mut stack: SmallVec<[Frame<'_>; 4]> = smallvec::smallvec![Frame {
            name,
            arguments,
            built: Vec::with_capacity(arguments.len()),
        }];
        // Invariant: `stack` holds one frame per application on the path from `self` to the sort being copied, and each frame's `built` holds the copies of its first `built.len()` arguments; every application is pushed and popped once, so the loop returns after O(|self|) iterations.
        loop {
            let frame = stack
                .last_mut()
                .expect("the root frame remains until return");
            if let Some(argument) = frame.arguments.get(frame.built.len()) {
                match argument {
                    Sort::Variable(name) => frame.built.push(Sort::Variable(name.clone())),
                    Sort::Application { name, arguments } => stack.push(Frame {
                        name,
                        arguments,
                        built: Vec::with_capacity(arguments.len()),
                    }),
                }
                continue;
            }
            let frame = stack.pop().expect("the completed frame is present");
            let sort = Sort::Application {
                name: frame.name.to_owned(),
                arguments: frame.built,
            };
            match stack.last_mut() {
                Some(parent) => parent.built.push(sort),
                None => return sort,
            }
        }
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Self) -> bool {
        self.eq_from_depth(other, 0)
    }
}

impl Sort {
    /// Whether the sorts are equal, `depth` levels below the sorts being compared.
    fn eq_from_depth(&self, other: &Self, depth: usize) -> bool {
        match (self, other) {
            (Sort::Variable(left), Sort::Variable(right)) => left == right,
            (
                Sort::Application {
                    name: left_name,
                    arguments: left,
                },
                Sort::Application {
                    name: right_name,
                    arguments: right,
                },
            ) => {
                if left_name != right_name || left.len() != right.len() {
                    false
                } else if depth >= SORT_RECURSION_LIMIT {
                    self.cmp_iteratively(other).is_eq()
                } else {
                    left.iter()
                        .zip(right)
                        .all(|(left, right)| left.eq_from_depth(right, depth + 1))
                }
            }
            (Sort::Variable(_), Sort::Application { .. })
            | (Sort::Application { .. }, Sort::Variable(_)) => false,
        }
    }

    /// [`Ord::cmp`], `depth` levels below the sorts being compared.
    fn cmp_from_depth(&self, other: &Self, depth: usize) -> std::cmp::Ordering {
        if depth >= SORT_RECURSION_LIMIT {
            return self.cmp_iteratively(other);
        }
        match (self, other) {
            (Sort::Variable(left), Sort::Variable(right)) => left.cmp(right),
            (
                Sort::Application {
                    name: left_name,
                    arguments: left,
                },
                Sort::Application {
                    name: right_name,
                    arguments: right,
                },
            ) => left_name.cmp(right_name).then_with(|| {
                for (left, right) in left.iter().zip(right) {
                    let ordering = left.cmp_from_depth(right, depth + 1);
                    if ordering.is_ne() {
                        return ordering;
                    }
                }
                left.len().cmp(&right.len())
            }),
            (Sort::Variable(_), Sort::Application { .. }) => std::cmp::Ordering::Less,
            (Sort::Application { .. }, Sort::Variable(_)) => std::cmp::Ordering::Greater,
        }
    }
}

impl Eq for Sort {}

impl PartialOrd for Sort {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Total order on sorts: variables before applications, variables by name, applications by
/// name, then arguments left to right, then argument count. This is the order
/// `#[derive(Ord)]` would give; it is written out because a derived comparison recurses once
/// per sort level, while this one recurses only `SORT_RECURSION_LIMIT` levels and compares
/// the subsorts below them with an explicit work list.
impl Ord for Sort {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cmp_from_depth(other, 0)
    }
}

impl Sort {
    /// [`Ord::cmp`] with an explicit work list.
    fn cmp_iteratively(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        enum Step<'a> {
            Compare(&'a Sort, &'a Sort),
            PrefixLength(Ordering),
        }

        let mut work: SmallVec<[Step<'_>; 8]> = smallvec::smallvec![Step::Compare(self, other)];
        // Invariant: every `Compare` popped so far found its two sorts equal in rank and name, and `work` holds, in comparison order, the unvisited argument pairs of the open pairs and each open pair's `PrefixLength`; each `Compare` pairs the sorts at one position common to `self` and `other` and is pushed once, so `work` empties.
        while let Some(step) = work.pop() {
            let (left, right) = match step {
                Step::Compare(left, right) => (left, right),
                Step::PrefixLength(ordering) if ordering.is_eq() => continue,
                Step::PrefixLength(ordering) => return ordering,
            };
            let ordering = left
                .discriminant()
                .cmp(&right.discriminant())
                .then_with(|| match (left, right) {
                    (Sort::Variable(left), Sort::Variable(right))
                    | (
                        Sort::Application { name: left, .. },
                        Sort::Application { name: right, .. },
                    ) => left.cmp(right),
                    _ => Ordering::Equal,
                });
            if !ordering.is_eq() {
                return ordering;
            }
            let (left, right) = (left.arguments(), right.arguments());
            work.push(Step::PrefixLength(left.len().cmp(&right.len())));
            for (left, right) in left.iter().zip(right).rev() {
                work.push(Step::Compare(left, right));
            }
        }
        Ordering::Equal
    }
}

impl Drop for Sort {
    fn drop(&mut self) {
        if self.is_shallow() {
            return;
        }
        let Sort::Application { arguments, .. } = self else {
            return;
        };
        let mut work = std::mem::take(arguments);
        // Invariant: `work` holds the detached sorts whose arguments are still attached; each pop detaches one sort's arguments into `work`, so each sort is popped once and is dropped with no arguments left.
        while let Some(mut sort) = work.pop() {
            if let Sort::Application { arguments, .. } = &mut sort {
                work.append(arguments);
            }
        }
    }
}

/// The output of `#[derive(Debug)]`, written with an explicit work list as for [`Pattern`].
impl fmt::Debug for Sort {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug::write(formatter, debug::Task::Sort(self))
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Symbol {
    pub name: String,
    pub sort_parameters: Vec<Sort>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum VariableKind {
    Element,
    Set,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Variable {
    pub kind: VariableKind,
    pub name: String,
    pub sort: Sort,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Associativity {
    Left,
    Right,
}

pub enum Pattern {
    String(KoreString),
    Variable(Variable),
    Application {
        symbol: Symbol,
        arguments: Vec<Pattern>,
    },
    Top {
        sort: Sort,
    },
    Bottom {
        sort: Sort,
    },
    And {
        sort: Sort,
        arguments: Vec<Pattern>,
    },
    Or {
        sort: Sort,
        arguments: Vec<Pattern>,
    },
    Not {
        sort: Sort,
        argument: Box<Pattern>,
    },
    Next {
        sort: Sort,
        argument: Box<Pattern>,
    },
    Implies {
        sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    Iff {
        sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    Rewrites {
        sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    Exists {
        sort: Sort,
        variable: Box<Variable>,
        body: Box<Pattern>,
    },
    Forall {
        sort: Sort,
        variable: Box<Variable>,
        body: Box<Pattern>,
    },
    Mu {
        variable: Box<Variable>,
        body: Box<Pattern>,
    },
    Nu {
        variable: Box<Variable>,
        body: Box<Pattern>,
    },
    Ceil {
        operand_sort: Box<Sort>,
        result_sort: Sort,
        argument: Box<Pattern>,
    },
    Floor {
        operand_sort: Box<Sort>,
        result_sort: Sort,
        argument: Box<Pattern>,
    },
    Equals {
        operand_sort: Box<Sort>,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    In {
        operand_sort: Box<Sort>,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    DomainValue {
        sort: Sort,
        value: KoreString,
    },
    AssociativeApplication {
        associativity: Associativity,
        symbol: Symbol,
        arguments: Vec<Pattern>,
    },
}

// Invariant: infrequent quantified and two-sort payloads are boxed; the inline
// Variable and AssociativeApplication variants bound the size of a pattern node.
const _: () = assert!(std::mem::size_of::<Pattern>() <= 88);

impl Clone for Pattern {
    fn clone(&self) -> Self {
        super::walk::rebuild(self, super::walk::clone_node)
    }
}

impl PartialEq for Pattern {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for Pattern {}

impl Drop for Pattern {
    fn drop(&mut self) {
        let mut work = super::walk::take_children(self);
        // Invariant: `work` holds the detached subpatterns whose children are still attached; each pop detaches one node's children into `work`, so each node is popped once and is dropped after its children are detached.
        while let Some(mut child) = work.pop() {
            work.extend(super::walk::take_children(&mut child));
        }
    }
}

/// The output of `#[derive(Debug)]`, in both the compact and the alternate (`{:#?}`) form,
/// written with an explicit work list: a derived implementation recurses through `Box<Pattern>`
/// and overflows the stack on the deep patterns this crate supports (`deep.rs`).
impl fmt::Debug for Pattern {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug::write(formatter, debug::Task::Pattern(self))
    }
}

impl PartialOrd for Pattern {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Total order on patterns: variant rank in declaration order, then the variant's scalar fields
/// in declaration order under their own `Ord` (strings byte-wise), then children left to right,
/// then child count. This is the order `#[derive(Ord)]` would give; it is written out with an
/// explicit work list because a derived comparison recurses through `Box<Pattern>` and overflows
/// the stack on the deep patterns this crate supports (`deep.rs`). `PartialEq` goes through
/// `cmp`, so equality is structural: two patterns are equal iff their printed KORE is equal.
impl Ord for Pattern {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use Pattern::*;
        use std::cmp::Ordering;

        fn scalars(left: &Pattern, right: &Pattern) -> Ordering {
            match (left, right) {
                (String(left), String(right)) => left.cmp(right),
                (Variable(left), Variable(right)) => left.cmp(right),
                (Application { symbol: ls, .. }, Application { symbol: rs, .. }) => ls.cmp(rs),
                (Top { sort: left }, Top { sort: right })
                | (Bottom { sort: left }, Bottom { sort: right }) => left.cmp(right),
                (And { sort: ls, .. }, And { sort: rs, .. })
                | (Or { sort: ls, .. }, Or { sort: rs, .. }) => ls.cmp(rs),
                (Not { sort: ls, .. }, Not { sort: rs, .. })
                | (Next { sort: ls, .. }, Next { sort: rs, .. }) => ls.cmp(rs),
                (Implies { sort: ls, .. }, Implies { sort: rs, .. })
                | (Iff { sort: ls, .. }, Iff { sort: rs, .. })
                | (Rewrites { sort: ls, .. }, Rewrites { sort: rs, .. }) => ls.cmp(rs),
                (
                    Exists {
                        sort: ls,
                        variable: lv,
                        ..
                    },
                    Exists {
                        sort: rs,
                        variable: rv,
                        ..
                    },
                )
                | (
                    Forall {
                        sort: ls,
                        variable: lv,
                        ..
                    },
                    Forall {
                        sort: rs,
                        variable: rv,
                        ..
                    },
                ) => ls.cmp(rs).then_with(|| lv.cmp(rv)),
                (Mu { variable: lv, .. }, Mu { variable: rv, .. })
                | (Nu { variable: lv, .. }, Nu { variable: rv, .. }) => lv.cmp(rv),
                (
                    Ceil {
                        operand_sort: lo,
                        result_sort: lr,
                        ..
                    },
                    Ceil {
                        operand_sort: ro,
                        result_sort: rr,
                        ..
                    },
                )
                | (
                    Floor {
                        operand_sort: lo,
                        result_sort: lr,
                        ..
                    },
                    Floor {
                        operand_sort: ro,
                        result_sort: rr,
                        ..
                    },
                ) => lo.cmp(ro).then_with(|| lr.cmp(rr)),
                (
                    Equals {
                        operand_sort: lo,
                        result_sort: lr,
                        ..
                    },
                    Equals {
                        operand_sort: ro,
                        result_sort: rr,
                        ..
                    },
                )
                | (
                    In {
                        operand_sort: lo,
                        result_sort: lr,
                        ..
                    },
                    In {
                        operand_sort: ro,
                        result_sort: rr,
                        ..
                    },
                ) => lo.cmp(ro).then_with(|| lr.cmp(rr)),
                (
                    DomainValue {
                        sort: ls,
                        value: lv,
                    },
                    DomainValue {
                        sort: rs,
                        value: rv,
                    },
                ) => ls.cmp(rs).then_with(|| lv.cmp(rv)),
                (
                    AssociativeApplication {
                        associativity: la,
                        symbol: ls,
                        ..
                    },
                    AssociativeApplication {
                        associativity: ra,
                        symbol: rs,
                        ..
                    },
                ) => la.cmp(ra).then_with(|| ls.cmp(rs)),
                _ => Ordering::Equal,
            }
        }

        enum Step<'a> {
            Compare(&'a Pattern, &'a Pattern),
            PrefixLength(Ordering),
        }

        let mut work = vec![Step::Compare(self, other)];
        // Invariant: every `Compare` popped so far found its two nodes equal in rank and scalars, and `work` holds, in comparison order, the unvisited child pairs of the open pairs and each open pair's `PrefixLength`; each `Compare` pairs the nodes at one position common to `self` and `other` and is pushed once, so `work` empties.
        while let Some(step) = work.pop() {
            let Step::Compare(left, right) = step else {
                let Step::PrefixLength(ordering) = step else {
                    unreachable!()
                };
                if !ordering.is_eq() {
                    return ordering;
                }
                continue;
            };

            let ordering = left
                .discriminant()
                .cmp(&right.discriminant())
                .then_with(|| scalars(left, right));
            if !ordering.is_eq() {
                return ordering;
            }

            let (left_children, right_children) =
                (super::walk::children(left), super::walk::children(right));
            let common = left_children.len().min(right_children.len());
            work.push(Step::PrefixLength(
                left_children.len().cmp(&right_children.len()),
            ));
            for index in (0..common).rev() {
                work.push(Step::Compare(left_children[index], right_children[index]));
            }
        }
        Ordering::Equal
    }
}

impl Pattern {
    /// The variant's rank in declaration order, the first key of [`Ord`].
    const fn discriminant(&self) -> u8 {
        match self {
            Pattern::String(_) => 0,
            Pattern::Variable(_) => 1,
            Pattern::Application { .. } => 2,
            Pattern::Top { .. } => 3,
            Pattern::Bottom { .. } => 4,
            Pattern::And { .. } => 5,
            Pattern::Or { .. } => 6,
            Pattern::Not { .. } => 7,
            Pattern::Next { .. } => 8,
            Pattern::Implies { .. } => 9,
            Pattern::Iff { .. } => 10,
            Pattern::Rewrites { .. } => 11,
            Pattern::Exists { .. } => 12,
            Pattern::Forall { .. } => 13,
            Pattern::Mu { .. } => 14,
            Pattern::Nu { .. } => 15,
            Pattern::Ceil { .. } => 16,
            Pattern::Floor { .. } => 17,
            Pattern::Equals { .. } => 18,
            Pattern::In { .. } => 19,
            Pattern::DomainValue { .. } => 20,
            Pattern::AssociativeApplication { .. } => 21,
        }
    }
}

/// The derived `Debug` rendering of [`Pattern`], written with an explicit work list.
///
/// `#[derive(Debug)]` writes a struct variant as `Name { field: value, .. }`, a tuple variant as
/// `Name(value)` and a vector as `[value, ..]`; the alternate form puts each field or element on
/// its own line, indented four spaces per level of nesting, followed by a comma. This module
/// writes the same text. Values that are not patterns are written through their own `Debug`
/// at the current indentation.
mod debug {
    use std::fmt::{self, Write as _};

    use smallvec::SmallVec;

    use super::{Pattern, Sort};

    pub(super) enum Task<'a> {
        Pattern(&'a Pattern),
        Patterns(&'a [Pattern]),
        Sort(&'a Sort),
        Sorts(&'a [Sort]),
        Leaf(&'a dyn fmt::Debug),
        Text(&'static str),
        Newline,
        Indent,
        Dedent,
    }

    /// Writes through a formatter, indenting every line that follows a newline by the current
    /// nesting level, as the standard library's alternate debug builders do.
    struct Indented<'a, 'f> {
        formatter: &'a mut fmt::Formatter<'f>,
        level: usize,
        on_newline: bool,
    }

    impl fmt::Write for Indented<'_, '_> {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            for line in text.split_inclusive('\n') {
                if self.on_newline {
                    for _ in 0..self.level {
                        self.formatter.write_str("    ")?;
                    }
                }
                self.on_newline = line.ends_with('\n');
                self.formatter.write_str(line)?;
            }
            Ok(())
        }
    }

    type Fields<'a> = SmallVec<[(&'static str, Task<'a>); 4]>;

    fn push_struct<'a>(
        work: &mut Vec<Task<'a>>,
        alternate: bool,
        name: &'static str,
        fields: Fields<'a>,
    ) {
        let mut tasks = Vec::with_capacity(4 * fields.len() + 4);
        tasks.push(Task::Text(name));
        if alternate {
            tasks.push(Task::Text(" {"));
            tasks.push(Task::Indent);
            for (field, value) in fields {
                tasks.extend([Task::Newline, Task::Text(field), Task::Text(": "), value]);
                tasks.push(Task::Text(","));
            }
            tasks.extend([Task::Dedent, Task::Newline, Task::Text("}")]);
        } else {
            tasks.push(Task::Text(" { "));
            for (index, (field, value)) in fields.into_iter().enumerate() {
                if index != 0 {
                    tasks.push(Task::Text(", "));
                }
                tasks.extend([Task::Text(field), Task::Text(": "), value]);
            }
            tasks.push(Task::Text(" }"));
        }
        work.extend(tasks.into_iter().rev());
    }

    fn push_tuple<'a>(
        work: &mut Vec<Task<'a>>,
        alternate: bool,
        name: &'static str,
        value: Task<'a>,
    ) {
        if alternate {
            work.extend([
                Task::Text(")"),
                Task::Newline,
                Task::Dedent,
                Task::Text(","),
                value,
                Task::Newline,
                Task::Indent,
                Task::Text("("),
                Task::Text(name),
            ]);
        } else {
            work.extend([Task::Text(")"), value, Task::Text("("), Task::Text(name)]);
        }
    }

    fn push_list<'a>(
        work: &mut Vec<Task<'a>>,
        alternate: bool,
        items: impl DoubleEndedIterator<Item = Task<'a>> + ExactSizeIterator,
    ) {
        let count = items.len();
        if count == 0 {
            work.push(Task::Text("[]"));
        } else if alternate {
            work.extend([Task::Text("]"), Task::Newline, Task::Dedent]);
            for item in items.rev() {
                work.extend([Task::Text(","), item, Task::Newline]);
            }
            work.extend([Task::Indent, Task::Text("[")]);
        } else {
            work.push(Task::Text("]"));
            for (index, item) in items.enumerate().rev() {
                work.push(item);
                if index != 0 {
                    work.push(Task::Text(", "));
                }
            }
            work.push(Task::Text("["));
        }
    }

    fn push_pattern<'a>(work: &mut Vec<Task<'a>>, alternate: bool, pattern: &'a Pattern) {
        use Task::{Leaf, Pattern as Child, Patterns};
        use smallvec::smallvec;

        let (name, fields): (&'static str, Fields<'a>) = match pattern {
            Pattern::String(value) => return push_tuple(work, alternate, "String", Leaf(value)),
            Pattern::Variable(variable) => {
                return push_tuple(work, alternate, "Variable", Leaf(variable));
            }
            Pattern::Application { symbol, arguments } => (
                "Application",
                smallvec![("symbol", Leaf(symbol)), ("arguments", Patterns(arguments))],
            ),
            Pattern::Top { sort } => ("Top", smallvec![("sort", Leaf(sort))]),
            Pattern::Bottom { sort } => ("Bottom", smallvec![("sort", Leaf(sort))]),
            Pattern::And { sort, arguments } => (
                "And",
                smallvec![("sort", Leaf(sort)), ("arguments", Patterns(arguments))],
            ),
            Pattern::Or { sort, arguments } => (
                "Or",
                smallvec![("sort", Leaf(sort)), ("arguments", Patterns(arguments))],
            ),
            Pattern::Not { sort, argument } => (
                "Not",
                smallvec![("sort", Leaf(sort)), ("argument", Child(argument))],
            ),
            Pattern::Next { sort, argument } => (
                "Next",
                smallvec![("sort", Leaf(sort)), ("argument", Child(argument))],
            ),
            Pattern::Implies { sort, left, right } => (
                "Implies",
                smallvec![
                    ("sort", Leaf(sort)),
                    ("left", Child(left)),
                    ("right", Child(right))
                ],
            ),
            Pattern::Iff { sort, left, right } => (
                "Iff",
                smallvec![
                    ("sort", Leaf(sort)),
                    ("left", Child(left)),
                    ("right", Child(right))
                ],
            ),
            Pattern::Rewrites { sort, left, right } => (
                "Rewrites",
                smallvec![
                    ("sort", Leaf(sort)),
                    ("left", Child(left)),
                    ("right", Child(right))
                ],
            ),
            Pattern::Exists {
                sort,
                variable,
                body,
            } => (
                "Exists",
                smallvec![
                    ("sort", Leaf(sort)),
                    ("variable", Leaf(variable)),
                    ("body", Child(body))
                ],
            ),
            Pattern::Forall {
                sort,
                variable,
                body,
            } => (
                "Forall",
                smallvec![
                    ("sort", Leaf(sort)),
                    ("variable", Leaf(variable)),
                    ("body", Child(body))
                ],
            ),
            Pattern::Mu { variable, body } => (
                "Mu",
                smallvec![("variable", Leaf(variable)), ("body", Child(body))],
            ),
            Pattern::Nu { variable, body } => (
                "Nu",
                smallvec![("variable", Leaf(variable)), ("body", Child(body))],
            ),
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => (
                "Ceil",
                smallvec![
                    ("operand_sort", Leaf(operand_sort)),
                    ("result_sort", Leaf(result_sort)),
                    ("argument", Child(argument))
                ],
            ),
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => (
                "Floor",
                smallvec![
                    ("operand_sort", Leaf(operand_sort)),
                    ("result_sort", Leaf(result_sort)),
                    ("argument", Child(argument))
                ],
            ),
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => (
                "Equals",
                smallvec![
                    ("operand_sort", Leaf(operand_sort)),
                    ("result_sort", Leaf(result_sort)),
                    ("left", Child(left)),
                    ("right", Child(right))
                ],
            ),
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => (
                "In",
                smallvec![
                    ("operand_sort", Leaf(operand_sort)),
                    ("result_sort", Leaf(result_sort)),
                    ("left", Child(left)),
                    ("right", Child(right))
                ],
            ),
            Pattern::DomainValue { sort, value } => (
                "DomainValue",
                smallvec![("sort", Leaf(sort)), ("value", Leaf(value))],
            ),
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => (
                "AssociativeApplication",
                smallvec![
                    ("associativity", Leaf(associativity)),
                    ("symbol", Leaf(symbol)),
                    ("arguments", Patterns(arguments))
                ],
            ),
        };
        push_struct(work, alternate, name, fields);
    }

    pub(super) fn write(formatter: &mut fmt::Formatter<'_>, root: Task<'_>) -> fmt::Result {
        let alternate = formatter.alternate();
        let mut output = Indented {
            formatter,
            level: 0,
            on_newline: false,
        };
        let mut work = vec![root];
        // Invariant: the text written so far followed by the text of `work`, popped in order, is the derived rendering of `root`; each pattern node is expanded once into its own punctuation, leaves, and child tasks, so the loop ends after O(|root|) pops.
        while let Some(task) = work.pop() {
            match task {
                Task::Pattern(pattern) => push_pattern(&mut work, alternate, pattern),
                Task::Patterns(patterns) => {
                    push_list(&mut work, alternate, patterns.iter().map(Task::Pattern));
                }
                Task::Sort(Sort::Variable(name)) => {
                    push_tuple(&mut work, alternate, "Variable", Task::Leaf(name));
                }
                Task::Sort(Sort::Application { name, arguments }) => push_struct(
                    &mut work,
                    alternate,
                    "Application",
                    smallvec::smallvec![
                        ("name", Task::Leaf(name)),
                        ("arguments", Task::Sorts(arguments))
                    ],
                ),
                Task::Sorts(sorts) => push_list(&mut work, alternate, sorts.iter().map(Task::Sort)),
                Task::Leaf(value) if alternate => write!(output, "{value:#?}")?,
                Task::Leaf(value) => write!(output, "{value:?}")?,
                Task::Text(text) => output.write_str(text)?,
                Task::Newline => output.write_str("\n")?,
                Task::Indent => output.level += 1,
                Task::Dedent => output.level -= 1,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Pattern;
    use crate::kore::parser::parse_pattern;

    #[test]
    fn debug_writes_the_derived_compact_form() {
        let pattern = parse_pattern(
            r#"\and{S{}}(f{}(X:S{}, "a"), \not{S{}}(\dv{S{}}("1")), \exists{S{}}(Y:S{}, \top{S{}}()))"#,
        )
        .unwrap();
        let sort = r#"Application { name: "S", arguments: [] }"#;
        assert_eq!(
            format!("{pattern:?}"),
            format!(
                "And {{ sort: {sort}, arguments: [\
                 Application {{ symbol: Symbol {{ name: \"f\", sort_parameters: [] }}, arguments: [\
                 Variable(Variable {{ kind: Element, name: \"X\", sort: {sort} }}), String(\"a\")] }}, \
                 Not {{ sort: {sort}, argument: DomainValue {{ sort: {sort}, value: \"1\" }} }}, \
                 Exists {{ sort: {sort}, variable: Variable {{ kind: Element, name: \"Y\", sort: {sort} }}, \
                 body: Top {{ sort: {sort} }} }}] }}"
            )
        );
    }

    /// One source per variant, listed in the order the variants are declared in `Pattern`.
    #[test]
    fn pattern_rank_follows_declaration_order() {
        let sources = [
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
        let patterns: Vec<Pattern> = sources
            .into_iter()
            .map(|source| parse_pattern(source).unwrap())
            .collect();

        let ranks: Vec<u8> = patterns.iter().map(Pattern::discriminant).collect();
        assert_eq!(ranks, (0..22).collect::<Vec<u8>>());
        for pair in patterns.windows(2) {
            assert!(pair[0] < pair[1], "{} should precede {}", pair[0], pair[1]);
        }
    }
}
