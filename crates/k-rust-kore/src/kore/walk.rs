//! ```toml algorithm
//! id = "kore.pattern.walk"
//! name = "explicit-stack traversal and rebuilding of KORE patterns"
//! sites = ["children", "for_each_post_order", "rebuild", "clone_node", "take_children"]
//! variable = "p = pattern nodes"
//! counters = []
//! no_counter = "pattern traversal has no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "one traversal"
//! bound = "O(|p|)"
//! ```
//!
//! One traversal of [`Pattern`] (children in field order, post-order visit with an explicit
//! stack, and rebuild) and the walkers derived from it. Each traversal visits every pattern
//! node once, and a derived walker that collects variables adds one ordered-set insertion per
//! variable node.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{Pattern, Sort, Symbol, Variable, VariableKind};

pub fn children(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments.iter().collect(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => vec![argument],
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => vec![left, right],
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => vec![body],
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => Vec::new(),
    }
}

pub fn for_each_post_order(pattern: &Pattern, mut visit: impl FnMut(&Pattern)) {
    let mut work = vec![(pattern, false)];
    while let Some((pattern, complete)) = work.pop() {
        if complete {
            visit(pattern);
            continue;
        }
        work.push((pattern, true));
        let children = children(pattern);
        work.extend(children.into_iter().rev().map(|child| (child, false)));
    }
}

pub fn rebuild<T>(root: &Pattern, mut build: impl FnMut(&Pattern, Vec<T>) -> T) -> T {
    struct Frame<'a, T> {
        pattern: &'a Pattern,
        children: Vec<&'a Pattern>,
        next: usize,
        built: Vec<T>,
    }

    impl<'a, T> Frame<'a, T> {
        fn new(pattern: &'a Pattern) -> Self {
            Self {
                pattern,
                children: children(pattern),
                next: 0,
                built: Vec::new(),
            }
        }
    }

    let mut stack = vec![Frame::new(root)];
    loop {
        let frame = stack
            .last_mut()
            .expect("the root frame remains until return");
        if let Some(child) = frame.children.get(frame.next).copied() {
            frame.next += 1;
            stack.push(Frame::new(child));
            continue;
        }

        let frame = stack.pop().expect("the completed frame is present");
        let value = build(frame.pattern, frame.built);
        if let Some(parent) = stack.last_mut() {
            parent.built.push(value);
        } else {
            return value;
        }
    }
}

pub(crate) fn clone_node(pattern: &Pattern, children: Vec<Pattern>) -> Pattern {
    let mut children = children.into_iter();
    let mut child = || {
        Box::new(
            children
                .next()
                .expect("the traversal supplies every pattern child"),
        )
    };
    match pattern {
        Pattern::String(value) => Pattern::String(value.clone()),
        Pattern::Variable(variable) => Pattern::Variable(variable.clone()),
        Pattern::Application { symbol, .. } => Pattern::Application {
            symbol: symbol.clone(),
            arguments: children.collect(),
        },
        Pattern::Top { sort } => Pattern::Top { sort: sort.clone() },
        Pattern::Bottom { sort } => Pattern::Bottom { sort: sort.clone() },
        Pattern::And { sort, .. } => Pattern::And {
            sort: sort.clone(),
            arguments: children.collect(),
        },
        Pattern::Or { sort, .. } => Pattern::Or {
            sort: sort.clone(),
            arguments: children.collect(),
        },
        Pattern::Not { sort, .. } => Pattern::Not {
            sort: sort.clone(),
            argument: child(),
        },
        Pattern::Next { sort, .. } => Pattern::Next {
            sort: sort.clone(),
            argument: child(),
        },
        Pattern::Implies { sort, .. } => Pattern::Implies {
            sort: sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::Iff { sort, .. } => Pattern::Iff {
            sort: sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::Rewrites { sort, .. } => Pattern::Rewrites {
            sort: sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::Exists { sort, variable, .. } => Pattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Forall { sort, variable, .. } => Pattern::Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Mu { variable, .. } => Pattern::Mu {
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Nu { variable, .. } => Pattern::Nu {
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Ceil {
            operand_sort,
            result_sort,
            ..
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: child(),
        },
        Pattern::Floor {
            operand_sort,
            result_sort,
            ..
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: child(),
        },
        Pattern::Equals {
            operand_sort,
            result_sort,
            ..
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::In {
            operand_sort,
            result_sort,
            ..
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::DomainValue { sort, value } => Pattern::DomainValue {
            sort: sort.clone(),
            value: value.clone(),
        },
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            ..
        } => Pattern::AssociativeApplication {
            associativity: *associativity,
            symbol: symbol.clone(),
            arguments: children.collect(),
        },
    }
}

pub(crate) fn take_children(pattern: &mut Pattern) -> Vec<Pattern> {
    fn take_box(pattern: &mut Box<Pattern>) -> Pattern {
        std::mem::replace(pattern.as_mut(), Pattern::String(String::new().into()))
    }

    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => std::mem::take(arguments),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => vec![take_box(argument)],
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => vec![take_box(left), take_box(right)],
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => vec![take_box(body)],
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => Vec::new(),
    }
}

impl Pattern {
    pub fn variables(&self) -> BTreeSet<Variable> {
        let mut result = BTreeSet::new();
        for_each_post_order(self, |pattern| match pattern {
            Pattern::Variable(variable)
            | Pattern::Exists { variable, .. }
            | Pattern::Forall { variable, .. }
            | Pattern::Mu { variable, .. }
            | Pattern::Nu { variable, .. } => {
                result.insert(variable.clone());
            }
            _ => {}
        });
        result
    }

    pub fn variable_occurrences(&self) -> BTreeMap<(VariableKind, String), usize> {
        let mut result = BTreeMap::new();
        for_each_post_order(self, |pattern| match pattern {
            Pattern::Variable(variable)
            | Pattern::Exists { variable, .. }
            | Pattern::Forall { variable, .. }
            | Pattern::Mu { variable, .. }
            | Pattern::Nu { variable, .. } => {
                *result
                    .entry((variable.kind, variable.name.clone()))
                    .or_default() += 1;
            }
            _ => {}
        });
        result
    }

    pub fn free_variables(&self) -> BTreeSet<Variable> {
        enum Step<'a> {
            Enter(&'a Pattern),
            Leave(&'a Variable),
        }

        let mut result = BTreeSet::new();
        let mut bound = BTreeMap::<&Variable, usize>::new();
        let mut work = vec![Step::Enter(self)];
        while let Some(step) = work.pop() {
            match step {
                Step::Leave(variable) => {
                    let count = bound
                        .get_mut(variable)
                        .expect("a binder remains active until its leave step");
                    *count -= 1;
                    if *count == 0 {
                        bound.remove(variable);
                    }
                }
                Step::Enter(pattern) => {
                    if let Pattern::Variable(variable) = pattern
                        && !bound.contains_key(variable)
                    {
                        result.insert(variable.clone());
                    }
                    let binder = match pattern {
                        Pattern::Exists { variable, .. }
                        | Pattern::Forall { variable, .. }
                        | Pattern::Mu { variable, .. }
                        | Pattern::Nu { variable, .. } => Some(variable),
                        _ => None,
                    };
                    if let Some(variable) = binder {
                        *bound.entry(variable).or_default() += 1;
                        work.push(Step::Leave(variable));
                    }
                    work.extend(children(pattern).into_iter().rev().map(Step::Enter));
                }
            }
        }
        result
    }

    pub fn sort_variables(&self) -> BTreeSet<String> {
        fn collect(sort: &Sort, result: &mut BTreeSet<String>) {
            let mut work = vec![sort];
            while let Some(sort) = work.pop() {
                match sort {
                    Sort::Variable(name) => {
                        result.insert(name.clone());
                    }
                    Sort::Application { arguments, .. } => work.extend(arguments),
                }
            }
        }

        let mut result = BTreeSet::new();
        for_each_post_order(self, |pattern| match pattern {
            Pattern::String(_) => {}
            Pattern::Variable(variable) => collect(&variable.sort, &mut result),
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => {
                for sort in &symbol.sort_parameters {
                    collect(sort, &mut result);
                }
            }
            Pattern::Top { sort }
            | Pattern::Bottom { sort }
            | Pattern::And { sort, .. }
            | Pattern::Or { sort, .. }
            | Pattern::Not { sort, .. }
            | Pattern::Next { sort, .. }
            | Pattern::Implies { sort, .. }
            | Pattern::Iff { sort, .. }
            | Pattern::Rewrites { sort, .. } => collect(sort, &mut result),
            Pattern::Exists { sort, variable, .. } | Pattern::Forall { sort, variable, .. } => {
                collect(sort, &mut result);
                collect(&variable.sort, &mut result);
            }
            Pattern::Mu { variable, .. } | Pattern::Nu { variable, .. } => {
                collect(&variable.sort, &mut result);
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
            } => {
                collect(operand_sort, &mut result);
                collect(result_sort, &mut result);
            }
            Pattern::DomainValue { sort, .. } => collect(sort, &mut result),
        });
        result
    }

    pub fn syntactic_sort(&self) -> Option<&Sort> {
        match self {
            Pattern::Variable(variable) => Some(&variable.sort),
            Pattern::Top { sort }
            | Pattern::Bottom { sort }
            | Pattern::And { sort, .. }
            | Pattern::Or { sort, .. }
            | Pattern::Not { sort, .. }
            | Pattern::Next { sort, .. }
            | Pattern::Implies { sort, .. }
            | Pattern::Iff { sort, .. }
            | Pattern::Rewrites { sort, .. }
            | Pattern::Exists { sort, .. }
            | Pattern::Forall { sort, .. } => Some(sort),
            Pattern::Ceil { result_sort, .. }
            | Pattern::Floor { result_sort, .. }
            | Pattern::Equals { result_sort, .. }
            | Pattern::In { result_sort, .. } => Some(result_sort),
            Pattern::DomainValue { sort, .. } => Some(sort),
            Pattern::String(_)
            | Pattern::Application { .. }
            | Pattern::Mu { .. }
            | Pattern::Nu { .. }
            | Pattern::AssociativeApplication { .. } => None,
        }
    }

    pub fn strip_exists(&self) -> &Pattern {
        let mut pattern = self;
        while let Pattern::Exists { body, .. } = pattern {
            pattern = body;
        }
        pattern
    }

    pub fn leading_existentials(&self) -> (&Pattern, Vec<&Variable>) {
        let mut pattern = self;
        let mut variables = Vec::new();
        while let Pattern::Exists { variable, body, .. } = pattern {
            variables.push(variable);
            pattern = body;
        }
        (pattern, variables)
    }

    pub fn conjuncts_at(&self, sort: &Sort) -> Vec<&Pattern> {
        self.flatten_at(sort, true)
    }

    pub fn disjuncts_at(&self, sort: &Sort) -> Vec<&Pattern> {
        self.flatten_at(sort, false)
    }

    fn flatten_at(&self, sort: &Sort, conjunction: bool) -> Vec<&Pattern> {
        let mut result = Vec::new();
        let mut work = vec![self];
        while let Some(pattern) = work.pop() {
            let arguments = match pattern {
                Pattern::And {
                    sort: node_sort,
                    arguments,
                } if conjunction && node_sort == sort => Some(arguments),
                Pattern::Or {
                    sort: node_sort,
                    arguments,
                } if !conjunction && node_sort == sort => Some(arguments),
                Pattern::Top { sort: node_sort } if conjunction && node_sort == sort => continue,
                Pattern::Bottom { sort: node_sort } if !conjunction && node_sort == sort => {
                    continue;
                }
                _ => None,
            };
            if let Some(arguments) = arguments {
                work.extend(arguments.iter().rev());
            } else {
                result.push(pattern);
            }
        }
        result
    }

    pub fn find_application(
        &self,
        mut accept: impl FnMut(&Symbol, &[Pattern]) -> bool,
    ) -> Option<&Pattern> {
        let mut work = vec![(self, false)];
        while let Some((pattern, complete)) = work.pop() {
            if complete {
                if let Pattern::Application { symbol, arguments } = pattern
                    && accept(symbol, arguments)
                {
                    return Some(pattern);
                }
            } else {
                work.push((pattern, true));
                work.extend(
                    children(pattern)
                        .into_iter()
                        .rev()
                        .map(|child| (child, false)),
                );
            }
        }
        None
    }
}
