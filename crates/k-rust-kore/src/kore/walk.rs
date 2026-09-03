use super::ast::Pattern;

pub(crate) fn children(pattern: &Pattern) -> Vec<&Pattern> {
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

pub(crate) fn rebuild<T>(root: &Pattern, mut build: impl FnMut(&Pattern, Vec<T>) -> T) -> T {
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
        std::mem::replace(pattern.as_mut(), Pattern::String(String::new()))
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
