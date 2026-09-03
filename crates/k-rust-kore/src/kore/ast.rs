//! Syntax tree for textual KORE.

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

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Sort {
    Variable(String),
    Application { name: String, arguments: Vec<Sort> },
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

#[derive(Debug)]
pub enum Pattern {
    String(String),
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
        variable: Variable,
        body: Box<Pattern>,
    },
    Forall {
        sort: Sort,
        variable: Variable,
        body: Box<Pattern>,
    },
    Mu {
        variable: Variable,
        body: Box<Pattern>,
    },
    Nu {
        variable: Variable,
        body: Box<Pattern>,
    },
    Ceil {
        operand_sort: Sort,
        result_sort: Sort,
        argument: Box<Pattern>,
    },
    Floor {
        operand_sort: Sort,
        result_sort: Sort,
        argument: Box<Pattern>,
    },
    Equals {
        operand_sort: Sort,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    In {
        operand_sort: Sort,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    DomainValue {
        sort: Sort,
        value: String,
    },
    AssociativeApplication {
        associativity: Associativity,
        symbol: Symbol,
        arguments: Vec<Pattern>,
    },
}

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
        while let Some(mut child) = work.pop() {
            work.extend(super::walk::take_children(&mut child));
        }
    }
}

impl PartialOrd for Pattern {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Pattern {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use Pattern::*;
        use std::cmp::Ordering;
        fn rank(pattern: &Pattern) -> u8 {
            match pattern {
                Variable(_) => 0,
                Application { .. } => 1,
                Top { .. } => 2,
                Bottom { .. } => 3,
                And { .. } => 4,
                Or { .. } => 5,
                Not { .. } => 6,
                Next { .. } => 7,
                Implies { .. } => 8,
                Iff { .. } => 9,
                Exists { .. } => 10,
                Forall { .. } => 11,
                Mu { .. } => 12,
                Nu { .. } => 13,
                Ceil { .. } => 14,
                Floor { .. } => 15,
                Rewrites { .. } => 16,
                Equals { .. } => 17,
                In { .. } => 18,
                DomainValue { .. } => 19,
                String(_) => 20,
                AssociativeApplication { .. } => 21,
            }
        }

        fn scalars(left: &Pattern, right: &Pattern) -> Ordering {
            match (left, right) {
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
                ) => ls.cmp(rs).then_with(|| alphanum_cmp(lv, rv)),
                (String(left), String(right)) => left.encode_utf16().cmp(right.encode_utf16()),
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

            let ordering = rank(left)
                .cmp(&rank(right))
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

fn alphanum_cmp(left: &str, right: &str) -> std::cmp::Ordering {
    fn is_digit(unit: u16) -> bool {
        (u16::from(b'0')..=u16::from(b'9')).contains(&unit)
    }

    fn chunk(value: &[u16], start: usize) -> &[u16] {
        let digit = is_digit(value[start]);
        let end = value[start + 1..]
            .iter()
            .position(|unit| is_digit(*unit) != digit)
            .map_or(value.len(), |offset| start + 1 + offset);
        &value[start..end]
    }

    let (left, right): (Vec<_>, Vec<_>) = (
        left.encode_utf16().collect(),
        right.encode_utf16().collect(),
    );
    let (mut li, mut ri) = (0, 0);
    while li < left.len() && ri < right.len() {
        let (lc, rc) = (chunk(&left, li), chunk(&right, ri));
        li += lc.len();
        ri += rc.len();
        let ordering = if is_digit(lc[0]) && is_digit(rc[0]) {
            lc.len().cmp(&rc.len()).then_with(|| lc.cmp(rc))
        } else {
            lc.cmp(rc)
        };
        if !ordering.is_eq() {
            return ordering;
        }
    }
    left.len().cmp(&right.len())
}

#[cfg(test)]
mod tests {
    use super::Pattern;
    use crate::kore::parser::parse_pattern;

    #[test]
    fn scala_pattern_ordering() {
        let sources = [
            "A:A{}",
            "A{}(\\dv{A{}}(\"A\"), A:A{})",
            "\\top{A{}}()",
            "\\bottom{A{}}()",
            "\\and{A{}}(\\top{A{}}(), \\bottom{A{}}())",
            "\\or{A{}}(\\top{A{}}(), \\bottom{A{}}())",
            "\\not{A{}}(\\top{A{}}())",
            "\\implies{A{}}(\\top{A{}}(), \\bottom{A{}}())",
            "\\iff{A{}}(\\top{A{}}(), \\bottom{A{}}())",
            "\\exists{A{}}(A:A{}, A{}())",
            "\\forall{A{}}(A:A{}, A{}())",
            "\\ceil{A{}, A{}}(A{}())",
            "\\floor{A{}, A{}}(A{}())",
            "\\rewrites{A{}}(A{}(), A:A{})",
            "\\equals{A{}, A{}}(A{}(), A{}())",
            "\\in{A{}, A{}}(A{}(), A{}())",
            "\\dv{A{}}(\"A\")",
            "\"A\"",
        ];
        let patterns: Vec<Pattern> = sources
            .into_iter()
            .map(|source| parse_pattern(source).unwrap())
            .collect();

        for pair in patterns.windows(2) {
            assert!(pair[0] < pair[1], "{} should precede {}", pair[0], pair[1]);
        }
    }

    #[test]
    fn scala_domain_values_use_alphanumeric_ordering() {
        let pattern = |value| parse_pattern(&format!(r#"\dv{{S{{}}}}("{value}")"#)).unwrap();
        assert!(pattern("item2") < pattern("item10"));
        assert!(pattern("item02") > pattern("item2"));
    }
}
