//! Conversion from parsed KORE patterns to user-facing K terms.

use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

use crate::kore::ast::{KoreString, Pattern, Sort as KoreSort, Symbol, Variable, VariableKind};
use crate::kore::normalize;
use crate::kore::string::LiteralEncoding;
use crate::names::{BuiltinSort, WellKnownSymbol};

use super::ast::{Label, Sort, Term, TermParts};
use super::identifier::{self, DecodeError};
use super::names::{FrontendSort, InternalLabel};
use super::string;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConversionError(pub String);

impl Display for ConversionError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ConversionError {}

impl From<DecodeError> for ConversionError {
    fn from(error: DecodeError) -> Self {
        Self(error.to_string())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Converter<'a> {
    sort_hooks: &'a HashMap<String, String>,
}

impl<'a> Converter<'a> {
    pub fn new(sort_hooks: &'a HashMap<String, String>) -> Self {
        Self { sort_hooks }
    }

    /// The KAST term of `pattern`, normalized for KAST first (`normalize::for_kast`).
    ///
    /// The conversion walks the pattern with an explicit work stack, so a pattern of any depth
    /// converts on any thread: a collection that execution built, one level per element, is as
    /// deep as it is long.
    pub fn convert(&self, pattern: &Pattern) -> Result<Term, ConversionError> {
        self.pattern(&normalize::for_kast(pattern))
    }

    /// The KAST term of a normalized pattern.
    ///
    /// Each node is opened when the walk reaches it, which converts its own fields (its label,
    /// sorts and bound variable) and may fail, and is finished once its children are converted,
    /// which cannot fail. Children are converted in order, so the first error is the one a
    /// depth-first conversion that opens each node before its children meets first.
    fn pattern(&self, root: &Pattern) -> Result<Term, ConversionError> {
        let mut stack = Vec::new();
        let mut finished = match self.open(root)? {
            Opened::Leaf(term) => Some(term),
            Opened::Node(node) => {
                stack.push(node);
                None
            }
        };
        // Invariant: `stack` holds the opened nodes on the path from `root` to the node being
        // converted, each with the terms of its converted children in `built` and its other
        // children in `children`; `finished` is the term of a node not yet handed to its parent.
        // Each node is opened once and finished once, so the loop returns after |root| steps.
        loop {
            if let Some(term) = finished.take() {
                let Some(parent) = stack.last_mut() else {
                    return Ok(term);
                };
                parent.built.push(term);
            }
            let node = stack.last_mut().expect("a node awaits its children");
            if let Some(child) = node.children.next() {
                match self.open(child)? {
                    Opened::Leaf(term) => finished = Some(term),
                    Opened::Node(node) => stack.push(node),
                }
            } else {
                let node = stack.pop().expect("the node is present");
                finished = Some(node.finish());
            }
        }
    }

    /// Open `pattern`: its term when it has no children to convert, or what it awaits.
    fn open<'p>(&self, pattern: &'p Pattern) -> Result<Opened<'p>, ConversionError> {
        match pattern {
            Pattern::Variable(variable) => Ok(Opened::Leaf(self.variable(variable)?)),
            Pattern::Application { symbol, arguments } => self.application(symbol, arguments),
            Pattern::Top { sort } => Ok(Opened::Leaf(Term::Apply {
                label: Label::with_parameters(InternalLabel::Top.as_str(), vec![self.sort(sort)?]),
                arguments: Vec::new(),
            })),
            Pattern::Bottom { sort } => Ok(Opened::Leaf(Term::Apply {
                label: Label::with_parameters(
                    InternalLabel::Bottom.as_str(),
                    vec![self.sort(sort)?],
                ),
                arguments: Vec::new(),
            })),
            Pattern::And { sort, arguments } => self.associative(
                InternalLabel::And.as_str(),
                InternalLabel::Top.as_str(),
                sort,
                arguments,
            ),
            Pattern::Or { sort, arguments } => self.associative(
                InternalLabel::Or.as_str(),
                InternalLabel::Bottom.as_str(),
                sort,
                arguments,
            ),
            Pattern::Not { sort, argument } => {
                self.ml(InternalLabel::Not.as_str(), [sort], [argument.as_ref()])
            }
            Pattern::Implies { sort, left, right } => self.ml(
                InternalLabel::Implies.as_str(),
                [sort],
                [left.as_ref(), right.as_ref()],
            ),
            Pattern::Rewrites { left, right, .. } => Ok(Opened::node(
                Pending::Rewrite,
                vec![left.as_ref(), right.as_ref()],
                Vec::with_capacity(2),
            )),
            Pattern::Exists {
                sort,
                variable,
                body,
            } => self.binder(InternalLabel::Exists.as_str(), sort, variable, body),
            Pattern::Forall {
                sort,
                variable,
                body,
            } => self.binder(InternalLabel::Forall.as_str(), sort, variable, body),
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => self.ml(
                InternalLabel::Ceil.as_str(),
                [operand_sort, result_sort],
                [argument.as_ref()],
            ),
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => self.ml(
                InternalLabel::Floor.as_str(),
                [operand_sort, result_sort],
                [argument.as_ref()],
            ),
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => self.ml(
                InternalLabel::Equals.as_str(),
                [operand_sort, result_sort],
                [left.as_ref(), right.as_ref()],
            ),
            Pattern::DomainValue {
                sort: kore_sort,
                value,
            } => Ok(Opened::Leaf(self.domain_value(kore_sort, value)?)),
            Pattern::String(value) => Ok(Opened::Leaf(Term::Token {
                token: value.as_utf8().map(str::to_owned).map_err(|_| {
                    ConversionError("KORE string pattern is not valid UTF-8".into())
                })?,
                sort: Sort::frontend(FrontendSort::KString),
            })),
            Pattern::Iff { .. } => {
                Err(ConversionError("Iff patterns currently unsupported".into()))
            }
            Pattern::In { .. } => Err(ConversionError("In patterns currently unsupported".into())),
            Pattern::Next { .. } => Err(ConversionError(
                "Next patterns currently unsupported".into(),
            )),
            Pattern::Mu { .. } => Err(ConversionError("Mu patterns currently unsupported".into())),
            Pattern::Nu { .. } => Err(ConversionError("Nu patterns currently unsupported".into())),
            Pattern::AssociativeApplication { .. } => unreachable!("normalization expands these"),
        }
    }

    fn domain_value(
        &self,
        kore_sort: &KoreSort,
        value: &KoreString,
    ) -> Result<Term, ConversionError> {
        let sort = self.sort(kore_sort)?;
        // The payload holds code points by the encoding of the KORE sort's name
        // (`LiteralEncoding`), and the hook says what they are.
        let encoding = LiteralEncoding::of_domain_value(kore_sort);
        let token = match self.sort_hooks.get(&sort.name).map(String::as_str) {
            Some("STRING.String") => string::quote(&encoding.code_points(value)),
            Some("BYTES.Bytes") => {
                let bytes = match encoding {
                    LiteralEncoding::Bytes => value.as_bytes().to_vec(),
                    LiteralEncoding::Utf8 => encoding
                        .code_points(value)
                        .chars()
                        .map(|character| u8::try_from(u32::from(character)).ok())
                        .collect::<Option<Vec<u8>>>()
                        .ok_or_else(|| {
                            ConversionError(format!(
                                "domain value of sort {} holds a code point above U+00FF, which is no byte",
                                sort.name
                            ))
                        })?,
                };
                format!("b{}", string::quote_bytes(&bytes))
            }
            _ => value.as_utf8().map(str::to_owned).map_err(|_| {
                ConversionError(format!(
                    "domain value of sort {} is not valid UTF-8",
                    sort.name
                ))
            })?,
        };
        Ok(Term::Token { token, sort })
    }

    fn sort(&self, sort: &KoreSort) -> Result<Sort, ConversionError> {
        kast_sort(sort)
    }

    fn variable(&self, variable: &Variable) -> Result<Term, ConversionError> {
        let (kind, name) = identifier::decode_variable(&variable.name);
        let prefix = match kind {
            VariableKind::Element => "",
            VariableKind::Set => "@",
        };
        Ok(Term::Variable {
            name: format!("{prefix}{}", name?),
            sort: Some(self.sort(&variable.sort)?),
        })
    }

    fn application<'p>(
        &self,
        symbol: &Symbol,
        arguments: &'p [Pattern],
    ) -> Result<Opened<'p>, ConversionError> {
        match symbol.name.as_str() {
            // An injection is its argument: open that in its place.
            name if name == WellKnownSymbol::Inj.as_str() => {
                self.open(arguments.first().ok_or_else(|| {
                    ConversionError("inj application requires an argument".into())
                })?)
            }
            name if name == WellKnownSymbol::KSeq.as_str()
                || name == WellKnownSymbol::Append.as_str() =>
            {
                Ok(Opened::node(
                    Pending::Sequence,
                    arguments.iter().collect(),
                    Vec::with_capacity(arguments.len()),
                ))
            }
            name if name == WellKnownSymbol::DotK.as_str() => {
                Ok(Opened::Leaf(Term::Sequence(Vec::new())))
            }
            _ => {
                let label = Label {
                    name: identifier::decode_label(&symbol.name)?,
                    parameters: symbol
                        .sort_parameters
                        .iter()
                        .map(|sort| self.sort(sort))
                        .collect::<Result<_, _>>()?,
                };
                Ok(Opened::node(
                    Pending::Apply(label),
                    arguments.iter().collect(),
                    Vec::with_capacity(arguments.len()),
                ))
            }
        }
    }

    fn ml<'p, const S: usize, const P: usize>(
        &self,
        name: &str,
        sorts: [&KoreSort; S],
        patterns: [&'p Pattern; P],
    ) -> Result<Opened<'p>, ConversionError> {
        let label = Label::with_parameters(
            name,
            sorts
                .into_iter()
                .map(|sort| self.sort(sort))
                .collect::<Result<_, _>>()?,
        );
        Ok(Opened::node(
            Pending::Apply(label),
            patterns.to_vec(),
            Vec::with_capacity(P),
        ))
    }

    /// A quantifier `name` over `variable`: the variable's sort and the pattern's are the label's
    /// parameters, and the variable and the body its arguments.
    fn binder<'p>(
        &self,
        name: &str,
        sort: &KoreSort,
        variable: &Variable,
        body: &'p Pattern,
    ) -> Result<Opened<'p>, ConversionError> {
        let label =
            Label::with_parameters(name, vec![self.sort(&variable.sort)?, self.sort(sort)?]);
        let mut built = Vec::with_capacity(2);
        built.push(self.variable(variable)?);
        Ok(Opened::node(Pending::Apply(label), vec![body], built))
    }

    fn associative<'p>(
        &self,
        name: &str,
        unit: &str,
        sort: &KoreSort,
        arguments: &'p [Pattern],
    ) -> Result<Opened<'p>, ConversionError> {
        let label = Label::with_parameters(name, vec![self.sort(sort)?]);
        let unit = Label::with_parameters(unit, vec![self.sort(sort)?]);
        Ok(Opened::node(
            Pending::Associative { label, unit },
            arguments.iter().collect(),
            Vec::with_capacity(arguments.len()),
        ))
    }
}

/// A pattern node as [`Converter::open`] leaves it.
enum Opened<'p> {
    /// The node's term: it has no children to convert.
    Leaf(Term),
    /// The node awaits the terms of its children.
    Node(Awaiting<'p>),
}

impl<'p> Opened<'p> {
    fn node(pending: Pending, children: Vec<&'p Pattern>, built: Vec<Term>) -> Self {
        Self::Node(Awaiting {
            pending,
            children: children.into_iter(),
            built,
        })
    }
}

/// An opened node: the children still to convert, the terms of those converted (after any the
/// node itself supplied, a binder's variable), and what the node makes of them.
struct Awaiting<'p> {
    pending: Pending,
    children: std::vec::IntoIter<&'p Pattern>,
    built: Vec<Term>,
}

/// What an opened node makes of its arguments' terms.
enum Pending {
    /// An application of the label to the arguments.
    Apply(Label),
    /// A `kseq` or `append`: the sequence of the arguments, nested sequences flattened.
    Sequence,
    /// A `\rewrites`: its two arguments, left and right.
    Rewrite,
    /// A `\and` or `\or`: an application of `label` to the arguments, with an argument that is an
    /// application of `label` replaced by its own arguments and one that is its `unit` dropped.
    Associative { label: Label, unit: Label },
}

impl Awaiting<'_> {
    fn finish(self) -> Term {
        debug_assert!(self.children.len() == 0, "every child is converted");
        match self.pending {
            Pending::Apply(label) => Term::Apply {
                label,
                arguments: self.built,
            },
            Pending::Sequence => Term::sequence(self.built),
            Pending::Rewrite => {
                let [left, right] = <[Term; 2]>::try_from(self.built)
                    .unwrap_or_else(|_| unreachable!("a rewrite has two sides"));
                Term::Rewrite {
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            Pending::Associative { label, unit } => {
                let mut flattened = Vec::with_capacity(self.built.len());
                for argument in self.built {
                    match argument.into_parts() {
                        TermParts::Apply {
                            label: child,
                            arguments,
                        } if child == label => {
                            flattened.extend(arguments);
                        }
                        TermParts::Apply {
                            label: child,
                            arguments,
                        } if child == unit && arguments.is_empty() => {}
                        argument => flattened.push(Term::from(argument)),
                    }
                }
                Term::Apply {
                    label,
                    arguments: flattened,
                }
            }
        }
    }
}

/// The KAST sort of a KORE sort: a sort variable is `K`. Sort parameters are converted with an
/// explicit work stack, so a sort of any depth converts on any thread, as it is read and dropped.
fn kast_sort(root: &KoreSort) -> Result<Sort, ConversionError> {
    /// An application sort whose name is decoded, with its arguments still to convert and the
    /// sorts of those converted.
    struct Awaiting<'s> {
        name: String,
        arguments: std::slice::Iter<'s, KoreSort>,
        built: Vec<Sort>,
    }

    fn open(sort: &KoreSort) -> Result<Result<Sort, Awaiting<'_>>, ConversionError> {
        match sort {
            KoreSort::Variable(_) => Ok(Ok(Sort::builtin(BuiltinSort::K))),
            KoreSort::Application { name, arguments } => {
                let name = identifier::decode_sort_name(name)?;
                if arguments.is_empty() {
                    Ok(Ok(Sort::new(name)))
                } else {
                    Ok(Err(Awaiting {
                        name,
                        arguments: arguments.iter(),
                        built: Vec::with_capacity(arguments.len()),
                    }))
                }
            }
        }
    }

    let mut stack = Vec::new();
    let mut finished = match open(root)? {
        Ok(sort) => Some(sort),
        Err(node) => {
            stack.push(node);
            None
        }
    };
    // Invariant: `stack` holds the opened application sorts on the path from `root` to the sort
    // being converted, each with the converted sorts of its first arguments in `built`;
    // `finished` is a converted sort not yet handed to its parent. Each sort is opened once and
    // finished once, so the loop returns after |root| steps.
    loop {
        if let Some(sort) = finished.take() {
            let Some(parent) = stack.last_mut() else {
                return Ok(sort);
            };
            parent.built.push(sort);
        }
        let node = stack.last_mut().expect("a sort awaits its arguments");
        if let Some(argument) = node.arguments.next() {
            match open(argument)? {
                Ok(sort) => finished = Some(sort),
                Err(node) => stack.push(node),
            }
        } else {
            let node = stack.pop().expect("the sort is present");
            finished = Some(Sort::with_parameters(node.name, node.built));
        }
    }
}

/// The sort hooks of a definition as [`Converter::new`] takes them: the KAST name of each hooked
/// sort with its hook, from the KORE name and hook of each sort declaration.
///
/// A domain value's KAST token depends on its sort's hook (a `BYTES.Bytes` payload is a byte
/// string, not text), and only the definition states the hooks. A KORE sort name that does not
/// decode names no sort a converted pattern can have, since the conversion of such a sort fails
/// first, and is left out.
pub fn sort_hooks<'a>(
    kore_sorts: impl IntoIterator<Item = (&'a str, &'a str)>,
) -> HashMap<String, String> {
    kore_sorts
        .into_iter()
        .filter_map(|(name, hook)| {
            Some((identifier::decode_sort_name(name).ok()?, hook.to_owned()))
        })
        .collect()
}

pub fn convert_sort(sort: &KoreSort) -> Result<Sort, ConversionError> {
    kast_sort(sort)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::kore::parser::parse_pattern;

    use super::{Converter, sort_hooks};

    /// The conversion of a pattern that holds no domain value, which needs no sort hook.
    fn convert(
        pattern: &crate::kore::ast::Pattern,
    ) -> Result<crate::kast::Term, super::ConversionError> {
        Converter::new(&HashMap::new()).convert(pattern)
    }

    #[test]
    fn converts_labels_sequences_and_rewrites() {
        let pattern = parse_pattern(
            r"\rewrites{SortK{}}(kseq{}(Lbl'UndsPlus'Int'Unds'{}(), X:SortInt{}), dotk{}())",
        )
        .unwrap();
        assert_eq!(
            convert(&pattern).unwrap().to_string(),
            r"`` `_+Int_`(.KList)~>X``=>.K"
        );
    }

    #[test]
    fn converts_string_domain_values_using_hooks() {
        let pattern = parse_pattern(r#"\dv{SortString{}}("hello")"#).unwrap();
        let hooks = HashMap::from([("String".into(), "STRING.String".into())]);
        let term = Converter::new(&hooks).convert(&pattern).unwrap();
        assert_eq!(term.to_string(), r#"#token("\"hello\"","String")"#);
    }

    /// A Bytes domain value is a byte string, one byte per code point U+0000 to U+00FF, rendered
    /// by its hook whether or not it is valid UTF-8; a String one is quoted. The hooks are read
    /// from KORE sort declarations.
    #[test]
    fn converts_bytes_and_string_domain_values_with_the_definitions_hooks() {
        let hooks = sort_hooks([
            ("SortBytes", "BYTES.Bytes"),
            ("SortString", "STRING.String"),
            ("NotASort", "INT.Int"),
        ]);
        assert_eq!(
            hooks,
            HashMap::from([
                ("Bytes".to_owned(), "BYTES.Bytes".to_owned()),
                ("String".to_owned(), "STRING.String".to_owned()),
            ])
        );
        let converter = Converter::new(&hooks);
        let bytes = parse_pattern(r#"\dv{SortBytes{}}("\x80\xff")"#).unwrap();
        assert_eq!(
            converter.convert(&bytes).unwrap().to_string(),
            r#"#token("b\"\\x80\\xff\"","Bytes")"#
        );
        let string = parse_pattern(r#"\dv{SortString{}}("a")"#).unwrap();
        assert_eq!(
            converter.convert(&string).unwrap().to_string(),
            r#"#token("\"a\"","String")"#
        );
    }

    /// A quantifier's label carries the variable's sort and its own, a conjunction nested in
    /// one of the same sort is flattened into it and its unit dropped, injections disappear, and
    /// matching-logic connectives keep their sorts as label parameters.
    #[test]
    fn converts_quantifiers_connectives_and_injections() {
        use crate::kast::{InternalLabel, Label, Sort, Term};

        let pattern = parse_pattern(
            r"\exists{SortK{}}(VarX:SortInt{}, \and{SortK{}}(
                \and{SortK{}}(a{}(), \top{SortK{}}()),
                \not{SortK{}}(inj{SortInt{}, SortK{}}(VarX:SortInt{})),
                \equals{SortInt{}, SortK{}}(VarX:SortInt{}, b{}())
            ))",
        )
        .unwrap();
        let int = || Sort::new("Int");
        let k = || Sort::new("K");
        let x = || Term::Variable {
            name: "X".into(),
            sort: Some(int()),
        };
        let constant = |name: &str| Term::Apply {
            label: Label::new(name),
            arguments: Vec::new(),
        };
        let ml = |label: InternalLabel, sorts: Vec<Sort>, arguments: Vec<Term>| Term::Apply {
            label: Label::with_parameters(label.as_str(), sorts),
            arguments,
        };
        let expected = ml(
            InternalLabel::Exists,
            vec![int(), k()],
            vec![
                x(),
                ml(
                    InternalLabel::And,
                    vec![k()],
                    vec![
                        constant("a"),
                        ml(InternalLabel::Not, vec![k()], vec![x()]),
                        ml(
                            InternalLabel::Equals,
                            vec![int(), k()],
                            vec![x(), constant("b")],
                        ),
                    ],
                ),
            ],
        );
        assert_eq!(convert(&pattern).unwrap(), expected);
    }

    /// A conversion fails with the first error met in depth-first order, where a node's own
    /// label and sorts come before its children and children come in order.
    #[test]
    fn reports_the_first_error_in_depth_first_order() {
        let next = "Next patterns currently unsupported";
        let siblings = parse_pattern(r"c{}(\next{SortK{}}(a{}()), d{Bad{}}())").unwrap();
        assert_eq!(convert(&siblings).unwrap_err().0, next);
        let parent = parse_pattern(r"d{Bad{}}(\next{SortK{}}(a{}()))").unwrap();
        let error = convert(&parent).unwrap_err().0;
        assert!(error != next && error.contains("Bad"), "{error}");
    }

    #[test]
    fn preserves_set_variable_names() {
        let pattern = parse_pattern("@VarX:SortSet{}").unwrap();
        assert_eq!(
            convert(&pattern).unwrap(),
            crate::kast::Term::Variable {
                name: "@X".into(),
                sort: Some(crate::kast::Sort::new("Set")),
            }
        );
    }
}
