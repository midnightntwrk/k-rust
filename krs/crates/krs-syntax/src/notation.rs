//! Expression notation for builtin applications: the short-circuit Boolean
//! connectives `a && b` and `a || b`, Rust's operators (`a + b`, `a < b`,
//! `!a`, `-a`), and domain method calls `recv.op::<D>(args..)`.
//!
//! Each form is notation for one builtin call and has no meaning of its own.
//! Term validation lowers a form to the application it denotes, marked
//! [`TermApplication::is_notation`](crate::TermApplication::is_notation),
//! whose head is the operation's path in the `builtin` module
//! (`bool::and_then`). An operator does not name its domain, so its head is
//! the operator's marker (`__operator::add`), which semantic analysis replaces
//! with the operation of the domain the operands' inferred sorts choose.
//! Expansion qualifies every head with the facade, so it names the facade's
//! marker whatever the facade crate is called and whether or not the author
//! imported the operation's module. Code that rustc checks receives the
//! denoted calls through [`denote_notation`], with each form's own spans.

use krs_ir::{BuiltinOperation, BuiltinOperator, OperatorReading};
use proc_macro2::Span;
use quote::ToTokens;
use syn::parse::ParseStream;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{
    BinOp, Expr, ExprBinary, ExprCall, ExprMethodCall, ExprPath, ExprUnary, GenericArgument, Ident,
    Path, PathArguments, PathSegment, Token, Type, UnOp,
};

use crate::{SyntaxError, SyntaxErrorKind};

/// Each method-call domain and the builtin module that holds its operations.
const DOMAINS: [(&str, &str); 6] = [
    ("Int", "int"),
    ("Bool", "bool"),
    ("String", "string"),
    ("Float", "float"),
    ("Bytes", "bytes"),
    ("K", "kequal"),
];

/// The domains a method-call turbofish may name, as prose.
const DOMAIN_LIST: &str = "`Int`, `Bool`, `String`, `Float`, `Bytes`, or `K`";

fn notation_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidExpressionNotation { reason }, span)
}

/// Whether `expression` is a notation form at its root: `&&`, `||`, an
/// operator, or a method call. A binary expression is always one, so a
/// compound assignment such as `a += b` is reported as notation it is not.
#[must_use]
pub fn is_expression_notation(expression: &Expr) -> bool {
    match expression {
        Expr::Binary(_) | Expr::MethodCall(_) => true,
        Expr::Unary(unary) => unary_operator(unary).is_some(),
        _ => false,
    }
}

/// The operator a unary expression applies: `!a`, or `-a` on anything but a
/// literal. The minus of `-1`, `-1.5`, or `-f64::INFINITY` belongs to the
/// literal, which is one token in patterns and results alike; `*a` is no
/// operator.
fn unary_operator(unary: &ExprUnary) -> Option<BuiltinOperator> {
    match unary.op {
        UnOp::Not(_) => Some(BuiltinOperator::Not),
        UnOp::Neg(_) => {
            let literal = match &*unary.expr {
                Expr::Lit(_) => true,
                Expr::Path(path) => {
                    path.qself.is_none()
                        && path.path.leading_colon.is_none()
                        && crate::term::float_constant_path(&path.path).is_some()
                }
                _ => false,
            };
            (!literal).then_some(BuiltinOperator::Neg)
        }
        _ => None,
    }
}

/// The operator a binary operator token applies, or `None` for `&&` and
/// `||`, which are connectives, and for a compound assignment.
const fn binary_operator(operator: &BinOp) -> Option<BuiltinOperator> {
    Some(match operator {
        BinOp::Add(_) => BuiltinOperator::Add,
        BinOp::Sub(_) => BuiltinOperator::Sub,
        BinOp::Mul(_) => BuiltinOperator::Mul,
        BinOp::Div(_) => BuiltinOperator::Div,
        BinOp::Rem(_) => BuiltinOperator::Rem,
        BinOp::Shl(_) => BuiltinOperator::ShiftLeft,
        BinOp::Shr(_) => BuiltinOperator::ShiftRight,
        BinOp::BitAnd(_) => BuiltinOperator::BitAnd,
        BinOp::BitOr(_) => BuiltinOperator::BitOr,
        BinOp::BitXor(_) => BuiltinOperator::BitXor,
        BinOp::Eq(_) => BuiltinOperator::Eq,
        BinOp::Ne(_) => BuiltinOperator::Ne,
        BinOp::Lt(_) => BuiltinOperator::Lt,
        BinOp::Le(_) => BuiltinOperator::Le,
        BinOp::Gt(_) => BuiltinOperator::Gt,
        BinOp::Ge(_) => BuiltinOperator::Ge,
        _ => return None,
    })
}

/// Replaces every notation form in `expression` with the call it denotes,
/// whose head is qualified by `builtin`, the facade's `builtin` module.
/// Forms inside macro invocations are left to the macro, and a malformed form,
/// which term validation rejects, is left as written.
pub fn denote_notation(expression: &mut Expr, builtin: &Path) {
    Denote { builtin }.visit_expr_mut(expression);
}

struct Denote<'a> {
    builtin: &'a Path,
}

impl VisitMut for Denote<'_> {
    fn visit_expr_mut(&mut self, expression: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expression);
        if let Ok(Some(mut call)) = denoted_call(expression) {
            if let Expr::Path(head) = &mut *call.func {
                let mut path = self.builtin.clone();
                path.segments.extend(head.path.segments.iter().cloned());
                head.path = path;
            }
            *expression = Expr::Call(call);
        }
    }
}

/// The builtin call that a notation form at the root of `expression` denotes,
/// with the form's operands as its arguments, or `None` for any other
/// expression.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidExpressionNotation`] for a method call
/// that names no domain, an unknown domain, or an operation its domain's
/// module does not define, or that has no operand to be its receiver.
pub(crate) fn denoted_call(expression: &Expr) -> Result<Option<ExprCall>, SyntaxError> {
    match expression {
        Expr::Binary(binary) => binary_call(binary).map(Some),
        Expr::Unary(unary) => unary_operator(unary)
            .map(|operator| unary_call(unary, operator))
            .transpose(),
        Expr::MethodCall(call) => method_call(call).map(Some),
        _ => Ok(None),
    }
}

/// `a && b` is `bool::and_then(a, b)`, `a || b` is `bool::or_else(a, b)`,
/// and `a + b` is the operator marker's call `__operator::add(a, b)`; the head
/// spans the operator.
fn binary_call(binary: &ExprBinary) -> Result<ExprCall, SyntaxError> {
    let (first, last) = token_spans(&binary.op);
    let head = match binary.op {
        BinOp::And(_) => generated_head("bool", "and_then", first, last),
        BinOp::Or(_) => generated_head("bool", "or_else", first, last),
        operator => {
            let Some(operator) = binary_operator(&operator) else {
                return Err(compound_assignment(&operator, first));
            };
            operator_head(operator, first, last)
        }
    };
    crate::term::reject_attributes(&binary.attrs, binary.span())?;
    let mut arguments = Punctuated::new();
    arguments.push_value((*binary.left).clone());
    arguments.push_punct(Token![,](last));
    arguments.push_value((*binary.right).clone());
    Ok(ExprCall {
        attrs: Vec::new(),
        func: Box::new(head),
        paren_token: syn::token::Paren(last),
        args: arguments,
    })
}

/// `!a` is `__operator::not(a)` and `-a` is `__operator::neg(a)`; the head
/// spans the operator.
fn unary_call(unary: &ExprUnary, operator: BuiltinOperator) -> Result<ExprCall, SyntaxError> {
    crate::term::reject_attributes(&unary.attrs, unary.span())?;
    let (first, last) = token_spans(&unary.op);
    let mut arguments = Punctuated::new();
    arguments.push_value((*unary.expr).clone());
    Ok(ExprCall {
        attrs: Vec::new(),
        func: Box::new(operator_head(operator, first, last)),
        paren_token: syn::token::Paren(last),
        args: arguments,
    })
}

/// The spans of an operator's first and last characters: `<=` is two tokens.
fn token_spans(operator: &impl ToTokens) -> (Span, Span) {
    let spans = operator
        .to_token_stream()
        .into_iter()
        .map(|token| token.span())
        .collect::<Vec<_>>();
    let first = spans.first().copied().unwrap_or_else(Span::call_site);
    (first, spans.last().copied().unwrap_or(first))
}

/// `__operator::name`, the marker of an operator whose domain semantic
/// analysis chooses.
fn operator_head(operator: BuiltinOperator, first: Span, last: Span) -> Expr {
    let marker = operator.facade_marker();
    generated_head(marker.module, marker.name, first, last)
}

/// The error for `a += b` and the other compound assignments: a term
/// denotes a value and has no place to assign to.
fn compound_assignment(operator: &BinOp, span: Span) -> SyntaxError {
    let written = operator.to_token_stream().to_string().replace(' ', "");
    let reason = match written.strip_suffix('=').and_then(|base| {
        BuiltinOperator::ALL
            .into_iter()
            .find(|operator| operator.arity() == 2 && operator.symbol() == base)
    }) {
        Some(operator) => format!(
            "`{written}` assigns, and a term has nothing to assign to; write the value `a {} b`",
            operator.symbol()
        ),
        None => format!("`{written}` is not a term operator"),
    };
    notation_error(reason, span)
}

/// The calls a left-hand side writes for `operator`, one per domain that
/// defines it: `` `int::add(..)`, `string::concat(..)`, or `float::add(..)` ``.
fn operator_calls(operator: BuiltinOperator) -> String {
    let calls = operator
        .domains()
        .into_iter()
        .filter_map(|domain| operator.reading(domain))
        .map(|reading| {
            let spec = reading.operation().spec();
            match reading {
                OperatorReading::Operation(_) => {
                    format!("`{}::{}(..)`", spec.rust_module, spec.rust_name)
                }
                OperatorReading::IntNegation => {
                    format!("`{}::{}(0, ..)`", spec.rust_module, spec.rust_name)
                }
            }
        })
        .collect::<Vec<_>>();
    match calls.as_slice() {
        [first, second] => format!("{first} or {second}"),
        [rest @ .., last] if !rest.is_empty() => format!("{}, or {last}", rest.join(", ")),
        _ => calls.concat(),
    }
}

/// `recv.op::<D>(args..)` is `d::op(recv, args..)`, where `d` is the builtin
/// module of domain `D`; the head takes the method name's span.
fn method_call(call: &ExprMethodCall) -> Result<ExprCall, SyntaxError> {
    crate::term::reject_attributes(&call.attrs, call.span())?;
    let name = syn::ext::IdentExt::unraw(&call.method).to_string();
    let span = call.method.span();
    let Some(turbofish) = &call.turbofish else {
        return Err(missing_domain(&name, span));
    };
    let domain = match (turbofish.args.len(), turbofish.args.first()) {
        (1, Some(GenericArgument::Type(Type::Path(domain))))
            if domain.qself.is_none()
                && domain.path.leading_colon.is_none()
                && domain.path.segments.len() == 1
                && matches!(domain.path.segments[0].arguments, PathArguments::None) =>
        {
            &domain.path.segments[0].ident
        }
        _ => {
            return Err(notation_error(
                format!(
                    "the turbofish of a method call names one builtin domain by its bare name: {DOMAIN_LIST}, as in `{name}::<Int>`"
                ),
                turbofish.span(),
            ));
        }
    };
    let Some((_, module)) = DOMAINS.iter().find(|(candidate, _)| domain == candidate) else {
        return Err(notation_error(
            format!("`{domain}` is not a builtin domain; a method call names {DOMAIN_LIST}"),
            domain.span(),
        ));
    };
    let Some(operation) = BuiltinOperation::ALL.iter().find(|operation| {
        operation.spec().rust_module == *module && operation.spec().rust_name == name
    }) else {
        let elsewhere = defining_domains(&name);
        let hint = match elsewhere.len() {
            0 => String::new(),
            1 => format!("; {} exists", turbofish_list(&name, &elsewhere)),
            _ => format!("; {} exist", turbofish_list(&name, &elsewhere)),
        };
        return Err(notation_error(
            format!("the builtin module `{module}` has no operation `{name}`{hint}"),
            span,
        ));
    };
    if operation.argument_sorts().is_empty() {
        return Err(notation_error(
            format!(
                "`{module}::{name}` takes no operands, so it has no receiver; write the call `{module}::{name}()`"
            ),
            span,
        ));
    }
    let mut arguments = Punctuated::new();
    arguments.push_value((*call.receiver).clone());
    for argument in &call.args {
        arguments.push_punct(Token![,](span));
        arguments.push_value(argument.clone());
    }
    Ok(ExprCall {
        attrs: Vec::new(),
        func: Box::new(generated_head(module, &name, span, span)),
        paren_token: call.paren_token,
        args: arguments,
    })
}

/// The error for a method call without a domain turbofish, listing the
/// domains whose module defines the operation.
fn missing_domain(name: &str, span: Span) -> SyntaxError {
    let domains = defining_domains(name);
    let reason = if domains.is_empty() {
        format!(
            "`.{name}(..)` is not a builtin operation of any domain; a term's only methods are builtin operations, written `receiver.operation::<Domain>(..)`"
        )
    } else {
        format!(
            "a method call names its builtin domain in a turbofish: write {}",
            turbofish_list(name, &domains)
        )
    };
    notation_error(reason, span)
}

/// The domains, in table order, whose module defines an operation `name`.
fn defining_domains(name: &str) -> Vec<&'static str> {
    DOMAINS
        .iter()
        .filter(|(_, module)| {
            BuiltinOperation::ALL.iter().any(|operation| {
                operation.spec().rust_module == *module && operation.spec().rust_name == name
            })
        })
        .map(|(domain, _)| *domain)
        .collect()
}

/// `` `lt::<Int>`, `lt::<String>`, or `lt::<Float>` `` for the domains of `name`.
fn turbofish_list(name: &str, domains: &[&str]) -> String {
    let forms = domains
        .iter()
        .map(|domain| format!("`{name}::<{domain}>`"))
        .collect::<Vec<_>>();
    match forms.as_slice() {
        [first, second] => format!("{first} or {second}"),
        [rest @ .., last] if !rest.is_empty() => format!("{}, or {last}", rest.join(", ")),
        _ => forms.concat(),
    }
}

/// `module::operation`, its module at `first` and its operation at `last`.
fn generated_head(module: &str, operation: &str, first: Span, last: Span) -> Expr {
    let segment = |name: &str, span: Span| PathSegment::from(Ident::new(name, span));
    let mut segments = Punctuated::new();
    segments.push_value(segment(module, first));
    segments.push_punct(Token![::](last));
    segments.push_value(segment(operation, last));
    Expr::Path(ExprPath {
        attrs: Vec::new(),
        qself: None,
        path: Path {
            leading_colon: None,
            segments,
        },
    })
}

/// The error for the first notation form in `expression`, which is the
/// expression a pattern failed to parse as: no form is a Rust pattern, so a
/// left-hand side spells the operation as the call it denotes.
pub(crate) fn notation_in_pattern(expression: &Expr) -> Option<SyntaxError> {
    struct First(Option<SyntaxError>);
    impl<'ast> Visit<'ast> for First {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if self.0.is_some() {
                return;
            }
            // `|` between patterns is an alternative, not the operator.
            let alternative =
                matches!(expression, Expr::Binary(binary) if matches!(binary.op, BinOp::BitOr(_)));
            if is_expression_notation(expression) && !alternative {
                self.0 = Some(pattern_error(expression));
                return;
            }
            syn::visit::visit_expr(self, expression);
        }
    }
    let mut first = First(None);
    first.visit_expr(expression);
    first.0
}

/// `error`, the failure to parse the tokens at `input` as a pattern, or the
/// notation error when those tokens are an expression with a notation form.
pub(crate) fn pattern_parse_error(input: ParseStream<'_>, error: syn::Error) -> SyntaxError {
    notation_at(input).unwrap_or_else(|| error.into())
}

/// The notation error when the tokens at `input`, where a pattern was
/// expected, begin an expression with a notation form. The expression is
/// parsed in full, so a record such as `Check { a: n && m }` is one
/// expression; a pattern parser may instead stop inside it, at the first
/// token that no pattern continues with.
pub(crate) fn notation_at(input: ParseStream<'_>) -> Option<SyntaxError> {
    input
        .fork()
        .parse::<Expr>()
        .ok()
        .and_then(|expression| notation_in_pattern(&expression))
}

fn pattern_error(expression: &Expr) -> SyntaxError {
    let call = match denoted_call(expression) {
        Ok(Some(call)) => call,
        Ok(None) => unreachable!("only notation forms reach here"),
        Err(error) => return error,
    };
    let Expr::Path(head) = &*call.func else {
        unreachable!("notation generates a path head");
    };
    let (form, operator, span) = match expression {
        Expr::Binary(binary) => (
            binary.op.to_token_stream().to_string().replace(' ', ""),
            binary_operator(&binary.op),
            token_spans(&binary.op).0,
        ),
        Expr::Unary(unary) => (
            unary.op.to_token_stream().to_string(),
            unary_operator(unary),
            token_spans(&unary.op).0,
        ),
        Expr::MethodCall(method) => {
            let operation = crate::path::path_text(&head.path);
            return notation_error(
                format!(
                    "a method call is not a pattern: a left-hand side matches `{operation}` only as the call `{operation}(..)`"
                ),
                method.method.span(),
            );
        }
        _ => unreachable!("only notation forms reach here"),
    };
    let reason = if let Some(operator) = operator {
        format!(
            "`{form}` is not a pattern: a left-hand side matches a builtin operation only as its call, {}",
            operator_calls(operator)
        )
    } else {
        let operation = crate::path::path_text(&head.path);
        format!(
            "`{form}` is not a pattern: a left-hand side matches `{operation}` only as the call `{operation}(..)`"
        )
    };
    notation_error(reason, span)
}
