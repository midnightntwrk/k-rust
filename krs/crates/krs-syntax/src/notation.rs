//! Expression notation for builtin applications: the short-circuit Boolean
//! connectives `a && b` and `a || b`, and domain method calls
//! `recv.op::<D>(args..)`.
//!
//! Each form is notation for one builtin call and has no meaning of its own.
//! Term validation lowers a form to the application it denotes, whose head is
//! the operation's path below [`NOTATION_ROOT`]. Expansion replaces that root
//! with the facade's `builtin` module ([`notation_operation`]), so the head
//! names the facade's operation whatever the facade crate is called and
//! whether or not the author imported the operation's module. Code that rustc
//! checks receives the denoted calls through [`denote_notation`], with each
//! form's own spans.

use krs_ir::BuiltinOperation;
use proc_macro2::Span;
use quote::ToTokens;
use syn::parse::ParseStream;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{
    BinOp, Expr, ExprBinary, ExprCall, ExprMethodCall, ExprPath, GenericArgument, Ident, Path,
    PathArguments, PathSegment, Token, Type,
};

use crate::{SyntaxError, SyntaxErrorKind};

/// The first segment of the head of an application that notation denotes;
/// expansion replaces it with the facade's `builtin` module.
pub const NOTATION_ROOT: &str = "__krs_builtin";

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

/// Returns the operation path (`bool::and_then`) of an application head that
/// notation generated, or `None` for an authored head.
#[must_use]
pub fn notation_operation(head: &Path) -> Option<Path> {
    let first = head.segments.first()?;
    if head.leading_colon.is_some() || first.ident != NOTATION_ROOT {
        return None;
    }
    Some(Path {
        leading_colon: None,
        segments: head.segments.iter().skip(1).cloned().collect(),
    })
}

/// Whether `expression` is a notation form at its root: `&&`, `||`, or a
/// method call.
#[must_use]
pub fn is_expression_notation(expression: &Expr) -> bool {
    match expression {
        Expr::Binary(binary) => matches!(binary.op, BinOp::And(_) | BinOp::Or(_)),
        Expr::MethodCall(_) => true,
        _ => false,
    }
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
            if let Expr::Path(head) = &mut *call.func
                && let Some(operation) = notation_operation(&head.path)
            {
                let mut path = self.builtin.clone();
                path.segments.extend(operation.segments);
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
        Expr::Binary(binary) => connective(binary),
        Expr::MethodCall(call) => method_call(call).map(Some),
        _ => Ok(None),
    }
}

/// `a && b` is `bool::and_then(a, b)` and `a || b` is `bool::or_else(a, b)`;
/// the head spans the operator.
fn connective(binary: &ExprBinary) -> Result<Option<ExprCall>, SyntaxError> {
    let (operation, [first, last]) = match binary.op {
        BinOp::And(token) => ("and_then", token.spans),
        BinOp::Or(token) => ("or_else", token.spans),
        _ => return Ok(None),
    };
    crate::term::reject_attributes(&binary.attrs, binary.span())?;
    let head = generated_head("bool", operation, first, last);
    let mut arguments = Punctuated::new();
    arguments.push_value((*binary.left).clone());
    arguments.push_punct(Token![,](last));
    arguments.push_value((*binary.right).clone());
    Ok(Some(ExprCall {
        attrs: Vec::new(),
        func: Box::new(head),
        paren_token: syn::token::Paren(last),
        args: arguments,
    }))
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

/// `__krs_builtin::module::operation`, its root and module at `first` and its
/// operation at `last`.
fn generated_head(module: &str, operation: &str, first: Span, last: Span) -> Expr {
    let segment = |name: &str, span: Span| PathSegment::from(Ident::new(name, span));
    let mut segments = Punctuated::new();
    segments.push_value(segment(NOTATION_ROOT, first));
    segments.push_punct(Token![::](first));
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
/// expression a pattern failed to parse as: neither form is a Rust pattern, so
/// a left-hand side spells the operation as the call it denotes.
pub(crate) fn notation_in_pattern(expression: &Expr) -> Option<SyntaxError> {
    struct First(Option<SyntaxError>);
    impl<'ast> Visit<'ast> for First {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if self.0.is_some() {
                return;
            }
            if is_expression_notation(expression) {
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
    input
        .call(Expr::parse_without_eager_brace)
        .ok()
        .and_then(|expression| notation_in_pattern(&expression))
        .unwrap_or_else(|| error.into())
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
    let operation = notation_operation(&head.path).expect("notation generates a rooted head");
    let operation = crate::path::path_text(&operation);
    let (form, span) = match expression {
        Expr::Binary(binary) => (
            format!("`{}`", binary.op.to_token_stream()),
            binary.op.span(),
        ),
        Expr::MethodCall(method) => ("a method call".to_owned(), method.method.span()),
        _ => unreachable!("only notation forms reach here"),
    };
    notation_error(
        format!(
            "{form} is not a pattern: a left-hand side matches `{operation}` only as the call `{operation}(..)`"
        ),
        span,
    )
}
