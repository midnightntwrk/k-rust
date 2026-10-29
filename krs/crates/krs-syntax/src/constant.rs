//! `#[k::constant]` on a `const` item: a name for a ground constructor term.
//!
//! ```ignore
//! /// Interrupt flag register.
//! #[k::constant]
//! pub const IF: Int = 0xFF0F;
//! ```
//!
//! The type is a KRS sort and the value a ground constructor term: a
//! literal (`k::id!`, `k::bytes!` and `k::lexeme!` among them), a
//! constructor application whose arguments are ground terms, or another
//! constant. The compiler substitutes the value at every use, in
//! patterns as in results, so a value that applies a function or a builtin
//! operation, which could not be matched, is rejected (the compiler rejects
//! the functions it alone can recognise). Both the macro and the collector
//! parse the authored item here, so their provenance agrees.

use krs_ir::ProvenanceKey;
use proc_macro2::{Spacing, TokenStream, TokenTree};
use syn::parse::Parser as _;
use syn::spanned::Spanned;
use syn::{Expr, Ident, ItemConst};

use crate::parse::KeyAllocator;
use crate::term::TermExpression;
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TermSort, TokenRange};

/// A parsed `#[k::constant]` item.
#[derive(Clone, Debug)]
pub struct ConstantItem {
    item: ItemConst,
    sort: TermSort,
    value: TermExpression,
    name_key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
    /// The anchors of the constant's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl ConstantItem {
    /// Reads a `const` item; its attributes are not part of the constant.
    ///
    /// # Errors
    ///
    /// Returns [`SyntaxErrorKind::InvalidConstant`] for generics, a type
    /// that is not a sort, or a value that is not a ground constructor term.
    pub fn from_item(item: ItemConst) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
            return Err(invalid(
                "a constant is not generic: K has no parametric values",
                item.generics.span(),
            ));
        }
        let sort =
            crate::term_sort::parse_term_or_readable_sort((*item.ty).clone()).map_err(|_| {
                invalid(
                    "a constant's type is a KRS sort, such as `Int`, `Bool`, or a sort alias",
                    item.ty.span(),
                )
            })?;
        check_ground(&item.expr, &item.ident)?;
        let value = TermExpression::from_expression((*item.expr).clone())?;
        Self {
            item,
            sort,
            value,
            name_key: None,
            type_key: None,
            anchors: Vec::new(),
        }
        .keyed()
    }

    /// Keys the constant: its name, its type, its value as the value's
    /// payload, then the value's paths, nodes and record field names, which
    /// are numbered as the nodes of a rule result are, and its constant
    /// islands.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.name_key = Some(keys.key(
            ProvenanceRole::ConstantDeclaration,
            TokenRange::for_tokens(&self.item.ident)?,
        )?);
        self.type_key = Some(keys.key(
            ProvenanceRole::ConstantType,
            TokenRange::for_tokens(self.sort.ty())?,
        )?);
        self.value.clear_keys();
        let value = keys.key(
            ProvenanceRole::ConstantValue,
            TokenRange::for_tokens(&self.item.expr)?,
        )?;
        self.value.keying().2.set_payload(value);
        self.value
            .allocate_symbol_keys(&mut keys, ProvenanceRole::RuleRightPath)?;
        let (nodes, tree, term_keys) = self.value.keying();
        crate::rule::allocate_term_node_keys(
            &mut keys,
            nodes,
            term_keys,
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
            ProvenanceRole::RuleRightLiteral,
        )?;
        crate::term::allocate_record_field_keys(
            &mut keys,
            tree,
            term_keys,
            ProvenanceRole::RuleRightRecordFieldName,
        )?;
        // The constant islands, each kind numbered in preorder, as in an
        // initializer.
        crate::state_rule::allocate_claim_node_keys(&mut keys, [(nodes, &mut *term_keys)])?;
        crate::term::allocate_lexeme_keys(&mut keys, nodes, term_keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// The key of the constant name.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of the declared type.
    #[must_use]
    pub const fn type_key(&self) -> Option<&ProvenanceKey> {
        self.type_key.as_ref()
    }

    /// Returns the authored item.
    #[must_use]
    pub const fn item(&self) -> &ItemConst {
        &self.item
    }

    /// Returns the constant's name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns the declared sort.
    #[must_use]
    pub const fn sort(&self) -> &TermSort {
        &self.sort
    }

    /// Returns the value.
    #[must_use]
    pub const fn value(&self) -> &TermExpression {
        &self.value
    }

    /// Returns the name, type, and value anchors, and the value's nodes,
    /// which are numbered as the nodes of a rule result are.
    ///
    /// The value's payload key is the constant's `constant_value` key.
    ///
    /// # Errors
    ///
    /// None: the constant was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }
}

impl crate::KrsSyntax for ConstantItem {
    /// Reads a `const` item from tokens, rejecting a `static` with the
    /// constant's diagnostic.
    fn parse_tokens(tokens: proc_macro2::TokenStream) -> Result<Self, SyntaxError> {
        match parse_item(tokens)? {
            syn::Item::Const(item) => Self::from_item(item),
            syn::Item::Static(item) => Err(invalid(
                "`#[k::constant]` names a value with `const`, not `static`: a constant has no storage",
                item.static_token.span(),
            )),
            other => Err(invalid(
                "`#[k::constant]` applies to a `const` item",
                other.span(),
            )),
        }
    }
}

fn invalid(reason: &str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidConstant {
            reason: reason.to_owned(),
        },
        span,
    )
}

/// Checks that `expression` is built of literals, constructor applications,
/// and paths only. A path is another constant or a unit constructor: a
/// constant has no binders, so no name in it is a variable. `k::id!`,
/// `k::bytes!` and `k::lexeme!` each denote one constant of their sort, so
/// they are literals too. Notation such as `a.add::<Int>(b)` or `a && b` and
/// the other term macros are builtin operations or non-constructor terms, so
/// they are rejected here, where their authored span is still at hand.
/// Parses the item in `tokens`. A `const` value that holds `name @ pattern`, which no Rust
/// expression holds, is read as one term with the pattern grammar
/// ([`crate::term::parse_term_expression`]), so that the position table refuses the alias in the
/// value, at its own tokens, as it does in a fn body.
fn parse_item(tokens: TokenStream) -> Result<syn::Item, SyntaxError> {
    let error = match syn::parse2::<syn::Item>(tokens.clone()) {
        Ok(item) => return Ok(item),
        Err(error) => error,
    };
    let mut tokens = tokens.into_iter().collect::<Vec<_>>();
    // `const NAME: Type = VALUE;`: the value runs from the item's first `=` to its final `;`.
    let equals = tokens.iter().position(
        |token| matches!(token, TokenTree::Punct(punct) if punct.as_char() == '=' && punct.spacing() == Spacing::Alone),
    );
    let semicolon =
        matches!(tokens.last(), Some(TokenTree::Punct(punct)) if punct.as_char() == ';');
    let Some(equals) = equals.filter(|&equals| semicolon && equals + 2 < tokens.len()) else {
        return Err(error.into());
    };
    let value = tokens[equals + 1..tokens.len() - 1]
        .iter()
        .cloned()
        .collect::<TokenStream>();
    if crate::term::find_pattern_alias(&value).is_none() {
        return Err(error.into());
    }
    let mut placeholder = proc_macro2::Literal::u8_unsuffixed(0);
    placeholder.set_span(tokens[equals + 1].span());
    let end = tokens.len() - 1;
    tokens.splice(equals + 1..end, [TokenTree::Literal(placeholder)]);
    let syn::Item::Const(mut item) = syn::parse2::<syn::Item>(tokens.into_iter().collect())? else {
        return Err(error.into());
    };
    item.expr = Box::new(crate::term::parse_term_expression.parse2(value)?);
    Ok(syn::Item::Const(item))
}

fn check_ground(expression: &Expr, name: &Ident) -> Result<(), SyntaxError> {
    let not_ground = |what: &str, span: proc_macro2::Span| {
        Err(invalid(
            &format!(
                "the value of constant `{name}` must be a ground constructor term (a literal, a constructor application of ground terms, or another constant), so that it is matchable wherever it is used; {what} is not one"
            ),
            span,
        ))
    };
    let plain = |path: &syn::Path| {
        path.segments
            .iter()
            .all(|segment| segment.arguments.is_none())
    };
    match expression {
        Expr::Paren(inner) => check_ground(&inner.expr, name),
        Expr::Group(inner) => check_ground(&inner.expr, name),
        // A literal is ground. A term no Rust expression holds (`name @ pattern`, [`parse_item`])
        // is left to the term walker, which refuses its construct, at the construct, as no ground
        // term.
        Expr::Lit(_) | Expr::Verbatim(_) => Ok(()),
        Expr::Macro(island) if crate::term::is_constant_island_macro(&island.mac.path) => Ok(()),
        Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Neg(_),
            expr,
            ..
        }) if matches!(**expr, Expr::Lit(_)) => Ok(()),
        Expr::Path(path) if path.qself.is_none() && plain(&path.path) => Ok(()),
        Expr::Call(call) => {
            let Expr::Path(head) = &*call.func else {
                return not_ground("a call of a computed head", call.func.span());
            };
            if head.qself.is_some() || !plain(&head.path) {
                return not_ground("a parametric production's turbofish", head.span());
            }
            call.args
                .iter()
                .try_for_each(|argument| check_ground(argument, name))
        }
        Expr::Struct(record) if record.rest.is_none() && record.qself.is_none() => {
            if !plain(&record.path) {
                return not_ground("a parametric production's turbofish", record.path.span());
            }
            record
                .fields
                .iter()
                .try_for_each(|field| check_ground(&field.expr, name))
        }
        // An index or a collection method denotes the application of a collection's function,
        // as a call does, and its value is checked as the call's: the applied head says it
        // computes (`krs::analysis::constant-applies-function`).
        Expr::Index(index) => {
            check_ground(&index.expr, name)?;
            check_ground(&index.index, name)
        }
        Expr::MethodCall(call) if crate::notation::is_collection_notation(expression) => {
            check_ground(&call.receiver, name)?;
            call.args
                .iter()
                .try_for_each(|argument| check_ground(argument, name))
        }
        Expr::MethodCall(_) | Expr::Binary(_) | Expr::Unary(_) => {
            not_ground("a builtin operation", expression.span())
        }
        other => not_ground("this expression", other.span()),
    }
}

#[cfg(test)]
impl ConstantItem {
    /// Records the keys of the name, the type, the value (its payload, at
    /// the item's value expression) and the value's nodes.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.name_key.as_ref(), &self.item.ident)?;
        nodes.push_tokens(self.type_key.as_ref(), self.sort.ty())?;
        nodes.push_tokens(self.value.keys().payload(), &self.item.expr)?;
        assert!(self.value.keys().term().is_none());
        self.value.keyed_parts(nodes)
    }
}
