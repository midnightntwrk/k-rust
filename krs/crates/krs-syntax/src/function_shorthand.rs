//! `#[k::function(..)]` on a `fn`: the function symbol declared by its
//! signature, and with a body its one defining equation.
//!
//! ```ignore
//! #[k::function(total, internal)]
//! pub fn Byte(value: k::Term<Int>) -> k::Term<Int> {
//!     k::term![int::rem_euclid(value, 256)]
//! }
//! ```
//!
//! is the struct `Byte { pub value: k::Term<Int> }` with
//! `#[k::function(total, internal, sort = Int)]` and the equation
//! `fn byte(Byte(value): k::Term<Int>) -> k::Term<Int> { .. }`. A `fn`
//! without a body (`pub fn R8(index: k::Term<Int>) -> k::Term<Operand>;`)
//! declares the symbol only. A body that is an `if` chain or a `match`
//! defines one equation per branch (`branches`). Both the macro and the
//! collector lower the authored item here, so the struct and the equations
//! carry the same authored spans on both sides and their provenance agrees
//! byte for byte.

mod branches;

use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};
use quote::{ToTokens, quote};
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream, Parser as _};
use syn::spanned::Spanned;
use syn::{Attribute, Block, FnArg, Ident, ItemFn, ItemStruct, Pat, ReturnType, Signature, Token};

use crate::rule::NegativeLiteralSpans;
use crate::surface::{AttributeMacro, helper_entry};
use crate::term_sort::parse_typed_term_sort;
use crate::{ConstructorDeclaration, FunctionAttribute, RuleItem, SyntaxError, SyntaxErrorKind};

/// A `fn` item that may end with `;` instead of a body: syn reads such an
/// item as `Item::Verbatim`, rustc accepts it as attribute-macro input.
#[derive(Clone, Debug)]
pub struct ShorthandItem {
    /// Outer attributes in source order.
    pub attrs: Vec<Attribute>,
    /// The declared visibility.
    pub vis: syn::Visibility,
    /// The complete signature.
    pub sig: Signature,
    /// The body, absent for a declaration that ends with `;`.
    pub body: Option<Block>,
    /// The tokens between the body's braces as written, when the item was
    /// parsed from tokens: syn joins a pattern's `-1` into one literal, and a
    /// branching body's arm patterns take their `-` spans from these.
    body_tokens: Option<TokenStream>,
}

impl Parse for ShorthandItem {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        let sig: Signature = input.parse()?;
        let (body, body_tokens) = if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
            (None, None)
        } else {
            let group: Group = input.parse()?;
            (Some(shorthand_body(&group)?), Some(group.stream()))
        };
        Ok(Self {
            attrs,
            vis,
            sig,
            body,
            body_tokens,
        })
    }
}

/// The body in `group`. A body that holds `name @ pattern`, which no Rust block holds, is read as
/// one term with the pattern grammar ([`crate::term::parse_term_expression`]), as a rule's or an
/// equation's body is, so that the position table refuses the alias in the result, at its own
/// tokens.
fn shorthand_body(group: &Group) -> syn::Result<Block> {
    let error = match syn::parse2::<Block>(TokenTree::Group(group.clone()).into()) {
        Ok(body) => return Ok(body),
        Err(error) => error,
    };
    if crate::term::find_pattern_alias(&group.stream()).is_none() {
        return Err(error);
    }
    let result = crate::term::parse_term_expression.parse2(group.stream())?;
    Ok(Block {
        brace_token: syn::token::Brace(group.delim_span()),
        stmts: vec![syn::Stmt::Expr(result, None)],
    })
}

impl ShorthandItem {
    /// Reads an item as a shorthand candidate: an ordinary `fn`, or a
    /// bodiless one that syn keeps verbatim.
    #[must_use]
    pub fn from_item(item: &syn::Item) -> Option<Self> {
        match item {
            syn::Item::Fn(item) => Some(Self {
                attrs: item.attrs.clone(),
                vis: item.vis.clone(),
                sig: item.sig.clone(),
                body: Some((*item.block).clone()),
                body_tokens: None,
            }),
            syn::Item::Verbatim(tokens) => syn::parse2(tokens.clone()).ok(),
            _ => None,
        }
    }

    /// Renders the item back to tokens, with `;` for a missing body.
    #[must_use]
    pub fn to_token_stream(&self) -> TokenStream {
        let attrs = &self.attrs;
        let vis = &self.vis;
        let sig = &self.sig;
        let body = self
            .body
            .as_ref()
            .map_or_else(|| quote!(;), ToTokens::to_token_stream);
        quote!(#(#attrs)* #vis #sig #body)
    }
}

/// One equation a function shorthand's body defines.
#[derive(Clone, Debug)]
pub struct ShorthandEquation {
    item: ItemFn,
    /// The `label = ".."` written on the function's `#[k::function(..)]`, which names the one
    /// equation its body defines.
    label: Option<syn::LitStr>,
    /// The `owise` key of a catch-all arm, spanned at the arm.
    owise: Option<Ident>,
    /// The negative literals of the patterns the head takes from arms.
    signs: NegativeLiteralSpans,
}

impl ShorthandEquation {
    /// The equation fn, its guard a `#[k::requires]` attribute.
    #[must_use]
    pub const fn item(&self) -> &ItemFn {
        &self.item
    }

    /// The equation's `#[k::equation(..)]` keys: the function's label, which names the one
    /// equation, and `owise` for the catch-all arm of the body's `match`.
    #[must_use]
    pub fn equation_keys(&self) -> TokenStream {
        let label = self.label.as_ref().map(|label| quote!(label = #label));
        let owise = self.owise.as_ref();
        match (label, owise) {
            (Some(label), Some(owise)) => quote!(#label, #owise),
            (Some(label), None) => label,
            (None, owise) => owise.map_or_else(TokenStream::new, ToTokens::to_token_stream),
        }
    }

    /// Validates the equation fn as a rule item.
    ///
    /// # Errors
    ///
    /// The errors of [`RuleItem::from_equation_item`].
    pub fn rule(&self) -> Result<RuleItem, SyntaxError> {
        RuleItem::from_shorthand_item(self.item.clone(), self.signs.clone())
    }
}

/// The struct and the equations a function shorthand stands for.
#[derive(Clone, Debug)]
pub struct FunctionShorthand {
    attribute: FunctionAttribute,
    structure: ItemStruct,
    equations: Vec<ShorthandEquation>,
    /// The authored result sort inside `k::Term<..>`, such as `Set<Int>`.
    sort_type: syn::Type,
}

impl FunctionShorthand {
    /// Lowers `#[k::function(attribute)]` on `item`, whose remaining
    /// attributes are `item.attrs`: `#[k::requires]` goes to the equation,
    /// `#[cfg]` to both items, everything else to the struct.
    ///
    /// # Errors
    ///
    /// Rejects every shape outside the shorthand
    /// (`krs::syntax::invalid-function-shorthand`), the attribute's own
    /// errors, and an omitted `syntax` on a production that is program syntax.
    pub fn lower(attribute: TokenStream, item: ShorthandItem) -> Result<Self, SyntaxError> {
        let ShorthandItem {
            attrs,
            vis,
            sig,
            body,
            body_tokens,
        } = item;
        validate_signature(&sig)?;
        let ReturnType::Type(_, result_type) = &sig.output else {
            return Err(shorthand_error(
                "a function declared by a `fn` returns its sort, `-> k::Term<Sort>`",
                sig.ident.span(),
            ));
        };
        let result_sort = parse_typed_term_sort((**result_type).clone())?;
        if result_sort.is_dynamic() || result_sort.is_predicate() {
            return Err(shorthand_error(
                "a function declared by a `fn` returns `k::Term<Sort>` with a sort alias or builtin sort, such as `k::Term<Exp>` or `k::Term<Int>`",
                result_type.span(),
            ));
        }
        let (attribute, label) = take_label(attribute)?;
        let mut attribute = FunctionAttribute::parse_shorthand_tokens(
            attribute,
            result_sort.sort(),
            result_sort.arguments(),
        )?;
        // An equation's subject and result are applications of the function,
        // whose element types its declaration states: the equations name
        // only the sort.
        let equation_type = crate::term_sort::without_collection_arguments(result_type);
        if let Some(hook) = attribute.hook()
            && body.is_some()
        {
            return Err(shorthand_error(
                "a hooked function takes its values from the backend, so it has no body; end the declaration with `;`",
                hook.range()?.first(),
            ));
        }

        let ItemAttributes {
            structure: struct_attrs,
            equation: equation_attrs,
            requires,
            cfg,
        } = item_attributes(attrs, body.is_some())?;

        let mut fields = Vec::new();
        let mut arguments = Vec::new();
        for input in &sig.inputs {
            let (name, ty) = parameter(input)?;
            fields.push(quote!(#vis #name: #ty));
            arguments.push(name);
        }
        let name = &sig.ident;
        // Only K rules apply a function, so a struct that is not `pub` has
        // fields Rust never reads.
        let dead_code =
            (!matches!(vis, syn::Visibility::Public(_))).then(|| quote!(#[allow(dead_code)]));
        let structure: ItemStruct = syn::parse2(quote! {
            #(#struct_attrs)*
            #dead_code
            #vis struct #name {
                #(#fields,)*
            }
        })?;
        let declaration = ConstructorDeclaration::from_item(structure.clone())?;
        attribute.complete_default_syntax(&declaration)?;
        attribute.production().validate_declaration(&declaration)?;

        let mut equations = match body {
            None => Vec::new(),
            Some(body) => {
                let lowering = branches::Lowering {
                    function: name,
                    parameters: &arguments,
                    parentheses: sig.paren_token.span.join(),
                    result_type: &equation_type,
                    cfg: &cfg,
                    requires: &requires,
                };
                let tokens = body_tokens.unwrap_or_else(|| {
                    match body.to_token_stream().into_iter().next() {
                        Some(TokenTree::Group(group)) => group.stream(),
                        _ => TokenStream::new(),
                    }
                });
                if let Some(equations) = branches::lower(&lowering, &body, tokens)? {
                    equations
                } else {
                    vec![single_equation(&lowering, &equation_attrs, &body)?]
                }
            }
        };
        if let Some(label) = label {
            label_equation(&mut equations, label)?;
        }
        Ok(Self {
            attribute,
            structure,
            equations,
            sort_type: crate::term_sort::term_sort_type(result_type)
                .cloned()
                .unwrap_or_else(|| (**result_type).clone()),
        })
    }

    /// The result sort as the long form's `sort = ..` states it: the sort
    /// inside the return type's `k::Term<..>`, with the element types of a
    /// typed collection (`Set<Int>`).
    #[must_use]
    pub const fn sort_type(&self) -> &syn::Type {
        &self.sort_type
    }

    /// The completed function attribute: the sort from the return type, and
    /// the default syntax when none was written.
    #[must_use]
    pub const fn attribute(&self) -> &FunctionAttribute {
        &self.attribute
    }

    /// The function struct, made of authored tokens.
    #[must_use]
    pub const fn structure(&self) -> &ItemStruct {
        &self.structure
    }

    /// The equations a body defines: one, named [`equation_name`] of the
    /// function, for a body that is a term; one per branch for an `if` chain
    /// or a `match`; none for a declaration that ends with `;`.
    #[must_use]
    pub fn equations(&self) -> &[ShorthandEquation] {
        &self.equations
    }
}

/// A shorthand item's attributes, sorted by the items they go to.
struct ItemAttributes {
    /// The struct's: everything but `#[k::requires]`.
    structure: Vec<Attribute>,
    /// The single equation's: `#[k::requires]` and `#[cfg]`.
    equation: Vec<Attribute>,
    requires: Vec<Attribute>,
    cfg: Vec<Attribute>,
}

/// Sorts the item's attributes: `#[k::requires]` goes to the equations,
/// `#[cfg]` to every item, everything else to the struct.
fn item_attributes(attrs: Vec<Attribute>, has_body: bool) -> Result<ItemAttributes, SyntaxError> {
    let mut sorted = ItemAttributes {
        structure: Vec::new(),
        equation: Vec::new(),
        requires: Vec::new(),
        cfg: Vec::new(),
    };
    for attribute in attrs {
        match helper_entry(attribute.path()) {
            Some(AttributeMacro::Requires) => {
                if !has_body {
                    return Err(shorthand_error(
                        "`#[k::requires]` guards the equation a body defines; a declaration ending with `;` has none",
                        attribute.span(),
                    ));
                }
                sorted.requires.push(attribute.clone());
                sorted.equation.push(attribute);
            }
            Some(entry) => {
                return Err(shorthand_error(
                    &shorthand_helper_reason(entry),
                    attribute.span(),
                ));
            }
            None if attribute.path().is_ident("cfg") => {
                sorted.cfg.push(attribute.clone());
                sorted.equation.push(attribute.clone());
                sorted.structure.push(attribute);
            }
            None => sorted.structure.push(attribute),
        }
    }
    Ok(sorted)
}

/// The one equation of a body that is a term: `fn byte(Byte(value): S) -> S
/// { body }`, named [`equation_name`] of the function.
fn single_equation(
    lowering: &branches::Lowering<'_>,
    attributes: &[Attribute],
    body: &Block,
) -> Result<ShorthandEquation, SyntaxError> {
    let name = lowering.function;
    let arguments = lowering.parameters;
    let result_type = lowering.result_type;
    let equation_name = equation_ident(name)?;
    // The subject `Byte(value)`: the head is the authored name, and its
    // parentheses carry the parameter list's span.
    let mut group = Group::new(Delimiter::Parenthesis, quote!(#(#arguments),*));
    group.set_span(lowering.parentheses);
    let subject = TokenStream::from_iter([TokenTree::Ident(name.clone()), TokenTree::Group(group)]);
    let item = crate::term::parse_fn_item(quote! {
        #(#attributes)*
        fn #equation_name(#subject: #result_type) -> #result_type #body
    })?;
    Ok(ShorthandEquation {
        item,
        label: None,
        owise: None,
        signs: NegativeLiteralSpans::default(),
    })
}

/// Gives `label` to the one equation of `equations`: a label names one sentence, so a body that
/// defines several equations (one per branch) or none is refused at the label.
fn label_equation(
    equations: &mut [ShorthandEquation],
    label: syn::LitStr,
) -> Result<(), SyntaxError> {
    let [equation] = equations else {
        return Err(shorthand_error(
            &format!(
                "a label names one sentence, and this function's body defines {}: one equation per branch of its `if` chain or `match`, or none for a declaration ending with `;`",
                match equations.len() {
                    0 => "no equation".to_owned(),
                    count => format!("{count} equations"),
                }
            ),
            label.span(),
        ));
    };
    equation.label = Some(label);
    Ok(())
}

/// Takes `label = ".."` out of a function shorthand's `#[k::function(..)]` payload: it names the
/// equation the body defines, not the function's production. Returns the payload without it, and
/// the label: the payload unchanged when it has no label, and otherwise its other entries with
/// the commas written after them.
///
/// # Errors
///
/// A repeated label, and a label value that is no portable K rule label.
pub fn take_label(
    attribute: TokenStream,
) -> Result<(TokenStream, Option<syn::LitStr>), SyntaxError> {
    // Each entry with the comma written after it.
    let mut entries: Vec<(Vec<TokenTree>, Option<TokenTree>)> = Vec::new();
    let mut entry = Vec::new();
    for token in attribute.clone() {
        match &token {
            TokenTree::Punct(punct) if punct.as_char() == ',' => {
                entries.push((std::mem::take(&mut entry), Some(token)));
            }
            _ => entry.push(token),
        }
    }
    entries.push((entry, None));
    let is_label = |entry: &[TokenTree]| {
        matches!(
            entry,
            [TokenTree::Ident(key), TokenTree::Punct(equals), _, ..]
                if key == "label" && equals.as_char() == '='
        )
    };
    if !entries.iter().any(|(entry, _)| is_label(entry)) {
        return Ok((attribute, None));
    }
    // A comma after the last entry kept stays only if it ended the payload as written.
    let ends_with_label = entries
        .iter()
        .rev()
        .find(|(entry, _)| !entry.is_empty())
        .is_some_and(|(entry, _)| is_label(entry));
    let mut label = None;
    let mut kept = Vec::new();
    for (entry, comma) in entries {
        if !is_label(&entry) {
            if !entry.is_empty() {
                kept.push((entry, comma));
            }
            continue;
        }
        if label.is_some() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::DuplicateArgument { name: "label" },
                entry[0].span(),
            ));
        }
        let value: syn::Expr = syn::parse2(entry[2..].iter().cloned().collect())?;
        label = Some(crate::attribute::parse_rule_label_value(value).map_err(
            |error| match error {
                crate::parse::ParseError::Structured(error) => error,
                crate::parse::ParseError::Syn(error) => SyntaxError::from(error),
            },
        )?);
    }
    let mut payload = TokenStream::new();
    let last = kept.len().saturating_sub(1);
    for (index, (entry, comma)) in kept.into_iter().enumerate() {
        payload.extend(entry);
        if index < last || !ends_with_label {
            payload.extend(comma);
        }
    }
    Ok((payload, label))
}

/// The name of a shorthand function's equation: the upper camel case function
/// name in snake case (`FieldX` → `field_x`, `R8` → `r8`, `HLValue` →
/// `hl_value`), the name a hand-written equation of the struct conventionally
/// takes.
#[must_use]
pub fn equation_name(function: &str) -> String {
    let characters = function.chars().collect::<Vec<_>>();
    let mut name = String::with_capacity(function.len() + 4);
    for (index, character) in characters.iter().enumerate() {
        if character.is_uppercase() && index > 0 {
            let previous = characters[index - 1];
            let next_lower = characters
                .get(index + 1)
                .is_some_and(|next| next.is_lowercase());
            if previous.is_lowercase()
                || previous.is_ascii_digit()
                || (previous.is_uppercase() && next_lower)
            {
                name.push('_');
            }
        }
        name.extend(character.to_lowercase());
    }
    name
}

fn equation_ident(name: &Ident) -> Result<Ident, SyntaxError> {
    let text = equation_name(&name.unraw().to_string());
    if syn::parse_str::<Ident>(&text).is_ok() {
        Ok(Ident::new(&text, name.span()))
    } else if matches!(text.as_str(), "self" | "super" | "crate" | "_") {
        Err(shorthand_error(
            "this function name gives its equation a name Rust reserves; rename the function",
            name.span(),
        ))
    } else {
        Ok(Ident::new_raw(&text, name.span()))
    }
}

fn validate_signature(sig: &Signature) -> Result<(), SyntaxError> {
    if let Some(token) = &sig.constness {
        return Err(shorthand_error(
            "a function shorthand is not `const`",
            token.span,
        ));
    }
    if let Some(token) = &sig.asyncness {
        return Err(shorthand_error(
            "a function shorthand is not `async`",
            token.span,
        ));
    }
    if let Some(token) = &sig.unsafety {
        return Err(shorthand_error(
            "a function shorthand is not `unsafe`",
            token.span,
        ));
    }
    if let Some(abi) = &sig.abi {
        return Err(shorthand_error(
            "a function shorthand has no ABI",
            abi.span(),
        ));
    }
    if let Some(variadic) = &sig.variadic {
        return Err(shorthand_error(
            "a function shorthand is not variadic",
            variadic.span(),
        ));
    }
    if !sig.generics.params.is_empty() || sig.generics.where_clause.is_some() {
        return Err(shorthand_error(
            "a function shorthand is not generic: a parametric function names its instance in each equation, so declare it as a struct",
            sig.generics.span(),
        ));
    }
    let name = sig.ident.unraw().to_string();
    let camel = name
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_uppercase())
        && name
            .chars()
            .all(|character| character.is_ascii_alphanumeric());
    if !camel {
        return Err(shorthand_error(
            &format!(
                "a function symbol is named as its applications are written, in UpperCamelCase (`fn {}`); its equation takes the snake_case name",
                upper_camel(&name)
            ),
            sig.ident.span(),
        ));
    }
    Ok(())
}

fn upper_camel(name: &str) -> String {
    name.split('_')
        .filter(|segment| !segment.is_empty())
        .map(|segment| {
            let mut characters = segment.chars();
            characters
                .next()
                .map(|first| first.to_uppercase().chain(characters).collect::<String>())
                .unwrap_or_default()
        })
        .collect()
}

fn parameter(input: &FnArg) -> Result<(Ident, Box<syn::Type>), SyntaxError> {
    let FnArg::Typed(typed) = input else {
        return Err(shorthand_error(
            "a function has no `self` receiver",
            input.span(),
        ));
    };
    if let Some(attribute) = typed.attrs.first() {
        return Err(shorthand_error(
            "a function parameter takes no attributes",
            attribute.span(),
        ));
    }
    let Pat::Ident(pattern) = &*typed.pat else {
        return Err(shorthand_error(
            "a function parameter is a plain name; write cases as a `match` on the parameter in the body, or as rows of `k::equations!`",
            typed.pat.span(),
        ));
    };
    if pattern.by_ref.is_some() || pattern.mutability.is_some() || pattern.subpat.is_some() {
        return Err(shorthand_error(
            "a function parameter is a plain name, without `ref`, `mut`, or `@`",
            typed.pat.span(),
        ));
    }
    let term_sort = parse_typed_term_sort((*typed.ty).clone())?;
    if term_sort.is_predicate() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            typed.ty.span(),
        ));
    }
    Ok((pattern.ident.clone(), typed.ty.clone()))
}

fn shorthand_error(reason: &str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidFunctionShorthand {
            reason: reason.to_owned(),
        },
        span,
    )
}

/// Why a helper or a sentence marker other than `#[k::requires]` means nothing on a function
/// shorthand, whose body states its function's equations (one, or one per branch).
fn shorthand_helper_reason(entry: AttributeMacro) -> String {
    let name = entry.name();
    match entry {
        AttributeMacro::Ensures | AttributeMacro::Exists => format!(
            "`#[k::{name}]` states what a step's result satisfies; a function shorthand's body states the function's equations, which reach no result state"
        ),
        AttributeMacro::Fresh => format!(
            "`#[k::{name}]` draws a value in a transition step; a function shorthand's body states the function's equations, which take no step"
        ),
        AttributeMacro::Priority => format!(
            "`#[k::{name}]` is retired, and a function shorthand orders the equations its body states itself, a branching body's catch-all after its other branches, so no order is written on it"
        ),
        _ => format!(
            "`#[k::{name}]` does not apply to a function declared by a `fn`: its body states the function's equations, under the function's own declaration"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::KrsSyntax as _;

    /// The start of every comma of `tokens`.
    fn comma_starts(tokens: &TokenStream) -> Vec<proc_macro2::LineColumn> {
        tokens
            .clone()
            .into_iter()
            .filter(|token| matches!(token, TokenTree::Punct(punct) if punct.as_char() == ','))
            .map(|token| token.span().start())
            .collect()
    }

    /// Without a label the payload is returned as written; with one, its other entries keep the
    /// commas written after them, and a label that is no literal is the label's own mistake.
    #[test]
    fn take_label_keeps_the_payload_as_written() {
        let parse = |source: &str| crate::parse::tokens_from_source(source).unwrap();
        let payload = parse("total, sort = Int, syntax = \"f({x})\"");
        let (kept, label) = take_label(payload.clone()).unwrap();
        assert!(label.is_none());
        assert_eq!(kept.to_string(), payload.to_string());
        assert_eq!(comma_starts(&kept), comma_starts(&payload));

        let payload = parse("total, label = \"named\", sort = Int");
        let (kept, label) = take_label(payload.clone()).unwrap();
        assert_eq!(label.unwrap().value(), "named");
        assert_eq!(kept.to_string(), "total , sort = Int");
        assert_eq!(comma_starts(&kept), comma_starts(&payload)[..1]);

        let (kept, _) = take_label(parse("total, label = \"named\"")).unwrap();
        assert_eq!(kept.to_string(), "total");

        let error = take_label(parse("total, label = path::x")).unwrap_err();
        assert_eq!(
            error.kind().code().as_str(),
            "krs::syntax::invalid-argument-value",
            "{error}"
        );
    }

    #[test]
    fn equation_names_split_words_and_keep_digits() {
        for (function, equation) in [
            ("Byte", "byte"),
            ("FieldX", "field_x"),
            ("R8", "r8"),
            ("Rp2", "rp2"),
            ("PairValue", "pair_value"),
            ("HLValue", "hl_value"),
            ("X", "x"),
        ] {
            assert_eq!(equation_name(function), equation, "{function}");
        }
    }

    fn lower(attribute: &str, item: &str) -> Result<FunctionShorthand, SyntaxError> {
        FunctionShorthand::lower(
            attribute.parse().expect("attribute tokens"),
            syn::parse_str(item).expect("a shorthand item"),
        )
    }

    #[test]
    fn a_typed_signature_keeps_its_element_types_and_its_equations_name_the_sort() {
        let shorthand = lower(
            "total, internal",
            "pub fn Mark(accessed: k::Term<Set<Int>>, n: k::Term<Int>) -> k::Term<Set<Int>> { set::union(accessed, set::item(n)) }",
        )
        .expect("valid shorthand");
        let production = shorthand.attribute().production();
        assert_eq!(crate::path::path_text(&production.sort), "Set");
        assert_eq!(production.sort_arguments.len(), 1);
        assert_eq!(
            shorthand.sort_type().to_token_stream().to_string(),
            "Set < Int >"
        );
        assert_eq!(
            production
                .sort_argument_provenance()
                .unwrap()
                .iter()
                .map(|anchor| (anchor.role(), anchor.ordinal()))
                .collect::<Vec<_>>(),
            [(crate::ProvenanceRole::ConstructorSortArgument, 0)]
        );
        // The struct's field keeps its type; the equation states the sort.
        assert_eq!(
            shorthand
                .structure()
                .fields
                .iter()
                .next()
                .map(|field| field.ty.to_token_stream().to_string()),
            Some("k :: Term < Set < Int > >".to_owned())
        );
        let [equation] = shorthand.equations() else {
            panic!("a body defines one equation");
        };
        assert_eq!(
            equation.item().sig.output.to_token_stream().to_string(),
            "-> k :: Term < Set >"
        );
    }

    #[test]
    fn the_long_form_states_a_typed_result_in_its_sort() {
        let attribute = FunctionAttribute::parse_tokens(
            "total, sort = Map<Int, Set<Int>>, syntax = \"m({x})\""
                .parse()
                .unwrap(),
        )
        .expect("a typed result sort");
        let production = attribute.production();
        assert_eq!(crate::path::path_text(&production.sort), "Map");
        assert_eq!(
            crate::SortArgument::preorder(&production.sort_arguments).len(),
            3
        );
        let error = FunctionAttribute::parse_tokens(
            "total, sort = Map<Int, &Int>, syntax = \"m({x})\""
                .parse()
                .unwrap(),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::InvalidCollectionArgument
        ));
    }

    #[test]
    fn a_body_declares_the_struct_and_one_equation() {
        let shorthand = lower(
            "total, internal",
            "/// Low byte.\n#[k::requires(int::ge(value, 0))]\npub fn Byte(value: k::Term<Int>) -> k::Term<Int> { int::rem_euclid(value, 256) }",
        )
        .expect("valid shorthand");
        assert_eq!(shorthand.structure().ident, "Byte");
        assert_eq!(
            shorthand
                .attribute()
                .production()
                .syntax
                .as_ref()
                .map(syn::LitStr::value)
                .as_deref(),
            Some("byte({value})")
        );
        assert!(!shorthand.attribute().has_authored_syntax());
        let [equation] = shorthand.equations() else {
            panic!("a body defines one equation");
        };
        assert_eq!(equation.item().sig.ident, "byte");
        assert_eq!(equation.item().attrs.len(), 1);
        assert!(equation.equation_keys().is_empty());
        assert_eq!(shorthand.structure().attrs.len(), 1);
    }

    #[test]
    fn a_declaration_without_body_has_no_equation() {
        let shorthand = lower(
            "total, syntax = \"#r({index})\"",
            "pub fn R8(index: k::Term<Int>) -> k::Term<Operand>;",
        )
        .expect("valid declaration");
        assert!(shorthand.equations().is_empty());
        assert!(shorthand.attribute().has_authored_syntax());
    }

    #[test]
    fn shorthand_shapes_outside_the_definitional_form_are_rejected() {
        for (attribute, item, expected) in [
            (
                "total, internal",
                "fn byte(value: k::Term<Int>) -> k::Term<Int> { value }",
                "UpperCamelCase (`fn Byte`)",
            ),
            (
                "total, internal, sort = Int",
                "fn Byte(value: k::Term<Int>) -> k::Term<Int> { value }",
                "remove `sort`",
            ),
            (
                "total, internal",
                "fn Byte((a, b): k::Term<Int>) -> k::Term<Int> { a }",
                "plain name",
            ),
            (
                "total, internal",
                "fn Pick<S: ?Sized>(value: k::Term<S>) -> k::Term<S> { value }",
                "not generic",
            ),
            (
                "total, internal",
                "#[k::equation(owise)] fn Byte(value: k::Term<Int>) -> k::Term<Int> { value }",
                "`#[k::equation]`",
            ),
            (
                "total, internal, hook = int::rem",
                "fn Byte(value: k::Term<Int>) -> k::Term<Int> { value }",
                "no body",
            ),
            (
                "total, internal",
                "#[k::requires(true)] fn Byte(value: k::Term<Int>) -> k::Term<Int>;",
                "has none",
            ),
        ] {
            let error = lower(attribute, item).expect_err(item);
            assert!(error.to_string().contains(expected), "{item}: {error}");
        }
    }

    #[test]
    fn a_program_syntax_function_needs_its_syntax() {
        let error = lower(
            "total",
            "pub fn Byte(value: k::Term<Int>) -> k::Term<Int> { value }",
        )
        .expect_err("pub and not internal");
        assert_eq!(error.kind(), &SyntaxErrorKind::MissingFunctionSyntax);
        lower(
            "total",
            "fn Byte(value: k::Term<Int>) -> k::Term<Int> { value }",
        )
        .expect("a private function is not program syntax");
        lower(
            "total",
            "pub(crate) fn Byte(value: k::Term<Int>) -> k::Term<Int> { value }",
        )
        .expect("a crate-visible function is not program syntax");
    }
}
