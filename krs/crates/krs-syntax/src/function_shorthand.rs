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
//! declares the symbol only. Both the macro and the collector lower the
//! authored item here, so the struct and the equation carry the same authored
//! spans on both sides and their provenance agrees byte for byte.

use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};
use quote::{ToTokens, quote};
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Attribute, Block, FnArg, Ident, ItemFn, ItemStruct, Pat, ReturnType, Signature, Token};

use crate::surface::{AttributeMacro, helper_entry};
use crate::term_sort::parse_term_sort;
use crate::{ConstructorDeclaration, FunctionAttribute, SyntaxError, SyntaxErrorKind};

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
}

impl Parse for ShorthandItem {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        let sig: Signature = input.parse()?;
        let body = if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
            None
        } else {
            Some(input.parse()?)
        };
        Ok(Self {
            attrs,
            vis,
            sig,
            body,
        })
    }
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

/// The struct and optional equation a function shorthand stands for.
#[derive(Clone, Debug)]
pub struct FunctionShorthand {
    attribute: FunctionAttribute,
    structure: ItemStruct,
    equation: Option<ItemFn>,
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
        } = item;
        validate_signature(&sig)?;
        let ReturnType::Type(_, result_type) = &sig.output else {
            return Err(shorthand_error(
                "a function declared by a `fn` returns its sort, `-> k::Term<Sort>`",
                sig.ident.span(),
            ));
        };
        let result_sort = parse_term_sort((**result_type).clone())?;
        if result_sort.is_dynamic() || result_sort.is_predicate() {
            return Err(shorthand_error(
                "a function declared by a `fn` returns `k::Term<Sort>` with a sort alias or builtin sort, such as `k::Term<Exp>` or `k::Term<Int>`",
                result_type.span(),
            ));
        }
        let mut attribute =
            FunctionAttribute::parse_shorthand_tokens(attribute, result_sort.sort())?;
        if let Some(hook) = attribute.hook()
            && body.is_some()
        {
            return Err(shorthand_error(
                "a hooked function takes its values from the backend, so it has no body; end the declaration with `;`",
                hook.range()?.first(),
            ));
        }

        let mut struct_attrs = Vec::new();
        let mut equation_attrs = Vec::new();
        for attribute in attrs {
            match helper_entry(attribute.path()) {
                Some(AttributeMacro::Requires) => {
                    if body.is_none() {
                        return Err(shorthand_error(
                            "`#[k::requires]` guards the equation a body defines; a declaration ending with `;` has none",
                            attribute.span(),
                        ));
                    }
                    equation_attrs.push(attribute);
                }
                Some(entry) => {
                    return Err(shorthand_error(
                        &format!(
                            "`#[k::{}]` does not apply to a function declared by a `fn`; write the struct and `#[k::equation]` fns instead",
                            entry.name()
                        ),
                        attribute.span(),
                    ));
                }
                None if attribute.path().is_ident("cfg") => {
                    equation_attrs.push(attribute.clone());
                    struct_attrs.push(attribute);
                }
                None => struct_attrs.push(attribute),
            }
        }

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

        let equation = body
            .map(|body| {
                let equation_name = equation_ident(name)?;
                // The subject `Byte(value)`: the head is the authored name,
                // and its parentheses carry the parameter list's span.
                let mut group = Group::new(Delimiter::Parenthesis, quote!(#(#arguments),*));
                group.set_span(sig.paren_token.span.join());
                let subject = TokenStream::from_iter([
                    TokenTree::Ident(name.clone()),
                    TokenTree::Group(group),
                ]);
                syn::parse2::<ItemFn>(quote! {
                    #(#equation_attrs)*
                    fn #equation_name(#subject: #result_type) -> #result_type #body
                })
                .map_err(SyntaxError::from)
            })
            .transpose()?;
        Ok(Self {
            attribute,
            structure,
            equation,
        })
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

    /// The equation fn a body defines, named [`equation_name`] of the
    /// function; absent for a declaration that ends with `;`.
    #[must_use]
    pub const fn equation(&self) -> Option<&ItemFn> {
        self.equation.as_ref()
    }
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
            "a function parameter is a plain name: one equation over variables defines the function; write cases as rows of `k::equations!`",
            typed.pat.span(),
        ));
    };
    if pattern.by_ref.is_some() || pattern.mutability.is_some() || pattern.subpat.is_some() {
        return Err(shorthand_error(
            "a function parameter is a plain name, without `ref`, `mut`, or `@`",
            typed.pat.span(),
        ));
    }
    let term_sort = parse_term_sort((*typed.ty).clone())?;
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

#[cfg(test)]
mod tests {
    use super::*;

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
        let equation = shorthand.equation().expect("a body defines an equation");
        assert_eq!(equation.sig.ident, "byte");
        assert_eq!(equation.attrs.len(), 1);
        assert_eq!(shorthand.structure().attrs.len(), 1);
    }

    #[test]
    fn a_declaration_without_body_has_no_equation() {
        let shorthand = lower(
            "total, syntax = \"#r({index})\"",
            "pub fn R8(index: k::Term<Int>) -> k::Term<Operand>;",
        )
        .expect("valid declaration");
        assert!(shorthand.equation().is_none());
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
