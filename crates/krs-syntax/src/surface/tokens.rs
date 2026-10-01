//! Invocation recognition in raw token trees.

use proc_macro2::{Delimiter, Group, Spacing, Span, TokenStream, TokenTree};
use syn::ext::IdentExt;
use syn::{Path, PathSegment};

use super::{Entry, Resolve};

/// Whether a tree is the specified punctuation character.
#[must_use]
pub fn is_punct(tree: Option<&TokenTree>, character: char) -> bool {
    matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == character)
}

/// Whether a tree is a colon joined to the following tree.
#[must_use]
pub fn is_joint_colon(tree: Option<&TokenTree>) -> bool {
    matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == ':' && punct.spacing() == Spacing::Joint)
}

/// Whether two trees at `index` form a path separator.
#[must_use]
pub fn is_path_separator(trees: &[TokenTree], index: usize) -> bool {
    is_joint_colon(trees.get(index)) && is_punct(trees.get(index + 1), ':')
}

/// Recognizes a path and returns the number of trees it occupies.
/// A path must not start immediately after a path separator.
#[must_use]
pub fn path_at(trees: &[TokenTree], index: usize) -> Option<(Path, usize)> {
    if index >= 2 && is_path_separator(trees, index - 2) {
        return None;
    }
    // The second colon of a separator must not become a leading separator.
    if index > 0 && is_joint_colon(trees.get(index - 1)) && is_punct(trees.get(index), ':') {
        return None;
    }
    let leading = is_path_separator(trees, index);
    if leading && index > 0 && matches!(trees.get(index - 1), Some(TokenTree::Ident(_))) {
        return None;
    }
    let mut cursor = index + if leading { 2 } else { 0 };
    let mut path = Path {
        leading_colon: leading.then(|| syn::Token![::](trees[index].span())),
        segments: syn::punctuated::Punctuated::new(),
    };
    loop {
        let Some(TokenTree::Ident(ident)) = trees.get(cursor) else {
            return None;
        };
        path.segments.push(PathSegment::from(ident.clone()));
        cursor += 1;
        if is_path_separator(trees, cursor) {
            cursor += 2;
        } else {
            return Some((path, cursor - index));
        }
    }
}

/// A function-like macro call recognized without resolving its path.
#[derive(Clone, Debug)]
pub struct MacroCall {
    /// The invoked path, with raw identifiers and a leading separator preserved.
    pub path: Path,
    /// Number of trees from the path through the body group.
    pub len: usize,
    /// The delimited macro body.
    pub group: Group,
}

/// Recognizes a path followed by `!` and a delimited group.
/// A single-segment keyword path must not be recognized as a macro call.
#[must_use]
pub fn macro_call(trees: &[TokenTree], index: usize) -> Option<MacroCall> {
    let (path, len) = path_at(trees, index)?;
    if path.segments.len() == 1
        && crate::keyword::is_keyword(&path.segments[0].ident.unraw().to_string())
    {
        return None;
    }
    if !is_punct(trees.get(index + len), '!') {
        return None;
    }
    let Some(TokenTree::Group(group)) = trees.get(index + len + 1) else {
        return None;
    };
    if group.delimiter() == Delimiter::None {
        return None;
    }
    Some(MacroCall {
        path,
        len: len + 2,
        group: group.clone(),
    })
}

/// An outer or inner attribute recognized without resolving its path.
#[derive(Clone, Debug)]
pub struct AttributeCall {
    /// The bracket group containing the attribute path and arguments.
    pub group: Group,
    /// Number of trees from `#` through the bracket group.
    pub len: usize,
}

/// Recognizes `#[…]` or `#![…]` at `index`.
#[must_use]
pub fn attribute_call(trees: &[TokenTree], index: usize) -> Option<AttributeCall> {
    if !is_punct(trees.get(index), '#') {
        return None;
    }
    let inner = is_punct(trees.get(index + 1), '!');
    let group_index = index + 1 + usize::from(inner);
    let Some(TokenTree::Group(group)) = trees.get(group_index) else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket {
        return None;
    }
    Some(AttributeCall {
        group: group.clone(),
        len: group_index + 1 - index,
    })
}

/// The token-tree form of a resolved invocation.
#[derive(Clone, Debug)]
pub enum TokenCallKind {
    /// A function-like call's body group.
    Function(Group),
    /// An attribute's bracket group and consumed length.
    Attribute(AttributeCall),
}

/// A resolved invocation and its position in a token stream.
#[derive(Clone, Debug)]
pub struct TokenCall {
    /// Group indices followed by the index of the invocation's first tree.
    pub at: Vec<usize>,
    /// Number of trees occupied in the containing stream.
    pub len: usize,
    /// The resolved KRS entry point.
    pub entry: Entry,
    /// Span of the invocation's first tree.
    pub span: Span,
    /// The invocation's raw token-tree form.
    pub kind: TokenCallKind,
    /// Whether an unresolved macro's body encloses this call within the scanned stream.
    pub in_non_krs_macro: bool,
}

/// Finds resolved KRS calls recursively in raw token trees.
/// The bodies of resolved calls must not be traversed.
#[must_use]
pub fn token_calls(tokens: &TokenStream, resolve: &dyn Resolve) -> Vec<TokenCall> {
    fn scan(
        tokens: &TokenStream,
        resolve: &dyn Resolve,
        position: &mut Vec<usize>,
        calls: &mut Vec<TokenCall>,
        in_non_krs_macro: bool,
    ) {
        let trees: Vec<_> = tokens.clone().into_iter().collect();
        let mut index = 0;
        while index < trees.len() {
            let call = macro_call(&trees, index)
                .and_then(|call| match resolve.resolve(&call.path)? {
                    entry @ Entry::Function(_) => {
                        Some((entry, call.len, TokenCallKind::Function(call.group)))
                    }
                    Entry::Attribute(_) => None,
                })
                .or_else(|| {
                    let call = attribute_call(&trees, index)?;
                    let inner: Vec<_> = call.group.stream().into_iter().collect();
                    let (path, _) = path_at(&inner, 0)?;
                    match resolve.resolve(&path)? {
                        entry @ Entry::Attribute(_) => {
                            Some((entry, call.len, TokenCallKind::Attribute(call)))
                        }
                        Entry::Function(_) => None,
                    }
                });
            position.push(index);
            if let Some((entry, len, kind)) = call {
                calls.push(TokenCall {
                    at: position.clone(),
                    len,
                    entry,
                    span: trees[index].span(),
                    kind,
                    in_non_krs_macro,
                });
                index += len;
            } else if let Some(call) = macro_call(&trees, index) {
                position.pop();
                position.push(index + call.len - 1);
                scan(&call.group.stream(), resolve, position, calls, true);
                index += call.len;
            } else {
                if let TokenTree::Group(group) = &trees[index] {
                    scan(&group.stream(), resolve, position, calls, in_non_krs_macro);
                }
                index += 1;
            }
            position.pop();
        }
    }
    let mut calls = Vec::new();
    scan(tokens, resolve, &mut Vec::new(), &mut calls, false);
    calls
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::{AttributeMacro, AuthoredResolver, FunctionMacro, path_text};

    fn trees(source: &str) -> Vec<TokenTree> {
        source.parse::<TokenStream>().unwrap().into_iter().collect()
    }

    #[test]
    fn path_starts_and_spelling() {
        let prefixed = trees("other::k::id!(x)");
        assert!(path_at(&prefixed, 3).is_none());
        let ascribed = trees("x: k::id!(x)");
        assert_eq!(path_text(&macro_call(&ascribed, 2).unwrap().path), "k::id");
        let leading = trees("::r#k::r#id!(x)");
        let call = macro_call(&leading, 0).unwrap();
        assert_eq!(path_text(&call.path), "::r#k::r#id");
        assert_eq!(call.len, 8);
        assert!(path_at(&leading, 1).is_none());
        assert!(path_at(&leading, 2).is_none());
    }

    #[test]
    fn keyword_paths_are_not_calls() {
        for source in [
            "if !(x)",
            "return !(x)",
            "match !{x}",
            "r#type !(x)",
            "::if !(x)",
        ] {
            assert!(macro_call(&trees(source), 0).is_none(), "{source}");
        }
        assert!(macro_call(&trees("r#custom !(x)"), 0).is_some());
    }

    #[test]
    fn attribute_forms() {
        assert_eq!(attribute_call(&trees("#[k::sort]"), 0).unwrap().len, 2);
        assert_eq!(attribute_call(&trees("#![k::sort]"), 0).unwrap().len, 3);
        assert!(attribute_call(&trees("#(k::sort)"), 0).is_none());
    }

    #[test]
    fn call_positions_and_consumed_bodies() {
        let tokens =
            "outer! { x: k::id!(k::rules! {}); [#[k::sort(k::id!(x))] #![k::sort] ] } k::rules! {}"
                .parse::<TokenStream>()
                .unwrap();
        let calls = token_calls(&tokens, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 4);
        assert_eq!(calls[0].at, [2, 2]);
        assert_eq!(calls[0].len, 6);
        assert_eq!(calls[0].entry, Entry::Function(FunctionMacro::Id));
        assert_eq!(calls[0].span.byte_range(), 12..13);
        assert_eq!(calls[1].at, [2, 9, 0]);
        assert_eq!(calls[1].entry, Entry::Attribute(AttributeMacro::Sort));
        assert_eq!(calls[2].at, [2, 9, 2]);
        assert_eq!(calls[2].len, 3);
        assert_eq!(calls[3].at, [3]);
        assert_eq!(calls[3].entry, Entry::Function(FunctionMacro::Rules));
        assert!(matches!(calls[0].kind, TokenCallKind::Function(_)));
        assert!(matches!(calls[1].kind, TokenCallKind::Attribute(_)));
    }

    #[test]
    fn only_complete_resolved_paths_are_reported() {
        let tokens = "other::k::id!(x); x: r#k::r#id!(x); if !(k::id!(y))"
            .parse::<TokenStream>()
            .unwrap();
        let calls = token_calls(&tokens, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0].entry, Entry::Function(FunctionMacro::Id));
        assert_eq!(calls[1].entry, Entry::Function(FunctionMacro::Id));
        assert_eq!(calls[0].at.len(), 1);
        assert_eq!(calls[1].at.len(), 2);
    }
}
