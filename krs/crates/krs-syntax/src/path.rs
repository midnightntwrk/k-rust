use syn::Path;
use syn::spanned::Spanned;

use crate::{SyntaxError, SyntaxErrorKind};

pub(crate) fn is_plain_path(path: &Path) -> bool {
    !path.segments.is_empty()
        && path
            .segments
            .iter()
            .all(|segment| matches!(segment.arguments, syn::PathArguments::None))
}

pub(crate) fn plain_path_last(path: &Path) -> Option<&syn::PathSegment> {
    is_plain_path(path).then(|| path.segments.last()).flatten()
}

pub(crate) fn unqualified_path_ident(path: &Path) -> Option<&syn::Ident> {
    if path.leading_colon.is_some() {
        return None;
    }
    let mut segments = path.segments.iter();
    let segment = segments.next()?;
    if segments.next().is_some() || !matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }
    Some(&segment.ident)
}

/// K's builtin collection sorts that the facade spells with type parameters
/// (`List<T>`, `Map<K, V>`, `Set<T>`) to carry Rust authoring information.
/// In K each is one unparameterized sort.
const PARAMETRIC_COLLECTION_MARKERS: &[&str] = &["List", "Map", "Set"];

/// The collection sort that `path` names with generic arguments: its last
/// segment is a builtin collection marker with angle-bracketed arguments and
/// every other segment is plain, as in `k::builtin::List<Instruction>`.
pub(crate) fn parametric_collection(path: &Path) -> Option<&'static str> {
    let last = path.segments.last()?;
    if !matches!(last.arguments, syn::PathArguments::AngleBracketed(_))
        || path
            .segments
            .iter()
            .rev()
            .skip(1)
            .any(|segment| !matches!(segment.arguments, syn::PathArguments::None))
    {
        return None;
    }
    PARAMETRIC_COLLECTION_MARKERS
        .iter()
        .find(|marker| last.ident == marker)
        .copied()
}

/// The error for a path that gives a builtin collection sort generic
/// arguments where only a sort makes sense: a rule narrowing when
/// `narrowing`, otherwise a field or term sort.
pub(crate) fn parametric_collection_error(path: &Path, narrowing: bool) -> Option<SyntaxError> {
    let collection = parametric_collection(path)?;
    Some(SyntaxError::new(
        SyntaxErrorKind::ParametricCollectionSort {
            collection,
            bare: path_text(path),
            narrowing,
        },
        path.span(),
    ))
}

pub(crate) fn without_last_arguments(path: &Path) -> Path {
    let mut path = path.clone();
    if let Some(last) = path.segments.last_mut() {
        last.arguments = syn::PathArguments::None;
    }
    path
}

/// The text of `path`: its segment identifiers joined by `::`, with a
/// leading `::` when one was authored, such as `::k::symbol`.
///
/// Raw identifiers keep their `r#` prefix and generic arguments are
/// omitted. Diagnostics and path comparisons use this text; a descriptor's
/// `authored_path` instead carries the token-stream text `a :: b`.
#[must_use]
pub fn path_text(path: &Path) -> String {
    let mut text = String::new();
    if path.leading_colon.is_some() {
        text.push_str("::");
    }
    for (index, segment) in path.segments.iter().enumerate() {
        if index > 0 {
            text.push_str("::");
        }
        text.push_str(&segment.ident.to_string());
    }
    text
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(source: &str) -> Path {
        syn::parse_str(source).expect("a path")
    }

    #[test]
    fn path_text_joins_identifiers_and_keeps_a_leading_colon() {
        assert_eq!(path_text(&path("a :: b")), "a::b");
        assert_eq!(path_text(&path(":: k :: symbol")), "::k::symbol");
        assert_eq!(path_text(&path("r#k::r#type")), "r#k::r#type");
        assert_eq!(path_text(&path("Vec::<u8>::new")), "Vec::new");
    }

    #[test]
    fn parametric_collection_names_a_collection_marker_with_arguments_last() {
        assert_eq!(parametric_collection(&path("List<BusCycle>")), Some("List"));
        assert_eq!(
            parametric_collection(&path("k::builtin::Map<Reg8, Int>")),
            Some("Map")
        );
        assert_eq!(
            parametric_collection(&path("::k::builtin::Set::<Int>")),
            Some("Set")
        );
        for other in [
            "List",
            "k::builtin::Map",
            "Vec<Int>",
            "List<Int>::Item",
            "k<X>::List<Int>",
        ] {
            assert_eq!(parametric_collection(&path(other)), None, "{other}");
        }
        let error = parametric_collection_error(&path("k::builtin::List<Int>"), true).unwrap();
        assert_eq!(
            error.to_string(),
            "K's `List` sort is not parametric, so a `where` narrowing tests the sort `List` and \
             cannot constrain its elements; write `k::builtin::List` without generic arguments"
        );
    }
}
