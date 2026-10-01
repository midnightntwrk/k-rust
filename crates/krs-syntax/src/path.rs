use syn::Path;

pub(crate) fn is_plain_path(path: &Path) -> bool {
    !path.segments.is_empty()
        && path
            .segments
            .iter()
            .all(|segment| matches!(segment.arguments, syn::PathArguments::None))
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
}
