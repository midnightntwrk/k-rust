//! Strict string-attribute extraction shared by definition and proof checks.

use k_rust::kore::ast::{Attributes, Pattern};

/// The structural error in a named string attribute.
pub(crate) enum StringAttributeError {
    NonUtf8,
    NotOneString,
    Duplicate,
}

/// Return the unique string value of a named attribute when it exists.
pub(crate) fn string_attribute<'a>(
    attributes: &'a Attributes,
    name: &str,
) -> Result<Option<&'a str>, StringAttributeError> {
    let mut matches = attributes.0.iter().filter_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == name => Some(arguments),
        _ => None,
    });
    let Some(arguments) = matches.next() else {
        return Ok(None);
    };
    if matches.next().is_some() {
        return Err(StringAttributeError::Duplicate);
    }
    let [Pattern::String(value)] = arguments.as_slice() else {
        return Err(StringAttributeError::NotOneString);
    };
    value
        .as_utf8()
        .map(Some)
        .map_err(|_| StringAttributeError::NonUtf8)
}
