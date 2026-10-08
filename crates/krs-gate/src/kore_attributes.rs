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

/// The named string attributes of the named labels' symbol declarations.
///
/// Labels are K label names (`while`, not the KORE symbol name); attributes a
/// declaration lacks are omitted from its object. Java K writes each
/// declaration on one line and k-rust across several, so the definition is
/// parsed rather than compared as text.
///
/// # Errors
///
/// Fails for unreadable or invalid KORE, a label without a symbol declaration
/// or with several, and a named attribute that is not one UTF-8 string.
pub(crate) fn symbol_attributes(
    kore: &std::path::Path,
    labels: &[String],
    names: &[String],
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    use k_rust::kast::identifier::encode_label;
    use k_rust::kore::{ast::Sentence, parser::parse_definition};

    let definition = parse_definition(&std::fs::read_to_string(kore)?)?;
    let mut rows = serde_json::Map::new();
    for label in labels {
        let symbol = encode_label(label);
        let mut declarations = definition
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    symbol: declared,
                    attributes,
                    ..
                } if declared.name == symbol => Some(attributes),
                _ => None,
            });
        let attributes = declarations
            .next()
            .ok_or_else(|| format!("KORE declares no symbol for label `{label}`"))?;
        if declarations.next().is_some() {
            return Err(format!("KORE declares label `{label}` more than once").into());
        }
        let mut row = serde_json::Map::new();
        for name in names {
            let value = string_attribute(attributes, name).map_err(|error| {
                let reason = match error {
                    StringAttributeError::NonUtf8 => "is not UTF-8",
                    StringAttributeError::NotOneString => "is not one string",
                    StringAttributeError::Duplicate => "is repeated",
                };
                format!("attribute `{name}` of label `{label}` {reason}")
            })?;
            if let Some(value) = value {
                row.insert(name.clone(), serde_json::Value::String(value.to_owned()));
            }
        }
        rows.insert(label.clone(), serde_json::Value::Object(row));
    }
    Ok(serde_json::Value::Object(rows))
}

#[cfg(test)]
mod tests {
    use super::symbol_attributes;

    #[test]
    fn reads_named_string_attributes_by_k_label() {
        let directory =
            std::env::temp_dir().join(format!("krs-gate-kore-attributes-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("definition.kore");
        std::fs::write(
            &path,
            "[]\nmodule M\n  sort SortStmt{} []\n  symbol Lblwhile{}(SortStmt{}) : SortStmt{} \
             [format{}(\"%cwhile%r %1\"), colors{}(\"red\"), functional{}()]\n  \
             symbol Lblskip{}() : SortStmt{}\n    [format{}(\"%cskip%r\")]\nendmodule []\n",
        )
        .unwrap();
        let strings = |values: &[&str]| {
            values
                .iter()
                .map(|value| (*value).to_owned())
                .collect::<Vec<_>>()
        };
        let rows = symbol_attributes(
            &path,
            &strings(&["while", "skip"]),
            &strings(&["format", "colors", "color"]),
        )
        .unwrap();
        assert_eq!(
            rows,
            serde_json::json!({
                "while": {"format": "%cwhile%r %1", "colors": "red"},
                "skip": {"format": "%cskip%r"},
            })
        );
        let missing = symbol_attributes(&path, &strings(&["absent"]), &strings(&["format"]));
        assert_eq!(
            missing.unwrap_err().to_string(),
            "KORE declares no symbol for label `absent`"
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}
