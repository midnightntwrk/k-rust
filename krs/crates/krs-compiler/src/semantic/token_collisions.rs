//! Token regexes that collide with K's own tokens.
//!
//! K's scanner keys a regex token by its text, so a user regex spelled like
//! one of K's own token regexes must carry K's `prec`: otherwise Java K
//! reports "Inconsistent token precedence detected." and k-rust fails to load
//! with `InconsistentTokenPrecedence`.
//!
//! K also lexes the emitted configuration declaration, where `<k>` is `<`, a
//! cell name, and `>`, and a cell property is a name, `=`, and a string. The
//! scanner takes the longest match and, among equally long matches, the
//! highest `prec`, a tie included. A user regex that matches a whole cell name
//! or property name at a `prec` at least as high as every K token that matches
//! it takes the lexeme from K, and Java K cannot parse the configuration.
//!
//! upstream k/token-regex-collisions (reviewed, not a request): K and k-rust
//! agree, and KRS checks the collision up front.

use krs_ir::{CellAttribute, FixedCell, FixedCellContent, GrammarProductionItemKind};
use krs_ir::{ConfigurationRoot, ProductionAttribute};
use krs_ir_levels::{SemanticModule, SemanticProduction};

use super::error::DescriptorLoweringError;
use crate::partition::is_private;

/// K 7.1.337's own regex tokens (`kast.md`), as K reads the regex text, with
/// their sort and `prec`. `#CellName` lexes configuration cell names.
const K_TOKENS: [(&str, &str, u32); 8] = [
    ("#LowerId", r"[a-z][a-zA-Z0-9]*", 2),
    ("#UpperId", r"[A-Z][a-zA-Z0-9]*", 2),
    (
        "KString",
        r#"[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]"#,
        0,
    ),
    ("KLabel", r"`(\\`|\\\\|[^`\\\n\r])+`", 0),
    ("KLabel", r"[#a-z][a-zA-Z0-9]*", 1),
    (
        "#KVariable",
        r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)",
        1,
    ),
    ("KConfigVar", r"(\$)([A-Z][A-Za-z0-9'_]*)", 0),
    ("#CellName", r"[a-zA-Z][a-zA-Z0-9\-]*", 1),
];

/// One user regex token: its production, regex text, and `prec`.
struct RegexToken<'a> {
    production: &'a SemanticProduction,
    regex: &'a str,
    precedence: u32,
}

/// Rejects, in stable module and production order, a token regex that is one
/// of K's own at another `prec`, then one that takes a configuration name
/// from K.
pub(super) fn check_token_collisions(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    for token in modules
        .iter()
        .flat_map(SemanticModule::productions)
        .filter_map(regex_token)
    {
        if let Some((sort, _, precedence)) =
            K_TOKENS.iter().find(|(_, regex, _)| *regex == token.regex)
            && *precedence != token.precedence
        {
            return Err(fail(
                token.production,
                format!(
                    "the token regex r\"{}\" at `prec({})` is the regex of K's own `{sort}` token, which K declares at `prec({precedence})`; K keys a regex token by its text, so Java K and k-rust both reject the definition. Use a different regex, or `prec = {precedence}`",
                    token.regex, token.precedence
                ),
            ));
        }
    }
    for module in modules.iter().filter(|module| !module.is_spec()) {
        let Some(configuration) = module.configuration() else {
            continue;
        };
        let mut names = Vec::new();
        if let ConfigurationRoot::Named { name, .. } = configuration.root() {
            names.push(ConfigurationName::Cell(name.as_str()));
        }
        for cell in configuration.cells() {
            collect_names(cell, &mut names);
        }
        // The configuration's module sees its own productions and the public
        // ones of every module it imports.
        let visible = modules
            .iter()
            .filter(|other| !other.is_spec())
            .flat_map(|other| {
                let own = other.id() == module.id();
                other
                    .productions()
                    .iter()
                    .filter(move |production| own || !is_private(production))
            })
            .filter_map(regex_token);
        for token in visible {
            check_configuration_names(&token, &names)?;
        }
    }
    Ok(())
}

/// A name K lexes in the emitted configuration declaration.
#[derive(Clone, Copy)]
enum ConfigurationName<'a> {
    /// A cell name, as in `<k>`.
    Cell(&'a str),
    /// A cell property name, as `color` in `<k color="red">`.
    Property { key: &'static str, cell: &'a str },
}

fn collect_names<'a, S, C>(cell: &'a FixedCell<S, C>, names: &mut Vec<ConfigurationName<'a>>) {
    names.push(ConfigurationName::Cell(cell.name()));
    for attribute in cell.attributes() {
        let key = match attribute {
            CellAttribute::Color { .. } => "color",
            CellAttribute::Multiplicity { .. } => "multiplicity",
            CellAttribute::CollectionType { .. } => "type",
            CellAttribute::Stream { .. } => "stream",
            CellAttribute::Exit { .. } => "exit",
            CellAttribute::Initial { .. } => "initial",
        };
        names.push(ConfigurationName::Property {
            key,
            cell: cell.name(),
        });
    }
    if let FixedCellContent::Children { children } = cell.content() {
        for child in children {
            collect_names(child, names);
        }
    }
}

fn check_configuration_names(
    token: &RegexToken<'_>,
    names: &[ConfigurationName<'_>],
) -> Result<(), DescriptorLoweringError> {
    // K's regex dialect is close to Rust's for the regexes that can match a
    // name; a regex Rust cannot read, such as one with a `{Name}` lexical, is
    // not evaluated.
    let Ok(regex) = regex::Regex::new(&format!("^(?:{})$", token.regex)) else {
        return Ok(());
    };
    for name in names {
        let (text, described) = match *name {
            ConfigurationName::Cell(cell) => (
                cell,
                format!("the name of the configuration cell `<{cell}>`"),
            ),
            ConfigurationName::Property { key, cell } => (
                key,
                format!("the `{key}` property of the configuration cell `<{cell}>`"),
            ),
        };
        if !regex.is_match(text) {
            continue;
        }
        let Some((sort, _, precedence)) = strongest_k_token(text) else {
            continue;
        };
        if token.precedence >= precedence {
            return Err(fail(
                token.production,
                format!(
                    "the token regex r\"{}\" at `prec({})` lexes `{text}`, {described}, at least as strongly as K's own `{sort}` token (`prec({precedence})`), so Java K cannot parse the emitted configuration. Lower its `prec` below {precedence}, or change the regex so it does not match `{text}`",
                    token.regex, token.precedence
                ),
            ));
        }
    }
    Ok(())
}

/// The K token with the highest `prec` that matches all of `text`.
fn strongest_k_token(text: &str) -> Option<(&'static str, &'static str, u32)> {
    K_TOKENS
        .iter()
        .filter(|(_, regex, _)| {
            regex::Regex::new(&format!("^(?:{regex})$")).is_ok_and(|regex| regex.is_match(text))
        })
        .copied()
        .reduce(|best, next| if next.2 > best.2 { next } else { best })
}

fn regex_token(production: &SemanticProduction) -> Option<RegexToken<'_>> {
    let precedence = production
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::Token {
                lexical_precedence, ..
            } => Some(lexical_precedence.unwrap_or(0)),
            _ => None,
        })?;
    match production.items() {
        [item] => match item.kind() {
            GrammarProductionItemKind::RegexTerminal {
                precede_regex: None,
                regex,
                follow_regex: None,
            } => Some(RegexToken {
                production,
                regex,
                precedence,
            }),
            _ => None,
        },
        _ => None,
    }
}

fn fail(production: &SemanticProduction, reason: String) -> DescriptorLoweringError {
    let token = production
        .attributes()
        .iter()
        .find(|attribute| matches!(attribute, ProductionAttribute::Token { .. }));
    DescriptorLoweringError::TokenCollision {
        item: Box::new(production.id().clone()),
        reason,
        range: token
            .and_then(|attribute| attribute.origin().origin().exact_authored_range())
            .or_else(|| production.origin().origin().exact_authored_range())
            .map(Box::new),
    }
}

#[cfg(test)]
mod tests {
    use super::{K_TOKENS, strongest_k_token};

    #[test]
    fn every_k_token_regex_is_readable() {
        for (sort, regex, _) in K_TOKENS {
            assert!(
                regex::Regex::new(&format!("^(?:{regex})$")).is_ok(),
                "{sort}: {regex}"
            );
        }
    }

    #[test]
    fn k_lexes_cell_names_with_its_strongest_matching_token() {
        assert_eq!(
            strongest_k_token("k").map(|token| (token.0, token.2)),
            Some(("#LowerId", 2))
        );
        assert_eq!(
            strongest_k_token("T").map(|token| (token.0, token.2)),
            Some(("#UpperId", 2))
        );
        assert_eq!(
            strongest_k_token("call-stack").map(|token| (token.0, token.2)),
            Some(("#CellName", 1))
        );
    }
}
