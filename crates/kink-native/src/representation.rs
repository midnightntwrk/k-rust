//! Admission of compiled sides whose token representations support syntactic comparison.
//!
//! This is a pure syntax gate (TB-03, VI-T12). It scans every compiled axiom, including
//! equations, lemmas and generated axioms, alias bodies, and the separately emitted macro and
//! alias rules, which k-rust prints as bare sentences (TB-03M).
//! String tokens are checked in the loaded KAST and in the compiled execution definition, which
//! holds the tokens kompile creates by constant folding (TB-03 review 1, F1). It does not
//! rewrite tokens: respelling one literal cannot make it agree with every Float format.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust::{
    definition::{AttributeKey, Definition as LoadedDefinition},
    kast::{Term, identifier::encode_sort_name},
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence, Sort},
        parser::{ParseError, parse_definition},
        walk,
    },
    names::KoreAttribute,
};

use crate::ValidatedDefinition;

/// The five representation premises required before execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RepresentationClause {
    FloatLiteral,
    MIntLiteral,
    TokenCreator,
    StringSpelling,
    RenamedIntLiteral,
}

impl fmt::Display for RepresentationClause {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::FloatLiteral => "G-F",
            Self::MIntLiteral => "G-M",
            Self::TokenCreator => "G-T",
            Self::StringSpelling => "G-S",
            Self::RenamedIntLiteral => "G-I",
        })
    }
}

/// A refused premise, together with the sentence that introduced it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepresentationFinding {
    pub clause: RepresentationClause,
    pub sort: String,
    pub sentence_unique_id: Option<String>,
    pub source: String,
}

impl fmt::Display for RepresentationFinding {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "representation clause {} refused sort {} at sentence UNIQUE_ID={} / source {}; k-rust compares Float/MInt tokens by spelling (VI-T12); respelling does not help",
            self.clause,
            self.sort,
            self.sentence_unique_id.as_deref().unwrap_or("<generated>"),
            self.source
        )
    }
}

impl std::error::Error for RepresentationFinding {}

/// Failure to establish representation admission, including unreadable compiled artifacts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepresentationError {
    Finding(RepresentationFinding),
    KoreParse(ParseError),
}

impl fmt::Display for RepresentationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Finding(finding) => finding.fmt(formatter),
            Self::KoreParse(error) => write!(
                formatter,
                "representation admission cannot parse compiled KORE: {error}"
            ),
        }
    }
}

impl std::error::Error for RepresentationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(match self {
            Self::Finding(finding) => finding,
            Self::KoreParse(error) => error,
        })
    }
}

impl From<RepresentationFinding> for RepresentationError {
    fn from(finding: RepresentationFinding) -> Self {
        Self::Finding(finding)
    }
}

impl From<ParseError> for RepresentationError {
    fn from(error: ParseError) -> Self {
        Self::KoreParse(error)
    }
}

/// Validate one already compiled side before any execution.
///
/// G-S scans both the loaded KAST and the compiled execution definition: kompile's constant
/// folding creates String tokens after loading (TB-03 review 1, F1), and the execution
/// definition is the KAST that the KORE emitter reads, after every transform stage.
pub fn validate_representation(side: &ValidatedDefinition) -> Result<(), RepresentationError> {
    let artifacts = side.artifacts();
    validate_kore_texts(
        &artifacts.definition_kore,
        &artifacts.syntax_definition_kore,
        &artifacts.macros_kore,
        &[side.definition(), &artifacts.execution_definition],
    )
}

/// Parse and check all three compiled KORE artifacts with one shared sort-hook registry.
/// Empty syntax/macro artifacts contain no sentences; the execution definition is required.
pub fn validate_representation_kore(
    definition: &str,
    syntax: &str,
    macros: &str,
    loaded: &LoadedDefinition,
) -> Result<(), RepresentationError> {
    validate_kore_texts(definition, syntax, macros, &[loaded])
}

fn validate_kore_texts(
    definition: &str,
    syntax: &str,
    macros: &str,
    kast: &[&LoadedDefinition],
) -> Result<(), RepresentationError> {
    let mut parsed = vec![parse_definition(definition)?];
    if !syntax.trim().is_empty() {
        parsed.push(parse_definition(syntax)?);
    }
    parsed.push(parse_macros(macros)?);
    validate_artifacts(&parsed.iter().collect::<Vec<_>>(), kast).map_err(Into::into)
}

/// Name of the synthetic module that holds the macro sentences; it appears only in diagnostics.
const MACROS_MODULE: &str = "MACROS";

/// Parse `macros_kore` in the form k-rust emits it (TB-03 review 2): the printed macro and alias
/// rules joined by newlines, with no definition attributes and no module (`kompile/compile.rs`,
/// Java's `macros.kore`). The text is read as the sentence list of one synthetic module, and the
/// parse must yield exactly that module with no attributes; text that closes the module or adds
/// another one is refused. A text whose first character is `[` cannot be a sentence list (every
/// sentence starts with a keyword); it is read as a whole KORE definition, the earlier API form,
/// which k-rust never emits. Every sentence either parse yields is scanned.
fn parse_macros(text: &str) -> Result<Definition, ParseError> {
    if text.trim_start().starts_with('[') {
        return parse_definition(text);
    }
    let prefix = format!("[] module {MACROS_MODULE}\n");
    let definition =
        parse_definition(&format!("{prefix}{text}\nendmodule []")).map_err(|error| ParseError {
            offset: error.offset.saturating_sub(prefix.len()),
            message: format!("macros_kore is not a KORE sentence list: {}", error.message),
        })?;
    match definition.modules.as_slice() {
        [module]
            if module.name == MACROS_MODULE
                && module.attributes.0.is_empty()
                && definition.attributes.0.is_empty() =>
        {
            Ok(definition)
        }
        _ => Err(ParseError {
            offset: 0,
            message: "macros_kore is not a KORE sentence list: it closes the module".into(),
        }),
    }
}

/// The same gate on parsed artifacts; exposed for clause-level tests without compiling
/// malformed or unsupported backend definitions.
pub fn validate_representation_ast(
    definition: &Definition,
    macros: Option<&Definition>,
    loaded: &LoadedDefinition,
) -> Result<(), RepresentationFinding> {
    validate_artifacts(
        &std::iter::once(definition)
            .chain(macros)
            .collect::<Vec<_>>(),
        &[loaded],
    )
}

fn validate_artifacts(
    artifacts: &[&Definition],
    kast: &[&LoadedDefinition],
) -> Result<(), RepresentationFinding> {
    let mut hooks = BTreeMap::new();
    for artifact in artifacts {
        for module in &artifact.modules {
            for sentence in &module.sentences {
                if let Sentence::SortDeclaration {
                    name, attributes, ..
                } = sentence
                    && let Some(hook) = attribute(attributes, KoreAttribute::Hook)
                {
                    hooks.insert(name.as_str(), hook);
                }
            }
        }
    }
    for artifact in artifacts {
        for module in &artifact.modules {
            for (index, sentence) in module.sentences.iter().enumerate() {
                let source = format!("{} sentence {index}", module.name);
                match sentence {
                    Sentence::SymbolDeclaration {
                        result_sort,
                        attributes,
                        ..
                    } if attribute(attributes, KoreAttribute::Hook)
                        == Some("STRING.string2token")
                        && token_result_refused(result_sort, &hooks) =>
                    {
                        return Err(finding(
                            RepresentationClause::TokenCreator,
                            result_sort,
                            attributes,
                            &source,
                        ));
                    }
                    Sentence::Axiom {
                        pattern,
                        attributes,
                        ..
                    }
                    | Sentence::Claim {
                        pattern,
                        attributes,
                        ..
                    }
                    // The backend unfolds alias bodies into axioms (TB-03 review 1, minor).
                    | Sentence::AliasDeclaration {
                        right: pattern,
                        attributes,
                        ..
                    } => {
                        let mut work = vec![pattern.as_ref()];
                        while let Some(node) = work.pop() {
                            if let Pattern::DomainValue { sort, value } = node {
                                let clause = match sort_hook(sort, &hooks) {
                                    Some("FLOAT.Float") => Some(RepresentationClause::FloatLiteral),
                                    Some("MINT.MInt") => Some(RepresentationClause::MIntLiteral),
                                    Some("INT.Int")
                                        if sort_name(sort) != "SortInt"
                                            && !canonical_decimal(value.as_bytes()) =>
                                    {
                                        Some(RepresentationClause::RenamedIntLiteral)
                                    }
                                    // k-rust's String values are UTF-8 text; a compiled byte
                                    // that is not denotes no K String (TB-03 review 1, F1).
                                    Some("STRING.String") if value.as_utf8().is_err() => {
                                        Some(RepresentationClause::StringSpelling)
                                    }
                                    _ => None,
                                };
                                if let Some(clause) = clause {
                                    return Err(finding(clause, sort, attributes, &source));
                                }
                            }
                            work.extend(walk::children(node).into_iter().rev());
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    for definition in kast {
        string_tokens(definition, &hooks)?;
    }
    Ok(())
}

/// G-S over one KAST definition: every token of a String-hooked sort, in any sentence of any
/// module, including modules outside the compiled closure.
fn string_tokens(
    loaded: &LoadedDefinition,
    hooks: &BTreeMap<&str, &str>,
) -> Result<(), RepresentationFinding> {
    let mut loaded_string_sorts = BTreeSet::new();
    for module in &loaded.modules {
        for sentence in &module.local_sentences {
            if let k_rust::definition::Sentence::SyntaxSort {
                sort, attributes, ..
            } = sentence.as_ref()
                && attributes.string(AttributeKey::Hook) == Some("STRING.String")
            {
                loaded_string_sorts.insert(sort.name.as_str());
            }
        }
    }
    for module in &loaded.modules {
        for (index, sentence) in module.local_sentences.iter().enumerate() {
            for (_, term) in sentence.terms() {
                let mut work = vec![term];
                while let Some(node) = work.pop() {
                    match node.unannotated() {
                        Term::Token { token, sort }
                            if (hooks.get(encode_sort_name(&sort.name).as_str())
                                == Some(&"STRING.String")
                                || loaded_string_sorts.contains(sort.name.as_str()))
                                && string_spelling_refused(token) =>
                        {
                            let attributes = sentence.attributes();
                            return Err(RepresentationFinding {
                                clause: RepresentationClause::StringSpelling,
                                sort: encode_sort_name(&sort.name),
                                sentence_unique_id: attributes
                                    .string(AttributeKey::UniqueId)
                                    .map(str::to_owned),
                                source: attributes.source().map(str::to_owned).unwrap_or_else(
                                    || format!("{} loaded sentence {index}", module.name),
                                ),
                            });
                        }
                        Term::Rewrite { left, right } => {
                            work.extend([right.as_ref(), left.as_ref()])
                        }
                        Term::As { pattern, alias } => {
                            work.extend([alias.as_ref(), pattern.as_ref()])
                        }
                        Term::Apply { arguments, .. } | Term::Sequence(arguments) => {
                            work.extend(arguments.iter().rev())
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    Ok(())
}

fn attribute(attributes: &Attributes, key: KoreAttribute) -> Option<&str> {
    attributes.string(key).ok().flatten()
}

fn sort_name(sort: &Sort) -> &str {
    match sort {
        Sort::Application { name, .. } | Sort::Variable(name) => name,
    }
}

fn sort_hook<'a>(sort: &Sort, hooks: &BTreeMap<&str, &'a str>) -> Option<&'a str> {
    match sort {
        Sort::Application { name, .. } => hooks.get(name.as_str()).copied(),
        Sort::Variable(_) => None,
    }
}

fn token_result_refused(sort: &Sort, hooks: &BTreeMap<&str, &str>) -> bool {
    let mut work = vec![sort];
    while let Some(node) = work.pop() {
        match node {
            Sort::Variable(_) => return true,
            Sort::Application { arguments, .. } => work.extend(arguments),
        }
    }
    matches!(
        sort_hook(sort, hooks),
        Some("FLOAT.Float" | "MINT.MInt" | "BOOL.Bool")
    ) || (sort_hook(sort, hooks) == Some("INT.Int") && sort_name(sort) != "SortInt")
}

fn finding(
    clause: RepresentationClause,
    sort: &Sort,
    attributes: &Attributes,
    fallback: &str,
) -> RepresentationFinding {
    RepresentationFinding {
        clause,
        sort: sort_name(sort).to_owned(),
        sentence_unique_id: attribute(attributes, KoreAttribute::UniqueId).map(str::to_owned),
        source: attribute(attributes, KoreAttribute::Source)
            .unwrap_or(fallback)
            .to_owned(),
    }
}

/// Canonical decimal Int text: `0`, or an optional minus and a nonzero leading digit.
pub(crate) fn canonical_decimal(value: &[u8]) -> bool {
    if value == b"0" {
        return true;
    }
    let digits = value.strip_prefix(b"-").unwrap_or(value);
    matches!(digits.first(), Some(b'1'..=b'9')) && digits.iter().all(u8::is_ascii_digit)
}

// Replicas of the two pinned KAST decoders. Keeping both interpretations makes the comparison
// independent of kompile's chosen byte decoder. The extra octal/high-byte rules are the
// fail-closed G-S amendment: even ASCII octal must not be silently admitted by equality.
fn string_spelling_refused(token: &str) -> bool {
    let mut chars = token.chars();
    while let Some(character) = chars.next() {
        if character != '\\' {
            continue;
        }
        match chars.next() {
            Some('0'..='9') => return true,
            Some('x') => {
                let digits: String = chars.by_ref().take(2).collect();
                if u8::from_str_radix(&digits, 16).is_ok_and(|byte| byte >= 0x80) {
                    return true;
                }
            }
            _ => {}
        }
    }
    match (unquote_bytes(token), unquote(token)) {
        (Ok(bytes), Ok(text)) => bytes != text.into_bytes(),
        _ => true,
    }
}

fn unquote(input: &str) -> Result<String, &'static str> {
    let body = quoted_body(input)?;
    let mut output = String::new();
    let mut characters = body.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            output.push(character);
            continue;
        }
        match characters.next().ok_or("truncated escape")? {
            '"' => output.push('"'),
            '\\' => output.push('\\'),
            'n' => output.push('\n'),
            'r' => output.push('\r'),
            't' => output.push('\t'),
            'f' => output.push('\u{000c}'),
            'x' => output.push(scalar(read_hex(&mut characters, 2)?)?),
            'u' => output.push(scalar(read_hex(&mut characters, 4)?)?),
            'U' => output.push(scalar(read_hex(&mut characters, 8)?)?),
            digit @ '0'..='9' => {
                let digits: String = std::iter::once(digit)
                    .chain(characters.by_ref().take(2))
                    .collect();
                if digits.len() != 3 {
                    return Err("truncated octal escape");
                }
                output.push(scalar(
                    u32::from_str_radix(&digits, 8).map_err(|_| "invalid octal escape")?,
                )?);
            }
            _ => {}
        }
    }
    Ok(output)
}

fn unquote_bytes(input: &str) -> Result<Vec<u8>, &'static str> {
    let body = quoted_body(input)?;
    let mut output = Vec::new();
    let mut characters = body.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            push_scalar(&mut output, character);
            continue;
        }
        match characters.next().ok_or("truncated escape")? {
            '"' => output.push(b'"'),
            '\\' => output.push(b'\\'),
            'n' => output.push(b'\n'),
            'r' => output.push(b'\r'),
            't' => output.push(b'\t'),
            'f' => output.push(0x0c),
            'x' => output.push(read_hex(&mut characters, 2)? as u8),
            'u' => push_scalar(&mut output, scalar(read_hex(&mut characters, 4)?)?),
            'U' => push_scalar(&mut output, scalar(read_hex(&mut characters, 8)?)?),
            digit @ '0'..='9' => {
                let digits: String = std::iter::once(digit)
                    .chain(characters.by_ref().take(2))
                    .collect();
                if digits.len() != 3 {
                    return Err("truncated octal escape");
                }
                let value = u16::from_str_radix(&digits, 8).map_err(|_| "invalid octal escape")?;
                output.push(u8::try_from(value).map_err(|_| "octal byte escape out of range")?);
            }
            _ => return Err("unsupported escape"),
        }
    }
    Ok(output)
}

fn quoted_body(input: &str) -> Result<&str, &'static str> {
    input
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
        .ok_or("expected a double-quoted string")
}

fn read_hex(
    characters: &mut impl Iterator<Item = char>,
    digits: usize,
) -> Result<u32, &'static str> {
    let value: String = characters.take(digits).collect();
    if value.len() != digits {
        return Err("truncated Unicode escape");
    }
    u32::from_str_radix(&value, 16).map_err(|_| "invalid Unicode escape")
}

fn scalar(value: u32) -> Result<char, &'static str> {
    char::from_u32(value).ok_or("invalid Unicode scalar")
}

fn push_scalar(output: &mut Vec<u8>, character: char) {
    let mut buffer = [0; 4];
    output.extend_from_slice(character.encode_utf8(&mut buffer).as_bytes());
}
