//! `k::patterns!` chains for kink (FB-49): each part's K rule-content text, read in memory.
//!
//! A part of a chain is the readable claim whose subject is the part's set of states, with no
//! result, so its claim body is exactly the K pattern kink lowers: its cell clauses, every one
//! only read, and its `requires`. Nothing here is written to `definition.k` or `spec.k`
//! ([`is_pattern_part`]): a pattern is a question kink asks of runs, not a sentence of the
//! definition, so a definition with or without one emits the same K.
//!
//! Two parts share a value only through a binder both name (kink reads a variable two parts
//! name as one variable of the chain). So every variable no author named is renamed apart per
//! part, and a binder two parts name must be one variable, of one K name and one sort, in each.

use std::collections::BTreeMap;

use krs_ir::{PatternDecl, SourceMapKey};
use krs_ir_levels::{DefinitionIr, DefinitionModule, DefinitionSentence, RuleSentence};

use super::{EmitContext, EmitError, Writer, sentence::emit_pattern_part};

fn pattern_of(sentence: &DefinitionSentence) -> Option<(&RuleSentence, &PatternDecl)> {
    match sentence {
        DefinitionSentence::Rule(rule) => rule
            .claim()
            .and_then(krs_ir_levels::DefinitionClaim::pattern)
            .map(|pattern| (rule, pattern)),
        _ => None,
    }
}

/// One step of an emitted chain: the step's K text and its arrow's `unless`, if any.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedPatternStep {
    /// K rule content, `requires` inline, that kink-flow's `Lowering::lower` parses in the
    /// definition's main module.
    pub pattern: String,
    /// The `unless` of the arrow into this step, in the same form; never on step 1.
    pub unless: Option<String>,
}

/// One binder of a chain: its K variable and its KRS name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PatternVariable {
    /// The K variable's name in every part that names it (`Before`).
    pub k: String,
    /// The binder as the author wrote it (`before`).
    pub krs: String,
    /// The K sort of the variable (`Int`).
    pub sort: String,
}

/// Where a pattern's clause is written: its package, its file and its byte range there. The
/// Definition IR holds no source text, so a caller that needs the line reads the file
/// ([`PatternSource::line`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternSource {
    /// The Cargo package of the authored file.
    pub package: String,
    /// The package-relative path of the file, slash-separated.
    pub file: String,
    /// The clause name's first byte in the file.
    pub start_byte: u32,
}

impl PatternSource {
    /// The 1-based line of [`Self::start_byte`] in `text`, the file's contents.
    #[must_use]
    pub fn line(&self, text: &str) -> u32 {
        let end = usize::try_from(self.start_byte)
            .unwrap_or(usize::MAX)
            .min(text.len());
        let lines = text.get(..end).unwrap_or(text).matches('\n').count();
        u32::try_from(lines).map_or(u32::MAX, |lines| lines.saturating_add(1))
    }
}

/// One `k::patterns!` clause, emitted for kink.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedPattern {
    /// The pattern's id, the clause name with `_` written `-`.
    pub id: String,
    /// The clause's documentation.
    pub note: Option<String>,
    /// The clause's Rust item, `crate::module::name`.
    pub item: String,
    /// Where the clause is written.
    pub source: PatternSource,
    /// `#[k::cases(..)]`: the programs the author claims hit the pattern.
    pub programs: Option<Vec<String>>,
    /// `#[k::expect(no)]`: `"no"`.
    pub expect: Option<String>,
    /// The steps in order.
    pub steps: Vec<EmittedPatternStep>,
    /// Every binder of the clause, by its KRS name.
    pub variables: Vec<PatternVariable>,
}

/// One part, rendered.
struct Part<'d> {
    decl: &'d PatternDecl,
    sentence: &'d RuleSentence,
    text: String,
    /// The part's variables a binder of the clause names: KRS name, K name, sort, occurrence.
    variables: BTreeMap<String, (String, String, SourceMapKey)>,
}

/// Emits every `k::patterns!` chain of `definition`, in id order.
///
/// # Errors
///
/// Returns [`EmitError::PatternBinder`] when a binder two parts name is not one variable of the
/// chain (two sorts, or no variable in a part), and any rendering failure of a part.
pub fn emit_patterns(definition: &DefinitionIr) -> Result<Vec<EmittedPattern>, EmitError> {
    let mut context = EmitContext::new(definition);
    context.constant_markers = false;
    let mut chains: BTreeMap<&str, Vec<Part<'_>>> = BTreeMap::new();
    for sentence in definition
        .modules()
        .iter()
        .filter(|module| !module.is_spec())
        .flat_map(DefinitionModule::pattern_parts)
    {
        let Some((rule, decl)) = pattern_of(sentence) else {
            continue;
        };
        chains
            .entry(decl.id.as_str())
            .or_default()
            .push(render_part(rule, decl, &context)?);
    }
    chains
        .into_values()
        .map(|parts| chain(definition, parts))
        .collect()
}

fn sentence_source(sentence: &RuleSentence) -> Option<(String, String, u32)> {
    match sentence.origin().origin().frames().first()? {
        krs_ir::OriginFrame::Ranged {
            kind: krs_ir::RangedOriginKind::Authored,
            range,
            ..
        } => Some((
            range.file.package().cargo_name().to_owned(),
            range.file.package_relative_path().to_owned(),
            range.start_byte,
        )),
        _ => None,
    }
}

fn render_part<'d>(
    sentence: &'d RuleSentence,
    decl: &'d PatternDecl,
    context: &EmitContext<'_>,
) -> Result<Part<'d>, EmitError> {
    let suffix = if decl.unless {
        format!("_Unless{}", decl.step)
    } else {
        format!("_Step{}", decl.step)
    };
    let names = context
        .naming
        .rule(sentence)
        .renamed_apart(&suffix)
        .ok_or_else(|| EmitError::UnsupportedShape {
            node: "pattern part",
            detail: format!(
                "a variable of `{}` renamed apart as its part's own takes a name the part holds",
                decl.name
            ),
        })?;
    let mut writer = Writer::default();
    emit_pattern_part(sentence, &names, context, &mut writer)?;
    let mut variables = BTreeMap::new();
    for variable in sentence.variables() {
        let krs = variable.id().as_str();
        if !decl.binders.iter().any(|binder| binder == krs) {
            continue;
        }
        let name = names.name(variable.id()).ok_or_else(|| {
            EmitError::InvalidReference(format!("pattern variable {krs:?} is not named"))
        })?;
        variables.insert(
            krs.to_owned(),
            (
                name.to_owned(),
                context.sort_name_ref(variable.sort())?.into_owned(),
                sentence.origin().key().clone(),
            ),
        );
    }
    Ok(Part {
        decl,
        sentence,
        text: one_line(&writer.source),
        variables,
    })
}

/// The text with each run of layout outside a string literal written as one space.
fn one_line(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut space = false;
    for character in text.chars() {
        if in_string {
            output.push(character);
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }
        if character.is_whitespace() {
            space = true;
            continue;
        }
        if space && !output.is_empty() {
            output.push(' ');
        }
        space = false;
        if character == '"' {
            in_string = true;
        }
        output.push(character);
    }
    output
}

fn part_name(decl: &PatternDecl) -> String {
    if decl.unless {
        format!("the `unless` before step {}", decl.step)
    } else {
        format!("step {}", decl.step)
    }
}

fn chain(definition: &DefinitionIr, mut parts: Vec<Part<'_>>) -> Result<EmittedPattern, EmitError> {
    parts.sort_by_key(|part| (part.decl.step, !part.decl.unless));
    let first = parts
        .first()
        .ok_or_else(|| EmitError::InvalidReference("a pattern has a part".to_owned()))?;
    let decl = first.decl;
    // Every binder two parts name is one variable of the chain: one K name and one sort in
    // every part that names it, and a variable in each.
    let mut variables: BTreeMap<String, (String, String, usize)> = BTreeMap::new();
    for (index, part) in parts.iter().enumerate() {
        for binder in &part.decl.binders {
            let Some((k, sort, key)) = part.variables.get(binder) else {
                let shared = parts
                    .iter()
                    .any(|other| !std::ptr::eq(other, part) && other.decl.binders.contains(binder));
                if shared {
                    return Err(EmitError::PatternBinder {
                        key: part.sentence.origin().key().clone(),
                        reason: format!(
                            "`{binder}` is no variable in {} of `{}`: there it names the cells of a group, which the pattern writes as those cells and not as one value; steps share values only through variables, so name the cell's own value instead",
                            part_name(part.decl),
                            decl.name,
                        ),
                    });
                }
                continue;
            };
            match variables.get(binder) {
                None => {
                    variables.insert(binder.clone(), (k.clone(), sort.clone(), index));
                }
                Some((first_k, first_sort, first_index)) => {
                    if first_sort != sort {
                        return Err(EmitError::PatternBinder {
                            key: key.clone(),
                            reason: format!(
                                "`{binder}` is `{first_sort}` in {} of `{}` and `{sort}` in {}: a binder is one variable of the pattern, so its occurrences have one sort; write its value at positions of one sort, or name the two values apart",
                                part_name(parts[*first_index].decl),
                                decl.name,
                                part_name(part.decl),
                            ),
                        });
                    }
                    if first_k != k {
                        return Err(EmitError::UnsupportedShape {
                            node: "pattern variable",
                            detail: format!(
                                "`{binder}` of `{}` is spelled `{first_k}` and `{k}` in two parts",
                                decl.name
                            ),
                        });
                    }
                }
            }
        }
    }
    let mut steps: Vec<EmittedPatternStep> = Vec::new();
    let mut unless = None;
    for part in &parts {
        if part.decl.unless {
            unless = Some(part.text.clone());
        } else {
            steps.push(EmittedPatternStep {
                pattern: part.text.clone(),
                unless: unless.take(),
            });
        }
    }
    let (package, file, start_byte) = sentence_source(first.sentence).unwrap_or_default();
    let item = first
        .sentence_item(definition)
        .unwrap_or_else(|| decl.name.clone());
    Ok(EmittedPattern {
        id: decl.id.clone(),
        note: decl.note.clone(),
        item,
        source: PatternSource {
            package,
            file,
            start_byte,
        },
        programs: decl.programs.clone(),
        expect: decl.expect.map(|expect| expect.as_str().to_owned()),
        steps,
        variables: variables
            .into_iter()
            .map(|(krs, (k, sort, _))| PatternVariable { k, krs, sort })
            .collect(),
    })
}

impl Part<'_> {
    /// The Rust path of the part's item, from its crate.
    fn sentence_item(&self, definition: &DefinitionIr) -> Option<String> {
        let id = self
            .sentence
            .origin()
            .origin()
            .frames()
            .iter()
            .find_map(|frame| match frame {
                krs_ir::OriginFrame::Ranged { item, .. }
                | krs_ir::OriginFrame::Transformation { item, .. } => item.as_ref(),
                krs_ir::OriginFrame::Inserted { .. } => None,
            })?;
        let crate_name = krs_ir::crate_name_in(definition.crate_names(), id.package());
        let mut path = vec![crate_name];
        path.extend(id.module_path().iter().cloned());
        path.push(id.item_name().to_owned());
        Some(path.join("::"))
    }
}
