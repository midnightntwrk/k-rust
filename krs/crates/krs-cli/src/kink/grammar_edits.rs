//! The grammar judgement: whether an edit of the grammar declarations KRS emits (a production,
//! a priority or an associativity sentence; [`krs_compiler::SentenceVerdict::Grammar`]) is a
//! grammar mutant kink can judge.
//!
//! A grammar mutant models an implementer's parser: kink parses every case again under the
//! mutant's grammar and keeps the rules' terms. So what an edit may change is decided by
//! whether the part affects the parse function (program text to term), not by whether some
//! Rust source emits the result:
//!
//! - editable: a production's items (terminal and regex literals, nonterminal sorts, a list's
//!   element and separator), its result sort, the attributes that choose among parses or lex a
//!   token ([`PARSE_ATTRIBUTES`]), a priority or associativity sentence, a production or
//!   relation added or removed;
//! - print-only: `format`, `color` and `colors` say how a term prints; a `format` the mutant
//!   writes must be well formed for the edited items (each item referenced once, in order),
//!   else the edit is refused `derived-mismatch`;
//! - kept: `symbol` and `klabel` name the constructor the rules' terms use (kink-flow refuses
//!   a changed declared label, `label-changed`, before this judgement; productions are paired
//!   by it, so a production under a new symbol is read as one deleted and one inserted);
//! - every other attribute (`strict`, `result`, `function`, `private`, ...) says what the
//!   constructor means or who sees it, not how a text parses, so an edit of one is no grammar
//!   mutation and is refused `not-judged`.
//!
//! An edit whose declarations parse every text as the specification's do (only print-only
//! parts changed, tags reordered inside a group, or every change outside the modules the
//! program grammar imports) is refused `no-parse-change`.
//!
//! Both texts are read by k-rust's outer parser, which reads declarations as written and
//! parses no rule body; each module's sentences are paired by their structure, spans ignored,
//! and each run of unpaired sentences is judged: productions paired by their `symbol`, then in
//! order; priority and associativity sentences compared as relations.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use k_rust::outer::{
    self, Associativity, Attribute, Module, Position, Production, ProductionItem, Sentence, Span,
    SyntaxBody,
};

/// The attributes of a production that change which text parses to which term: a group (which
/// the priority and associativity sentences name), the disambiguation filters, a bracket, and
/// a token's lexing.
pub(crate) const PARSE_ATTRIBUTES: [&str; 6] =
    ["group", "avoid", "prefer", "bracket", "token", "prec"];
/// The attributes that say only how a term prints.
const PRINT_ATTRIBUTES: [&str; 3] = ["format", "color", "colors"];
/// The attributes that name the constructor.
const NAME_ATTRIBUTES: [&str; 2] = ["symbol", "klabel"];

/// Why the grammar judgement refuses an edit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum GrammarRefusal {
    /// The edited declarations parse every text as the specification's do.
    NoParseChange(String),
    /// A `format` the mutant writes is not well formed for its production's items.
    MalformedFormat(String),
    /// The edit changes what the judgement does not read as grammar.
    NotJudged(String),
}

/// A refusal with the baseline byte its declarations start at (the place of the edit that
/// makes it).
pub(crate) type Placed = (usize, GrammarRefusal);

/// Judges the grammar edits that turn `baseline` into `mutant`, two texts of `definition.k`,
/// where `syntax_module` is the module whose grammar parses programs. `Ok(())` admits the
/// mutation as a grammar mutant; otherwise the refusals, in text order.
pub(crate) fn judge(baseline: &str, mutant: &str, syntax_module: &str) -> Result<(), Vec<Placed>> {
    let unread = |which: &str, error: &dyn std::fmt::Display| {
        vec![(
            0,
            GrammarRefusal::NotJudged(format!(
                "k-rust's outer parser does not read the {which}: {error}"
            )),
        )]
    };
    let before = outer::parse("definition.k", baseline).map_err(|e| unread("specification", &e))?;
    let after = outer::parse("definition.k", mutant).map_err(|e| unread("mutant", &e))?;
    let names = |file: &outer::SourceFile| {
        file.modules
            .iter()
            .map(|module| {
                let imports = module
                    .imports
                    .iter()
                    .map(|import| (import.module.clone(), import.public))
                    .collect::<Vec<_>>();
                (module.name.clone(), imports, module.attributes.clone())
            })
            .collect::<Vec<_>>()
    };
    let requires = |file: &outer::SourceFile| {
        file.requires
            .iter()
            .map(|require| require.path.clone())
            .collect::<Vec<_>>()
    };
    if names(&before) != names(&after) || requires(&before) != requires(&after) {
        return Err(vec![(
            0,
            GrammarRefusal::NotJudged(
                "the edit changes a module, an import or a require, which is no grammar \
                 declaration"
                    .into(),
            ),
        )]);
    }
    let parsed = program_modules(&before, syntax_module);
    let mut judgement = Judgement::default();
    for (old, new) in before.modules.iter().zip(&after.modules) {
        let reaches = parsed.contains(old.name.as_str());
        for hunk in hunks(old, new) {
            judgement.hunk(old, &hunk, reaches);
        }
    }
    judgement.finish()
}

/// The modules whose sentences the program grammar reads: `syntax_module` (else the first
/// module, when the text has none of that name) and every module it imports, transitively,
/// within the text.
fn program_modules<'f>(file: &'f outer::SourceFile, syntax_module: &str) -> BTreeSet<&'f str> {
    let by_name = file
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let start = by_name
        .get_key_value(syntax_module)
        .map(|(name, _)| *name)
        .or_else(|| file.modules.first().map(|module| module.name.as_str()));
    let mut reached = BTreeSet::new();
    let mut pending = start.into_iter().collect::<Vec<_>>();
    while let Some(name) = pending.pop() {
        if !reached.insert(name) {
            continue;
        }
        if let Some(module) = by_name.get(name) {
            pending.extend(module.imports.iter().map(|import| import.module.as_str()));
        }
    }
    reached
}

/// One run of unpaired sentences of a module: the baseline's `old` and the mutant's `new`.
struct Hunk<'m> {
    old: Vec<&'m Sentence>,
    new: Vec<&'m Sentence>,
    /// The baseline byte the run starts at (for an insertion, where it is inserted).
    at: usize,
}

/// The runs of sentences a longest common subsequence of equal sentences (spans ignored)
/// leaves unpaired.
fn hunks<'m>(old: &'m Module, new: &'m Module) -> Vec<Hunk<'m>> {
    let (olds, news) = (&old.sentences, &new.sentences);
    let old_keys = olds.iter().map(unspanned).collect::<Vec<_>>();
    let new_keys = news.iter().map(unspanned).collect::<Vec<_>>();
    let (n, m) = (olds.len(), news.len());
    // Invariant: `lengths[i][j]` is the length of a longest common subsequence of `olds[i..]`
    // and `news[j..]`, filled from the ends.
    let mut lengths = vec![vec![0_usize; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            lengths[i][j] = if old_keys[i] == new_keys[j] {
                lengths[i + 1][j + 1] + 1
            } else {
                lengths[i + 1][j].max(lengths[i][j + 1])
            };
        }
    }
    let end_of = |index: usize| {
        index.checked_sub(1).map_or(old.span.start.offset, |last| {
            span_of(&olds[last]).end.offset
        })
    };
    let mut hunks = Vec::new();
    let (mut i, mut j) = (0, 0);
    let mut current: Option<Hunk<'m>> = None;
    while i < n || j < m {
        if i < n && j < m && old_keys[i] == new_keys[j] {
            hunks.extend(current.take());
            i += 1;
            j += 1;
            continue;
        }
        let hunk = current.get_or_insert_with(|| Hunk {
            old: Vec::new(),
            new: Vec::new(),
            at: if i < n {
                span_of(&olds[i]).start.offset
            } else {
                end_of(i)
            },
        });
        if j < m && (i == n || lengths[i][j + 1] >= lengths[i + 1][j]) {
            hunk.new.push(&news[j]);
            j += 1;
        } else {
            hunk.old.push(&olds[i]);
            i += 1;
        }
    }
    hunks.extend(current);
    hunks
}

const NO_POSITION: Position = Position {
    offset: 0,
    line: 0,
    column: 0,
};
const NO_SPAN: Span = Span {
    start: NO_POSITION,
    end: NO_POSITION,
};

/// `sentence` with every span cleared, so that two sentences compare by what they declare.
fn unspanned(sentence: &Sentence) -> Sentence {
    let mut sentence = sentence.clone();
    match &mut sentence {
        Sentence::Syntax(syntax) => {
            syntax.span = NO_SPAN;
            if let SyntaxBody::Productions(blocks) = &mut syntax.body {
                for block in blocks {
                    block.span = NO_SPAN;
                    for production in &mut block.productions {
                        production.span = NO_SPAN;
                    }
                }
            }
        }
        Sentence::Priority(priority) => priority.span = NO_SPAN,
        Sentence::Associativity(associativity) => associativity.span = NO_SPAN,
        Sentence::Lexical(lexical) => lexical.span = NO_SPAN,
        Sentence::Bubble(bubble) => {
            bubble.span = NO_SPAN;
            bubble.content_span = NO_SPAN;
        }
    }
    sentence
}

const fn span_of(sentence: &Sentence) -> Span {
    match sentence {
        Sentence::Syntax(syntax) => syntax.span,
        Sentence::Priority(priority) => priority.span,
        Sentence::Associativity(associativity) => associativity.span,
        Sentence::Lexical(lexical) => lexical.span,
        Sentence::Bubble(bubble) => bubble.span,
    }
}

/// One production of a hunk with what its declaration gives it: the result sort, and the
/// relations its declaration states between its blocks (`>` and `left:`).
struct Declared<'m> {
    module: &'m str,
    sort: String,
    production: &'m Production,
    /// The block's index in its declaration and its associativity, which are relations of
    /// the grammar too.
    block: (usize, Associativity),
}

impl Declared<'_> {
    fn symbol(&self) -> Option<&str> {
        self.production
            .attributes
            .iter()
            .find(|attribute| NAME_ATTRIBUTES.contains(&attribute.key.as_str()))
            .and_then(|attribute| attribute.value.as_deref())
    }

    /// The production as a detail names it.
    fn named(&self) -> String {
        match self.symbol() {
            Some(symbol) => format!("production `{symbol}` of {}", self.module),
            None => format!(
                "the production of sort {} `{}` of {}",
                self.sort,
                items_text(&self.production.items),
                self.module
            ),
        }
    }

    /// What the program parser reads of the production: its sort, items, block relations and
    /// the attributes that change a parse, each attribute by its key and value.
    fn parse_part(
        &self,
    ) -> (
        String,
        &[ProductionItem],
        (usize, Associativity),
        Vec<&Attribute>,
    ) {
        (
            self.sort.clone(),
            &self.production.items,
            self.block,
            attributes_in(&self.production.attributes, &PARSE_ATTRIBUTES),
        )
    }
}

fn attributes_in<'a>(attributes: &'a [Attribute], keys: &[&str]) -> Vec<&'a Attribute> {
    let mut chosen = attributes
        .iter()
        .filter(|attribute| keys.contains(&attribute.key.as_str()))
        .collect::<Vec<_>>();
    chosen.sort_by(|a, b| (&a.key, &a.value).cmp(&(&b.key, &b.value)));
    chosen
}

/// The attributes that are neither parse, print nor name attributes, sorted.
fn meaning_attributes(attributes: &[Attribute]) -> Vec<&Attribute> {
    let mut chosen = attributes
        .iter()
        .filter(|attribute| {
            let key = attribute.key.as_str();
            !PARSE_ATTRIBUTES.contains(&key)
                && !PRINT_ATTRIBUTES.contains(&key)
                && !NAME_ATTRIBUTES.contains(&key)
        })
        .collect::<Vec<_>>();
    chosen.sort_by(|a, b| (&a.key, &a.value).cmp(&(&b.key, &b.value)));
    chosen
}

fn attribute_text(attribute: &Attribute) -> String {
    attribute.value.as_ref().map_or_else(
        || attribute.key.clone(),
        |value| format!("{}({value})", attribute.key),
    )
}

fn items_text(items: &[ProductionItem]) -> String {
    items
        .iter()
        .map(|item| match item {
            ProductionItem::Terminal(text) => format!("{text:?}"),
            ProductionItem::Regex(regex) => format!("r{regex:?}"),
            ProductionItem::NonTerminal { sort, .. } => sort.name.clone(),
            ProductionItem::UserList {
                sort,
                separator,
                non_empty,
            } => format!(
                "{}{{{}, {separator:?}}}",
                if *non_empty { "NeList" } else { "List" },
                sort.name
            ),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// A relation sentence as the parser reads it: a priority as its groups of tags, an
/// associativity as its kind and tags.
#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Relation {
    Priority(Vec<BTreeSet<String>>),
    Associativity(String, BTreeSet<String>),
}

/// What the hunks of a mutation give.
#[derive(Default)]
struct Judgement {
    refusals: Vec<Placed>,
    /// Whether some edit changes what the program parser reads.
    parse_changed: bool,
    /// What the edits change that the program parser does not read, for the
    /// `no-parse-change` detail.
    unparsed: Vec<String>,
    /// The baseline byte of the first hunk.
    first: Option<usize>,
}

impl Judgement {
    fn refuse(&mut self, at: usize, refusal: GrammarRefusal) {
        self.refusals.push((at, refusal));
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One pass over a hunk's sentences, each kind of change judged in place."
    )]
    fn hunk(&mut self, module: &Module, hunk: &Hunk<'_>, reaches: bool) {
        self.first.get_or_insert(hunk.at);
        let at = hunk.at;
        let mut old_productions = Vec::new();
        let mut new_productions = Vec::new();
        let mut old_relations = Vec::new();
        let mut new_relations = Vec::new();
        for (sentences, productions, relations) in [
            (&hunk.old, &mut old_productions, &mut old_relations),
            (&hunk.new, &mut new_productions, &mut new_relations),
        ] {
            for sentence in sentences {
                match sentence {
                    Sentence::Syntax(syntax) => match &syntax.body {
                        SyntaxBody::Productions(blocks) => {
                            if syntax.name.is_some() || !syntax.parameters.is_empty() {
                                self.refuse(
                                    at,
                                    GrammarRefusal::NotJudged(format!(
                                        "the edit changes a parametric or named syntax \
                                         declaration of sort {} in {}, which KRS does not emit",
                                        syntax.sort.name, module.name
                                    )),
                                );
                                continue;
                            }
                            for (index, block) in blocks.iter().enumerate() {
                                for production in &block.productions {
                                    productions.push(Declared {
                                        module: &module.name,
                                        sort: syntax.sort.name.clone(),
                                        production,
                                        block: (index, block.associativity),
                                    });
                                }
                            }
                        }
                        SyntaxBody::Sort(_) | SyntaxBody::Synonym { .. } => self.refuse(
                            at,
                            GrammarRefusal::NotJudged(format!(
                                "the edit changes the declaration of sort {} in {}, which is no \
                                 production, priority or associativity",
                                syntax.sort.name, module.name
                            )),
                        ),
                    },
                    Sentence::Priority(priority) => relations.push(Relation::Priority(
                        priority
                            .groups
                            .iter()
                            .map(|group| group.iter().cloned().collect())
                            .collect(),
                    )),
                    Sentence::Associativity(associativity) => {
                        relations.push(Relation::Associativity(
                            format!("{:?}", associativity.associativity),
                            associativity.tags.iter().cloned().collect(),
                        ));
                    }
                    Sentence::Lexical(lexical) => self.refuse(
                        at,
                        GrammarRefusal::NotJudged(format!(
                            "the edit changes the lexical declaration `{}` in {}, which KRS \
                             does not emit",
                            lexical.name, module.name
                        )),
                    ),
                    Sentence::Bubble(bubble) => self.refuse(
                        at,
                        GrammarRefusal::NotJudged(format!(
                            "the edit changes a {} in {}, and a grammar mutation edits grammar \
                             declarations alone",
                            match bubble.kind {
                                outer::BubbleKind::Rule => "rule",
                                outer::BubbleKind::Claim => "claim",
                                outer::BubbleKind::Context => "context",
                                outer::BubbleKind::ContextAlias => "context alias",
                                outer::BubbleKind::Configuration => "configuration",
                            },
                            module.name
                        )),
                    ),
                }
            }
        }
        old_relations.sort();
        new_relations.sort();
        if old_relations != new_relations {
            self.parse_change(reaches, || {
                format!("a priority or associativity sentence of {}", module.name)
            });
        } else if !hunk.old.is_empty() && hunk.old.iter().any(|s| !matches!(s, Sentence::Syntax(_)))
        {
            self.unparsed.push(format!(
                "the order of tags inside a priority or associativity group of {}",
                module.name
            ));
        }
        // Productions: by their symbol, then the unnamed ones in order.
        let mut pairs = Vec::new();
        let mut inserted = Vec::new();
        let mut paired_old = vec![false; old_productions.len()];
        let mut unnamed_new = Vec::new();
        for new in &new_productions {
            let partner = new.symbol().and_then(|symbol| {
                old_productions
                    .iter()
                    .position(|old| old.symbol() == Some(symbol))
            });
            match (partner, new.symbol()) {
                (Some(index), _) => {
                    paired_old[index] = true;
                    pairs.push((&old_productions[index], new));
                }
                (None, Some(_)) => inserted.push(new),
                (None, None) => unnamed_new.push(new),
            }
        }
        let mut unnamed_old = old_productions
            .iter()
            .enumerate()
            .filter(|(index, old)| !paired_old[*index] && old.symbol().is_none())
            .map(|(index, _)| index)
            .collect::<Vec<_>>()
            .into_iter();
        for new in unnamed_new {
            match unnamed_old.next() {
                Some(index) => {
                    paired_old[index] = true;
                    pairs.push((&old_productions[index], new));
                }
                None => inserted.push(new),
            }
        }
        for (old, new) in pairs {
            self.edited(at, old, new, reaches);
        }
        for new in inserted {
            self.inserted(at, new, reaches);
        }
        for (old, _) in old_productions
            .iter()
            .zip(&paired_old)
            .filter(|(_, paired)| !**paired)
        {
            self.parse_change(reaches, || format!("{} (deleted)", old.named()));
        }
    }

    /// Notes a change the program parser reads, when its module is one the parser reads.
    fn parse_change(&mut self, reaches: bool, what: impl FnOnce() -> String) {
        if reaches {
            self.parse_changed = true;
        } else {
            self.unparsed.push(format!(
                "{}, in a module the program grammar does not import",
                what()
            ));
        }
    }

    fn edited(&mut self, at: usize, old: &Declared<'_>, new: &Declared<'_>, reaches: bool) {
        let named = old.named();
        if attributes_in(&old.production.attributes, &NAME_ATTRIBUTES)
            != attributes_in(&new.production.attributes, &NAME_ATTRIBUTES)
        {
            self.refuse(
                at,
                GrammarRefusal::NotJudged(format!(
                    "the edit changes the symbol of {named}, which names the constructor the \
                     rules' terms use; KRS keeps it"
                )),
            );
        }
        let (before, after) = (
            meaning_attributes(&old.production.attributes),
            meaning_attributes(&new.production.attributes),
        );
        if before != after {
            self.refuse(
                at,
                GrammarRefusal::NotJudged(format!(
                    "the edit changes the attributes [{}] of {named} to [{}]: they say what the \
                     constructor means or who sees it, not how a text parses, so the edit is no \
                     grammar mutation",
                    before
                        .iter()
                        .map(|a| attribute_text(a))
                        .collect::<Vec<_>>()
                        .join(", "),
                    after
                        .iter()
                        .map(|a| attribute_text(a))
                        .collect::<Vec<_>>()
                        .join(", ")
                )),
            );
        }
        if old.parse_part() == new.parse_part() {
            self.unparsed
                .push(format!("`format`, `color` or `colors` of {named}"));
        } else {
            self.parse_change(reaches, || named.clone());
            self.check_format(at, new);
        }
    }

    fn inserted(&mut self, at: usize, new: &Declared<'_>, reaches: bool) {
        let named = new.named();
        let meaning = meaning_attributes(&new.production.attributes);
        if !meaning.is_empty() {
            self.refuse(
                at,
                GrammarRefusal::NotJudged(format!(
                    "the inserted {named} has the attributes [{}], which say what a constructor \
                     means or who sees it, not how a text parses; an added alternative carries \
                     only parse, print and name attributes",
                    meaning
                        .iter()
                        .map(|a| attribute_text(a))
                        .collect::<Vec<_>>()
                        .join(", ")
                )),
            );
        }
        self.parse_change(reaches, || format!("{named} (inserted)"));
        self.check_format(at, new);
    }

    /// Refuses a `format` of `declared` that does not reference each of its items once, in
    /// order.
    fn check_format(&mut self, at: usize, declared: &Declared<'_>) {
        let production = declared.production;
        let Some(format) = production
            .attributes
            .iter()
            .find(|attribute| attribute.key == "format")
        else {
            return;
        };
        let text = format.value.as_deref().unwrap_or_default();
        let lists = production
            .items
            .iter()
            .any(|item| matches!(item, ProductionItem::UserList { .. }));
        let count = production.items.len();
        let well_formed = format_references(text).is_some_and(|references| {
            if lists {
                references.iter().all(|&reference| reference <= count)
            } else {
                references == (1..=count).collect::<Vec<_>>()
            }
        });
        if !well_formed {
            let mut derived = String::new();
            for index in 1..=count {
                if index > 1 {
                    derived.push(' ');
                }
                _ = write!(derived, "%{index}");
            }
            self.refuse(
                at,
                GrammarRefusal::MalformedFormat(format!(
                    "the mutant's `format({text})` of {} does not reference each of its {count} \
                     items (`{}`) once, in order; KRS derives a format that does, with any text \
                     or layout controls between the references: write one, such as \
                     `format({derived})`, or leave `format` out",
                    declared.named(),
                    items_text(&production.items)
                )),
            );
        }
    }

    fn finish(mut self) -> Result<(), Vec<Placed>> {
        if self.refusals.is_empty() && !self.parse_changed {
            let mut unparsed = std::mem::take(&mut self.unparsed);
            unparsed.dedup();
            let what = if unparsed.is_empty() {
                "nothing the program parser reads".to_owned()
            } else {
                unparsed.join("; ")
            };
            self.refusals.push((
                self.first.unwrap_or(0),
                GrammarRefusal::NoParseChange(format!(
                    "the edited declarations parse every text as the specification's do: the \
                     edit changes only {what}"
                )),
            ));
        }
        if self.refusals.is_empty() {
            Ok(())
        } else {
            self.refusals.sort_by_key(|(at, _)| *at);
            // A declaration changed on both sides is named once.
            self.refusals.dedup();
            Err(self.refusals)
        }
    }
}

/// The item references of a K `format`, in order; `None` when a `%` introduces nothing K's
/// format language has (`%%`, `%n`, `%i`, `%d`, `%c`, `%r`, a positive position).
fn format_references(text: &str) -> Option<Vec<usize>> {
    let mut references = Vec::new();
    let mut characters = text.chars().peekable();
    while let Some(character) = characters.next() {
        if character != '%' {
            continue;
        }
        match characters.peek().copied() {
            Some('%' | 'n' | 'i' | 'd' | 'c' | 'r') => {
                characters.next();
            }
            Some(digit) if digit.is_ascii_digit() => {
                let mut number = String::new();
                while let Some(digit) = characters.peek().copied().filter(char::is_ascii_digit) {
                    number.push(digit);
                    characters.next();
                }
                let position = number
                    .parse::<usize>()
                    .ok()
                    .filter(|&position| position > 0)?;
                references.push(position);
            }
            _ => return None,
        }
    }
    Some(references)
}

#[cfg(test)]
mod tests {
    use super::{GrammarRefusal, format_references, judge};

    const BASE: &str = r#"module T-SYNTAX
  imports INT-SYNTAX

  syntax Exp
  syntax Exp ::= "count" "(" Int ")" [symbol(count), group(g-a), format(%1%2%3%4), strict]
  syntax Exp ::= Exp "+" Exp [symbol(plus), group(g-b), format(%1 %2 %3)]
  syntax Exp ::= "(" Exp ")" [bracket, format(%1%2%3)]
  syntax priority g-a g-c > g-b
  syntax left g-b
endmodule

module T
  imports T-SYNTAX
  syntax Int ::= "helper" "(" Int ")" [symbol(helper), function]
  rule helper(I:Int) => I
endmodule
"#;

    fn judged(find: &str, replace: &str) -> Result<(), Vec<GrammarRefusal>> {
        assert_eq!(BASE.matches(find).count(), 1, "{find}");
        let mutant = BASE.replace(find, replace);
        judge(BASE, &mutant, "T-SYNTAX")
            .map_err(|refusals| refusals.into_iter().map(|(_, refusal)| refusal).collect())
    }

    fn reason(result: &Result<(), Vec<GrammarRefusal>>) -> Vec<&'static str> {
        result
            .as_ref()
            .err()
            .into_iter()
            .flatten()
            .map(|refusal| match refusal {
                GrammarRefusal::NoParseChange(_) => "no-parse-change",
                GrammarRefusal::MalformedFormat(_) => "derived-mismatch",
                GrammarRefusal::NotJudged(_) => "not-judged",
            })
            .collect()
    }

    #[test]
    fn parse_changes_are_admitted() {
        for (find, replace) in [
            // A literal, a sort, the result sort, a group, a parse attribute.
            (r#""count" "(""#, r#""cnt" "(""#),
            (
                r#""(" Int ")" [symbol(count)"#,
                r#""(" Exp ")" [symbol(count)"#,
            ),
            ("syntax Exp ::= Exp \"+\"", "syntax Int ::= Exp \"+\""),
            ("group(g-b)", "group(g-a)"),
            (
                "[symbol(plus), group(g-b)",
                "[symbol(plus), group(g-b), avoid",
            ),
            ("[bracket, format(%1%2%3)]", "[format(%1%2%3)]"),
            // Relations.
            ("syntax left g-b", "syntax right g-b"),
            ("g-a g-c > g-b", "g-a g-c g-b"),
            ("  syntax left g-b\n", ""),
            // A terminal dropped with its format following, or left out.
            (
                r#""(" Int ")" [symbol(count), group(g-a), format(%1%2%3%4)"#,
                r#""(" Int [symbol(count), group(g-a), format(%1%2 %3)"#,
            ),
            (
                r#""(" Int ")" [symbol(count), group(g-a), format(%1%2%3%4), "#,
                r#""(" Int [symbol(count), group(g-a), "#,
            ),
            // An alternative inserted, with and without a format; a production deleted.
            (
                "  syntax Exp ::= \"(\"",
                "  syntax Exp ::= Exp \"plus\" Exp [group(g-b), format(%1%n%2 %3)]\n  syntax Exp ::= Exp \"minus\" Exp\n  syntax Exp ::= \"(\"",
            ),
            (
                "  syntax Exp ::= \"(\" Exp \")\" [bracket, format(%1%2%3)]\n",
                "",
            ),
        ] {
            assert_eq!(judged(find, replace), Ok(()), "{find} -> {replace}");
        }
    }

    #[test]
    fn what_changes_no_parse_is_refused() {
        for (find, replace) in [
            ("format(%1 %2 %3)", "format(%1%2%3)"),
            ("g-a g-c > g-b", "g-c g-a > g-b"),
            // The function's production is outside the program grammar's modules.
            (r#""helper" "(""#, r#""help" "(""#),
        ] {
            let result = judged(find, replace);
            assert_eq!(reason(&result), ["no-parse-change"], "{find}: {result:?}");
        }
    }

    #[test]
    fn malformed_formats_and_meaning_attributes_are_refused() {
        let result = judged(r#""(" Int ")" [symbol(count)"#, r#""(" Int [symbol(count)"#);
        assert_eq!(reason(&result), ["derived-mismatch"], "{result:?}");
        let Err(refusals) = &result else {
            unreachable!()
        };
        let GrammarRefusal::MalformedFormat(detail) = &refusals[0] else {
            unreachable!()
        };
        assert!(detail.contains("`format(%1 %2 %3)`"), "{detail}");
        for (find, replace) in [
            ("format(%1%2%3%4), strict]", "format(%1%2%3%4)]"),
            (
                "[symbol(plus), group(g-b)",
                "[symbol(plus), group(g-b), private",
            ),
            (
                "  syntax Exp ::= \"(\"",
                "  syntax Exp ::= \"neg\" Exp [strict]\n  syntax Exp ::= \"(\"",
            ),
            ("  syntax Exp\n", "  syntax Exp [token]\n"),
            ("  syntax left g-b\n", "  syntax left g-b\n  rule 1 => 2\n"),
        ] {
            let result = judged(find, replace);
            assert_eq!(reason(&result), ["not-judged"], "{find}: {result:?}");
        }
    }

    #[test]
    fn format_references_read_k_formats() {
        assert_eq!(format_references("%1 %2%3%4"), Some(vec![1, 2, 3, 4]));
        assert_eq!(
            format_references("%1%i%n%2%d%n%3 100%%"),
            Some(vec![1, 2, 3])
        );
        assert_eq!(format_references("%1%x"), None);
        assert_eq!(format_references("%0"), None);
    }
}
