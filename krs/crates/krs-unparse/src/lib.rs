//! Grammar-directed printing of KORE terms, as K 7.1.337 prints them.
//!
//! The printer reads the two artifacts every K compilation writes beside `definition.kore`:
//! `syntaxDefinition.kore`, whose symbol declarations carry each production's `format`,
//! `terminals`, `colors`, priorities and associativities, and `macros.kore`, the macro and alias
//! rules. It is a port, step for step, of the printer `krun --output pretty` runs on an LLVM
//! definition (`kprint` of the LLVM backend 0.1.140 shipped with K 7.1.337):
//!
//! 1. n-ary `\and`/`\or` become binary;
//! 2. aliases are reversed (bottom-up, `macros.kore` order; a non-recursive alias at most once on
//!    one chain, `alias-rec` repeatedly; `macro` and `macro-rec` rules are never reversed);
//! 3. associative-commutative collections are sorted by their printed items (alphanumerically);
//! 4. in [`Mode::Pretty`], equations binding an anonymous variable that occurs nowhere else are
//!    dropped and identical disjuncts printed once;
//! 5. brackets are inserted by K's simple algorithm, injections removed;
//! 6. each application is printed through its `format` (`%N %n %i %d %c %r`, assoc dedent),
//!    with colours as 256-colour ANSI codes when enabled.
//!
//! [`Mode::Pretty`] first rewrites each binary32 and binary64 Float domain value in the form the
//! LLVM runtime prints it, `0.15000000000000000e1` for `1.5`, since a native result carries
//! k-rust's own canonical Float token; [`Unparser::llvm_floats`] does the same for the other
//! output formats.
//!
//! [`Mode::Program`] prints a parsed program as `kast --output program` does: no substitution
//! filtering, and a child that needs brackets in a sort without a bracket production is printed
//! bare.
//!
//! A print is text of a grammar, which reads it back as the term. Where priority, associativity
//! or a sort requires a bracket around a child and no bracket production takes it, no text of
//! the program grammar writes the term, and the print says so: [`Mode::Program`] prints the
//! child bare and warns ([`Warning::Ungrouped`]); [`Mode::Pretty`] groups it in K's default
//! bracket `( .. )` ([`Printed::grouped`]), which a rule's or a claim's grammar reads, and warns
//! where the text is for programs and configuration values ([`Grammar::Value`],
//! [`Warning::Grouped`]).
//!
//! A symbol without a printable production (no `format` in `syntaxDefinition.kore`) is printed as
//! KAST text and reported in [`Printed::warnings`].
//!
//! The crate does no I/O and depends only on k-rust's public KORE and KAST types, so it builds for
//! WebAssembly.

mod abstract_term;
mod alias;
mod brackets;
mod data;
mod float;
mod format;
mod instance;
mod node;
mod program;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust::kore::{
    ast::{Definition, Pattern, Sentence},
    parser::{parse_definition, parse_module},
};

use crate::abstract_term::{
    dedupe_disjuncts, filter_substitution, singleton_vars, sort_collections, unflatten_and_or,
};
use crate::alias::{REVERSAL_BOUND, Reverser};
use crate::brackets::{Brackets, Fallback};
use crate::data::{Macro, PrintData};
use crate::format::{Printer, Problems, ProgramFormats};
use crate::node::{Node, from_pattern, instantiate, to_pattern};

pub use crate::float::llvm_float_text;
pub use crate::format::{decode_kore, enquote, enquote_string};

/// Which K printer to reproduce.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Mode {
    /// `krun --output pretty`: whole configurations, cells, and matching-logic connectives.
    #[default]
    Pretty,
    /// `kast --output program`: a parsed program.
    Program,
}

/// The grammar a [`Mode::Pretty`] print is text of, by what reads it: which brackets its reader
/// has. ([`Mode::Program`] prints program text, which the program grammar reads.)
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Grammar {
    /// The grammars of programs and configuration values (a `krs run` or `krs search` state, a
    /// `-c` value): they have K's default bracket `( .. )` only at `K`, in the ground K-value
    /// grammar a `K` cell is read with. Grouping a child of another sort in it is a stated
    /// fallback ([`Warning::Grouped`]).
    #[default]
    Value,
    /// A rule's or a claim's grammar (a `krs prove` leaf, which a claim states again): K's
    /// default bracket groups every sort.
    Claim,
}

/// Printing options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Options {
    /// Which printer to reproduce.
    pub mode: Mode,
    /// The grammar a [`Mode::Pretty`] print is for.
    pub grammar: Grammar,
    /// Write the productions' colours as ANSI escape codes.
    pub color: bool,
    /// Print each `alias` in reverse, as K always does.
    pub reverse_aliases: bool,
    /// Sort the items of associative-commutative collections (maps, sets) by their printed text, as K always does.
    pub sort_collections: bool,
}

impl Options {
    /// K's defaults for `mode`, without colour.
    #[must_use]
    pub const fn new(mode: Mode) -> Self {
        Self {
            mode,
            grammar: Grammar::Value,
            color: false,
            reverse_aliases: true,
            sort_collections: true,
        }
    }

    /// The same options with colour on or off.
    #[must_use]
    pub const fn with_color(mut self, color: bool) -> Self {
        self.color = color;
        self
    }

    /// The same options for text of `grammar`.
    #[must_use]
    pub const fn for_grammar(mut self, grammar: Grammar) -> Self {
        self.grammar = grammar;
        self
    }
}

impl Default for Options {
    fn default() -> Self {
        Self::new(Mode::Pretty)
    }
}

/// A problem found while printing; the output degrades instead of failing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Warning {
    /// Symbols without a printable production, printed as KAST text.
    Unprintable(Vec<String>),
    /// A `colors` list shorter than the production's terminals and `%c` codes.
    ShortColors(Vec<String>),
    /// A format that names an argument its symbol does not have, or ends in `%`.
    InvalidFormat(Vec<String>),
    /// An `alias-rec` reversal that did not reach a fixed point within the bound.
    ReversalBound(String),
    /// A format that names a regex terminal of its production.
    RegexTerminal(Vec<String>),
    /// Applications of parametric productions whose instance their text does not fix: printed,
    /// each would read back at another instance, so each is printed as its KORE pattern.
    Instance(Vec<String>),
    /// [`Mode::Program`]: children of these sorts (K names) need a bracket that no bracket
    /// production of the definition gives, and are printed bare, which the program grammar does
    /// not read as the term.
    Ungrouped(Vec<String>),
    /// [`Mode::Pretty`] for [`Grammar::Value`]: children of these sorts (K names, `K` aside) are
    /// grouped in K's default bracket `( .. )`, which neither a program nor a configuration value
    /// reads.
    Grouped(Vec<String>),
}

fn sorts(names: &[String]) -> String {
    names
        .iter()
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn labels(symbols: &[String]) -> String {
    symbols
        .iter()
        .map(|symbol| format!("`{}`", label_name(symbol)))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The K label of a KORE symbol name (`Lbl'Unds'Map'Unds'` is `_Map_`).
#[must_use]
pub fn label_name(symbol: &str) -> String {
    decode_kore(symbol.strip_prefix("Lbl").unwrap_or(symbol))
}

impl fmt::Display for Warning {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unprintable(symbols) => write!(
                formatter,
                "no production can print {}; printed as KAST",
                labels(symbols)
            ),
            Self::ShortColors(symbols) => write!(
                formatter,
                "Invalid colors attribute. Must be a comma separated list with exactly one element per terminal ({})",
                labels(symbols)
            ),
            Self::InvalidFormat(symbols) => write!(
                formatter,
                "Invalid format attribute; index must be in range 1-N for a production with N items ({})",
                labels(symbols)
            ),
            Self::RegexTerminal(symbols) => write!(
                formatter,
                "Cannot currently format productions with regex terminals which are not tokens ({})",
                labels(symbols)
            ),
            Self::Instance(symbols) => write!(
                formatter,
                "no program text fixes the instance of {}, which would read back at another; printed as KORE",
                labels(symbols)
            ),
            Self::Ungrouped(names) => write!(
                formatter,
                "priority, associativity or a sort requires a bracket around a child of sort {}, and the definition declares no bracket that takes it: printed bare, which a program reads as another term or none",
                sorts(names)
            ),
            Self::Grouped(names) => write!(
                formatter,
                "priority, associativity or a sort requires a bracket around a child of sort {}, and the definition declares no bracket that takes it: grouped in K's default bracket `( .. )`, which a rule or a claim reads and neither a program nor a configuration value does",
                sorts(names)
            ),
            Self::ReversalBound(symbol) => write!(
                formatter,
                "reversing the aliases of `{}` did not finish within {REVERSAL_BOUND} applications; printed unreversed",
                label_name(symbol)
            ),
        }
    }
}

/// Printed text and the problems found while printing it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Printed {
    /// The text, without a trailing newline.
    pub text: String,
    /// Problems, in a fixed order.
    pub warnings: Vec<Warning>,
    /// The sorts (K names, in order) of the children printed in K's default bracket `( .. )`
    /// (`{Sort} Sort ::= "(" Sort ")"`, which K declares in `KSEQ`): where priority,
    /// associativity or a sort requires a bracket around a child and the definition declares
    /// none that takes it. A rule's or a claim's grammar reads it; the program grammar and the
    /// main module's value grammar (`-c` values, cell expectations) have no such bracket (the
    /// ground K-value grammar of a `K` cell has it at `K` only), so for them the text does not
    /// read back ([`Warning::Grouped`], for [`Grammar::Value`]). A map whose key is a map
    /// (`( 1 |-> 2 ) |-> 3`) has no other text there: `_|->_` is non-associative, ranks above
    /// `.Map` and `_Map_`, and no bracket groups a map.
    pub grouped: Vec<String>,
}

/// An alias clause a printer reverses ([`Unparser::reversed_clauses`]).
#[derive(Clone, Debug, PartialEq)]
pub struct ReversedClause {
    /// The rule's `label`.
    pub label: Option<String>,
    /// The tokens its left-hand side writes, which a reversal prints as they are.
    pub tokens: Vec<SubjectToken>,
    /// The KORE names of the symbols its left-hand side applies, its own head included, which a
    /// reversal prints: every application but a domain value, an injection (printed as its
    /// argument) and a conjunction (the subject's `#as`, printed as its term).
    pub symbols: BTreeSet<String>,
}

/// A token an alias clause's left-hand side writes.
#[derive(Clone, Debug, PartialEq)]
pub struct SubjectToken {
    /// The sort of the position it stands at: the target of the injection around it, or its own.
    pub position: k_rust::kore::ast::Sort,
    /// The token, `\dv{S}("..")`.
    pub token: Pattern,
    /// The token as this printer writes it.
    pub printed: String,
}

/// The tokens below `node` with the sort of the position each stands at, `position` being the
/// target of the injection `node` stands under, if any.
fn subject_tokens<'n>(
    node: &'n Node,
    position: Option<&'n k_rust::kore::ast::Sort>,
    found: &mut Vec<(&'n k_rust::kore::ast::Sort, &'n Node)>,
) {
    let Node::App(app) = node else {
        return;
    };
    if app.sym.name == "\\dv" {
        if let Some(sort) = position.or_else(|| app.sym.formals.first()) {
            found.push((sort, node));
        }
        return;
    }
    // A conjunction's conjuncts stand at its position; an injection's argument at its target.
    let inner = match app.sym.name.as_str() {
        "\\and" => position,
        "inj" => app.sym.formals.get(1),
        _ => None,
    };
    for argument in &app.args {
        subject_tokens(argument, inner, found);
    }
}

/// The KORE names of the symbols `node` applies, but domain values, injections and
/// conjunctions, which a reversal does not print as applications of their own.
fn subject_symbols(node: &Node, found: &mut BTreeSet<String>) {
    let Node::App(app) = node else {
        return;
    };
    if app.sym.name == "\\dv" {
        return;
    }
    if !matches!(app.sym.name.as_str(), "\\and" | "inj") {
        found.insert(app.sym.name.clone());
    }
    for argument in &app.args {
        subject_symbols(argument, found);
    }
}

/// A failure to build an [`Unparser`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnparseError(String);

impl fmt::Display for UnparseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for UnparseError {}

/// The printer of one compiled definition.
#[derive(Clone, Debug)]
pub struct Unparser {
    data: PrintData,
    macros: Vec<Macro>,
    program: ProgramFormats,
}

impl Unparser {
    /// Build the printer from the parsed `syntaxDefinition.kore` and the sentences of `macros.kore`.
    #[must_use]
    pub fn new(syntax_definition: &Definition, macros: &[Sentence]) -> Self {
        let sentences = syntax_definition
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .collect::<Vec<_>>();
        let data = PrintData::new(&sentences);
        let macros = data.macros(&macros.iter().collect::<Vec<_>>());
        Self {
            data,
            macros,
            program: ProgramFormats::new(),
        }
    }

    /// Read the authored formats [`Mode::Program`] prints with from the frontend definition the program grammar was built from.
    #[must_use]
    pub fn with_program_grammar(mut self, frontend: &k_rust::definition::Definition) -> Self {
        self.program = program::program_productions(frontend);
        self
    }

    /// This printer with only the macro axioms whose left-hand side's head symbol (its KORE name,
    /// `LblcmdAz`) `keep` admits, and every axiom whose left-hand side is no application: the
    /// printer of a definition without the other axioms' productions' clauses.
    #[must_use]
    pub fn retaining_aliases(&self, keep: impl Fn(&str) -> bool) -> Self {
        let mut printer = self.clone();
        printer.macros.retain(|rule| {
            rule.left
                .as_app()
                .is_none_or(|app| keep(app.sym.name.as_str()))
        });
        printer
    }

    /// The alias clauses this printer reverses, in `macros.kore` order: each `alias` or
    /// `alias-rec` axiom whose right-hand side is an application.
    #[must_use]
    pub fn reversed_clauses(&self) -> Vec<ReversedClause> {
        self.macros
            .iter()
            .filter(|rule| rule.reversible())
            .map(|rule| {
                let mut tokens = Vec::new();
                subject_tokens(&rule.left, None, &mut tokens);
                let mut symbols = BTreeSet::new();
                subject_symbols(&rule.left, &mut symbols);
                ReversedClause {
                    label: rule.label.clone(),
                    symbols,
                    tokens: tokens
                        .into_iter()
                        .filter_map(|(position, token)| {
                            let pattern = to_pattern(token)?;
                            // A reversal writes the subject's token as the axiom holds it, after
                            // a run's floats are converted to the runtime's form, so the token
                            // is printed without that conversion, which only `Mode::Pretty`
                            // makes: `1.5`, not `0.15000000000000000e1`.
                            let printed = self
                                .print_kore(
                                    &pattern,
                                    &Options {
                                        reverse_aliases: false,
                                        mode: Mode::Program,
                                        ..Options::default()
                                    },
                                )
                                .text;
                            Some(SubjectToken {
                                position: position.clone(),
                                token: pattern,
                                printed,
                            })
                        })
                        .collect(),
                }
            })
            .collect()
    }

    /// This printer reversing only the alias clauses whose `label` `reversed` admits: every other
    /// axiom, one without a label included, still expands where a program or a rule writes it,
    /// but a printed term is never written through it.
    #[must_use]
    pub fn reversing_only(&self, reversed: impl Fn(&str) -> bool) -> Self {
        let mut printer = self.clone();
        for rule in &mut printer.macros {
            rule.forward_only = !rule.label.as_deref().is_some_and(&reversed);
        }
        printer
    }

    /// This printer reversing every `alias` and `alias-rec` axiom whose right-hand side is an
    /// application, as [`Unparser::from_kore`] builds it: what [`Unparser::reversing_only`] kept
    /// forward only is reversed again.
    #[must_use]
    pub fn reversing_every_alias(&self) -> Self {
        let mut printer = self.clone();
        for rule in &mut printer.macros {
            rule.forward_only = false;
        }
        printer
    }

    /// The labels of the axioms of `macros.kore`, each the clause it was emitted from.
    #[must_use]
    pub fn clause_labels(&self) -> BTreeSet<&str> {
        self.macros
            .iter()
            .filter_map(|rule| rule.label.as_deref())
            .collect()
    }

    /// The declared argument sorts of the symbol `name` (its KORE name), as `syntaxDefinition.kore`
    /// declares them; `None` for a symbol it does not declare.
    #[must_use]
    pub fn argument_sorts(&self, name: &str) -> Option<&[k_rust::kore::ast::Sort]> {
        self.data
            .declarations
            .get(name)
            .map(|declaration| declaration.arguments.as_slice())
    }

    /// Build the printer from the text of `syntaxDefinition.kore` and `macros.kore`.
    ///
    /// # Errors
    ///
    /// Returns an error when either text is not KORE.
    pub fn from_kore(syntax_definition: &str, macros: &str) -> Result<Self, UnparseError> {
        let definition = parse_definition(syntax_definition)
            .map_err(|error| UnparseError(format!("syntaxDefinition.kore: {error}")))?;
        let macros = parse_module(&format!(
            "module KRS-UNPARSE-MACROS\n{macros}\nendmodule []"
        ))
        .map_err(|error| UnparseError(format!("macros.kore: {error}")))?;
        Ok(Self::new(&definition, &macros.sentences))
    }

    /// `pattern`, a result of the definition, with each binary32 and binary64 Float domain
    /// value in the form K's LLVM runtime prints it (`0.15000000000000000e1` for k-rust's
    /// `1.5000000000000000e+00p53x11`), as every `krun` output format shows it; `None` when no
    /// domain value changes.
    #[must_use]
    pub fn llvm_floats(&self, pattern: &Pattern) -> Option<Pattern> {
        float::llvm_floats(&self.data, pattern)
    }

    /// Print a KORE pattern.
    #[must_use]
    pub fn print_kore(&self, pattern: &Pattern, options: &Options) -> Printed {
        let mut problems = Problems::default();
        // The LLVM runtime prints every Float it returns in MPFR's form, before kprint reverses
        // aliases.
        let floats = (options.mode == Mode::Pretty)
            .then(|| self.llvm_floats(pattern))
            .flatten();
        let pattern = floats.as_ref().unwrap_or(pattern);
        let mut node = unflatten_and_or(&from_pattern(pattern));
        instantiate(&mut node, &self.data.declarations);
        let mut exceeded = None;
        if options.reverse_aliases {
            let mut reverser = Reverser::new(&self.data, &self.macros);
            node = reverser.expand(&node);
            exceeded = reverser.exceeded;
        }
        let sort = |node: &Node, problems: &mut Problems| {
            if options.sort_collections {
                sort_collections(&self.data, node, problems)
            } else {
                node.clone()
            }
        };
        node = sort(&node, &mut problems);
        let fallback = match options.mode {
            Mode::Pretty => {
                let vars = singleton_vars(&node);
                node = filter_substitution(&self.data, &node, &vars, &mut problems);
                node = dedupe_disjuncts(&node);
                node = sort(&node, &mut problems);
                Fallback::Parentheses
            }
            Mode::Program => Fallback::Nothing,
        };
        // An instance is judged on the tree as it prints, after reversal has moved or built
        // applications, and after the collections are sorted by their elements' terms.
        instantiate(&mut node, &self.data.declarations);
        let mut unfixed = BTreeSet::new();
        instance::fix_instances(&self.data, &mut node, &mut unfixed);
        let brackets = Brackets::new(&self.data, fallback);
        node = brackets.add(&node, None, None);
        let unbracketed = brackets.unbracketed();
        // Keys printed while sorting are not output: only the final pass reports.
        let mut problems = Problems::default();
        let mut printer = Printer::new(&self.data, options.color, &mut problems);
        if options.mode == Mode::Program {
            printer = printer.with_program(&self.program);
        }
        printer.print(&node);
        let text = printer.finish();
        let mut warnings = Vec::new();
        let list =
            |set: &std::collections::BTreeSet<String>| set.iter().cloned().collect::<Vec<_>>();
        if !problems.unprintable.is_empty() {
            warnings.push(Warning::Unprintable(list(&problems.unprintable)));
        }
        if !problems.short_colors.is_empty() {
            warnings.push(Warning::ShortColors(list(&problems.short_colors)));
        }
        if !problems.bad_formats.is_empty() {
            warnings.push(Warning::InvalidFormat(list(&problems.bad_formats)));
        }
        if !problems.regex_formats.is_empty() {
            warnings.push(Warning::RegexTerminal(list(&problems.regex_formats)));
        }
        if let Some(symbol) = exceeded {
            warnings.push(Warning::ReversalBound(symbol));
        }
        if !unfixed.is_empty() {
            warnings.push(Warning::Instance(list(&unfixed)));
        }
        let grouped = match fallback {
            Fallback::Nothing => {
                if !unbracketed.is_empty() {
                    warnings.push(Warning::Ungrouped(list(&unbracketed)));
                }
                Vec::new()
            }
            Fallback::Parentheses => {
                // The ground K-value grammar of a `K` cell has the bracket at `K`.
                let unread = unbracketed
                    .iter()
                    .filter(|sort| *sort != "K")
                    .cloned()
                    .collect::<Vec<_>>();
                if options.grammar == Grammar::Value && !unread.is_empty() {
                    warnings.push(Warning::Grouped(unread));
                }
                list(&unbracketed)
            }
        };
        Printed {
            text,
            warnings,
            grouped,
        }
    }
}

/// The KAST text of a node, or its KORE text when it has no KAST form. `hooks` are the
/// definition's sort hooks by KORE sort name, by which a domain value's token is rendered.
pub(crate) fn kast_text(node: &Node, hooks: &BTreeMap<String, String>) -> String {
    let Some(pattern) = to_pattern(node) else {
        return node.key();
    };
    let hooks = k_rust::kast::convert::sort_hooks(
        hooks
            .iter()
            .map(|(sort, hook)| (sort.as_str(), hook.as_str())),
    );
    match k_rust::kast::convert::Converter::new(&hooks).convert(&pattern) {
        Ok(term) => k_rust::kast::printer::Printer::new().print_term(&term),
        Err(_) => pattern.to_string(),
    }
}

#[cfg(test)]
mod tests;
