//! The K-text syntax of one definition: printing collection and data-sort values as program text
//! with krs-unparse, and reading program text back as the KORE the configuration assembler builds
//! (ARCHITECTURE 2.3, 2.6, G-6). Owner: FZ-G6.
//!
//! A [`TextSyntax`] is built once per campaign from the baseline's compiled definition and shared
//! by every [`super::ValueSort`] resolved with it ([`TextSyntax::resolve`]), so that
//! [`super::print::print_k_text`] and [`super::print::parse_k_text`] keep their definition-free
//! signatures.
//!
//! Printing goes through krs-unparse's [`Mode::Program`], the printer of parsed programs: each
//! constructor is printed through its production (terminals in place, arguments in order),
//! injections are dropped, and brackets are added where the grammar's priorities and
//! associativities need them and the sort has a bracket production. Alias reversal and the
//! sorting of associative-commutative collections are off, so the text lists a collection's
//! items in the value's own order, and the KORE of the value ([`super::print::to_kore`]) is the
//! KORE the text parses back to. The layout newlines the productions' formats ask for are
//! replaced by spaces: K text separates tokens by any whitespace, and every newline inside a
//! literal is escaped, so the text is one line that a span hole can replace in place.
//!
//! Reading follows the assembler's path for a configuration value: the program parser of the
//! main module at the hole's sort, macro expansion in the main module, sort injection at the
//! hole's sort, and conversion to KORE with the main module's lexical hooks.

use std::{
    collections::BTreeSet,
    fmt,
    sync::{Arc, OnceLock},
};

use k_rust::{
    definition::Definition,
    inner::ProgramParser,
    k_rust_backend::definition::BackendDefinition,
    kast::{Sort as KastSort, parser::parse_sort},
    kompile::{
        MacroExpansionDefinition, ProgramGrammar, SortInjector, encode_kore_sort,
        term_to_kore_from_resolved_with_token_module,
    },
    kore::ast::{Pattern as KorePattern, Sort as KoreSort},
};
use krs_unparse::{Mode, Options, Unparser};

use super::{Constraints, ValueSort, resolve_with};
use crate::error::SortRefusal;

/// Sorts no data table enters whatever the caller excludes: computations and K's internal sorts,
/// which the hole-sort rule refuses (FZ-02, `holes/sorts.rs`).
const ALWAYS_EXCLUDED: [&str; 5] = ["K", "KItem", "KResult", "KBott", "KConfigVar"];

/// Whether the sort whose KORE name is `name` is one of [`ALWAYS_EXCLUDED`].
pub(super) fn is_always_excluded(name: &str) -> bool {
    name.strip_prefix("Sort")
        .is_some_and(|name| ALWAYS_EXCLUDED.contains(&name))
}

/// The K-text syntax of one definition (see the module documentation). Cloning shares it.
#[derive(Clone)]
pub struct TextSyntax(Arc<Inner>);

struct Inner {
    unparser: Unparser,
    grammar: ProgramGrammar,
    macros: MacroExpansionDefinition,
    /// The main module's program parser, built on first use.
    parser: OnceLock<Result<ProgramParser, String>>,
    main_module: String,
    /// KORE names of sorts whose values are not data: a data table never enters them.
    excluded: BTreeSet<String>,
}

impl fmt::Debug for TextSyntax {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TextSyntax")
            .field("main_module", &self.0.main_module)
            .field("excluded", &self.0.excluded)
            .finish_non_exhaustive()
    }
}

/// Two value sorts are equal when they admit the same values: the syntax they carry is the
/// definition's, and does not take part in the comparison.
impl PartialEq for TextSyntax {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for TextSyntax {}

impl TextSyntax {
    /// The syntax of a compiled definition: `frontend` is the loaded source definition the
    /// program grammar is built from (`CompiledDefinition::frontend_definition`), `main_module`
    /// the module values are read in, and `syntax_definition_kore` and `macros_kore` the
    /// compiler's `syntaxDefinition.kore` and `macros.kore`
    /// (`CompiledKoreArtifacts::{syntax_definition_kore, macros_kore}`), from which krs-unparse
    /// reads each production's format.
    ///
    /// `excluded` names the sorts (K names, such as `Stmt`) whose values are not data and that a
    /// data-sort table must not enter even as a constructor's argument: the sorts of the program
    /// syntax closure and the cell sorts of the hole-sort rule (ARCHITECTURE 2.4). Only data
    /// sorts are affected: a builtin or collection sort in `excluded` (the program grammar
    /// mentions `Int`) is still generated, since ARCHITECTURE 2.4 exempts builtins. `K`,
    /// `KItem` and K's internal sorts (`KResult`, `KBott`, `KConfigVar`) are always excluded.
    ///
    /// # Errors
    ///
    /// A message when either KORE text does not parse, the frontend definition has no program
    /// grammar, or its macros cannot be prepared.
    pub fn new(
        frontend: &Definition,
        main_module: &str,
        syntax_definition_kore: &str,
        macros_kore: &str,
        excluded: impl IntoIterator<Item = String>,
    ) -> Result<Self, String> {
        let unparser = Unparser::from_kore(syntax_definition_kore, macros_kore)
            .map_err(|error| error.to_string())?
            .with_program_grammar(frontend);
        let grammar = ProgramGrammar::new(frontend).map_err(|error| error.to_string())?;
        let macros = MacroExpansionDefinition::prepare(grammar.definition())?;
        let mut names = excluded.into_iter().collect::<BTreeSet<_>>();
        names.extend(ALWAYS_EXCLUDED.map(str::to_owned));
        let excluded = names
            .iter()
            .map(|name| {
                let sort = parse_sort(name).map_err(|error| format!("sort `{name}`: {error}"))?;
                match &encode_kore_sort(&sort) {
                    KoreSort::Application { name, .. } | KoreSort::Variable(name) => {
                        Ok(name.clone())
                    }
                }
            })
            .collect::<Result<BTreeSet<_>, String>>()?;
        Ok(Self(Arc::new(Inner {
            unparser,
            grammar,
            macros,
            parser: OnceLock::new(),
            main_module: main_module.to_owned(),
            excluded,
        })))
    }

    /// Whether the sort whose KORE name is `name` is excluded from data tables.
    pub(crate) fn is_excluded(&self, name: &str) -> bool {
        self.0.excluded.contains(name)
    }

    /// Resolve a hole's sort as [`super::resolve_value_sort`] does, with this syntax attached to
    /// collection and data sorts (so that their values print and read back as K text) and the
    /// excluded sorts left out of data tables. A data hole of an excluded sort is refused with
    /// [`SortRefusal::Computation`] (`K`, `KItem`) or [`SortRefusal::ProgramSyntax`].
    ///
    /// # Errors
    ///
    /// The refusals of [`super::resolve_value_sort`].
    pub fn resolve(
        &self,
        sort: &str,
        constraints: &Constraints,
        definition: &BackendDefinition,
    ) -> Result<ValueSort, SortRefusal> {
        resolve_with(sort, constraints, definition, Some(self))
    }

    /// `pattern`, a value at its own sort below the sort whose K name is `sort`, as one line of
    /// K program text (see the module documentation), checked by reading it back: the text is
    /// returned only when [`Self::parse`] at `sort` gives `pattern` again.
    ///
    /// # Errors
    ///
    /// The unparser's warnings, when a symbol has no printable production or a format is
    /// invalid; and a message when the text reads back as another term or does not read back,
    /// which happens when the grammar cannot tell the term from another (a nested infix term of
    /// a sort without a bracket production, an overloaded constructor whose more specific
    /// overload the parser prefers, two productions with the same syntax). Never a wrong text.
    pub(crate) fn print(&self, pattern: &KorePattern, sort: &str) -> Result<String, String> {
        let options = Options {
            mode: Mode::Program,
            color: false,
            reverse_aliases: false,
            sort_collections: false,
        };
        let printed = self.0.unparser.print_kore(pattern, &options);
        if !printed.warnings.is_empty() {
            let warnings = printed
                .warnings
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            return Err(warnings.join("; "));
        }
        let text = one_line(&printed.text);
        match self.parse(&text, sort) {
            Ok(read) if read == *pattern => Ok(text),
            Ok(_) => Err(format!(
                "`{text}` reads back at {sort} as another term: the grammar does not tell the \
                 value apart"
            )),
            Err(error) => Err(format!("`{text}` does not read back at {sort}: {error}")),
        }
    }

    /// `text` read at the sort whose K name is `sort`, as the configuration assembler reads a
    /// configuration value of that sort: parsed in the main module, macro-expanded, injected at
    /// the sort, and converted to KORE. The injection to `sort` around the whole value is
    /// removed: the result is the value at its own sort, as [`super::print::to_kore`] gives it,
    /// since the assembler replaces that injection by the one the value's position needs.
    ///
    /// # Errors
    ///
    /// A message when the text does not parse at the sort or cannot be placed there.
    pub(crate) fn parse(&self, text: &str, sort: &str) -> Result<KorePattern, String> {
        let inner = &*self.0;
        let sort: KastSort = parse_sort(sort).map_err(|error| error.to_string())?;
        let resolved = inner.grammar.resolved();
        let parser = inner
            .parser
            .get_or_init(|| {
                ProgramParser::from_resolved(resolved, &inner.main_module)
                    .map_err(|error| format!("{error:?}"))
            })
            .as_ref()
            .map_err(Clone::clone)?;
        let parsed = parser
            .parse(&sort, text)
            .map_err(|error| format!("`{text}` does not parse at {sort}: {error:?}"))?;
        let expanded = inner
            .macros
            .expand_program(&inner.main_module, parsed, &sort)?;
        let injector = SortInjector::new(resolved, &inner.main_module)
            .map_err(|error| format!("{error:?}"))?;
        let term = injector
            .inject(expanded.term(), &sort)
            .map_err(|error| format!("`{text}` cannot be placed at {sort}: {error:?}"))?;
        let mut pattern = term_to_kore_from_resolved_with_token_module(
            resolved,
            &inner.main_module,
            &inner.main_module,
            &term,
        )
        .map_err(|error| format!("{error:?}"))?;
        while let KorePattern::Application { symbol, arguments } = &pattern
            && symbol.name == "inj"
            && arguments.len() == 1
        {
            let inner = arguments[0].clone();
            pattern = inner;
        }
        Ok(pattern)
    }
}

/// `text` with each newline and the indentation after it replaced by one space.
fn one_line(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let mut lines = text.split('\n');
    if let Some(first) = lines.next() {
        output.push_str(first.trim_end());
    }
    for line in lines {
        let line = line.trim();
        if !line.is_empty() {
            output.push(' ');
            output.push_str(line);
        }
    }
    output
}
