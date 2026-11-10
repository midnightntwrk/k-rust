//! The initial configuration of a compiled definition: `$PGM`, configuration variables parsed
//! with their cell's parser module, `$IO`/`$STDIN` stream defaults, and the
//! `initGeneratedTopCell` application.
//!
//! [`ConfigurationAssembler`] composes these steps. The bindings it collects and the builder of
//! the application are private to the crate, so every `$X` entry it emits comes from a
//! macro-expanded value or a stream default: an embedder cannot place an unexpanded program in
//! the configuration map.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::OnceLock,
};

use crate::{
    definition::{AttributeKey, Definition, ResolveError, ResolvedDefinition, Sentence},
    inner::{
        LOCATION_LABEL, ParsedProgram, ProgramError, ProgramParseError, ProgramParser,
        UNNAMED_PROGRAM, definition_with_named_projections,
    },
    kast::{Sort as KastSort, Term, WellKnownModule},
    kompile::{
        ExpandedProgram, MacroExpansionDefinition, ProgramExpansion, SortInjectionError,
        SortInjector, TermConversionError, term_to_kore_from_resolved_with_token_module,
    },
    kore::ast::{KoreString, Pattern, Sort, Symbol},
    names::BuiltinSort,
};

/// One `$X` entry of `initGeneratedTopCell`: its name and normalized K payload.
///
/// The value is built only from a macro-expanded program or configuration value
/// ([`ConfigurationAssembler::program`], [`ConfigurationAssembler::bind`]) or a stream default
/// ([`stream_defaults`]).
#[derive(Debug)]
pub(crate) struct ConfigurationBinding {
    name: String,
    value: ConfigurationValue,
}

/// The grammar that concrete inputs to a compiled definition are parsed and converted against.
///
/// It is the frontend definition extended with the named-field projection productions of every
/// production ([`definition_with_named_projections`]): a program or configuration value may apply
/// such a projection, and that application needs a production for sort injection and KORE
/// conversion. The resolution is exposed so that other consumers of the same grammar, such as a
/// search-pattern compiler, share it instead of resolving the definition again.
///
/// The macro-expansion definition of the grammar is prepared on first use and kept, so every
/// assembler of the grammar shares it.
pub struct ProgramGrammar {
    definition: Definition,
    resolved: ResolvedDefinition,
    macro_definition: OnceLock<Result<MacroExpansionDefinition, String>>,
}

impl ProgramGrammar {
    pub fn new(frontend: &Definition) -> Result<Self, ConfigurationError> {
        let definition = definition_with_named_projections(frontend);
        let resolved =
            ResolvedDefinition::resolve(&definition).map_err(ConfigurationError::Definition)?;
        Ok(Self {
            definition,
            resolved,
            macro_definition: OnceLock::new(),
        })
    }

    pub fn definition(&self) -> &Definition {
        &self.definition
    }

    pub fn resolved(&self) -> &ResolvedDefinition {
        &self.resolved
    }

    /// The definition that programs and configuration values of this grammar are
    /// macro-expanded against ([`MacroExpansionDefinition::prepare`] of [`Self::definition`]),
    /// prepared on first use. It depends on the grammar alone, so a failure is kept and
    /// returned again.
    pub fn macro_definition(&self) -> Result<&MacroExpansionDefinition, String> {
        self.macro_definition
            .get_or_init(|| MacroExpansionDefinition::prepare(&self.definition))
            .as_ref()
            .map_err(Clone::clone)
    }
}

/// Why an initial configuration could not be assembled.
///
/// The messages name configuration variables with their `$` and say nothing about how a caller
/// collected its inputs; a command-line front end adds its own hints.
#[derive(Debug)]
#[non_exhaustive]
pub enum ConfigurationError {
    /// A configuration variable name that is empty after its optional `$`.
    EmptyName,
    /// `$PGM` given as a configuration variable; the program binds it.
    ProgramVariable,
    /// A variable, `$PGM` included, bound twice in one configuration.
    Duplicate {
        name: String,
    },
    /// A variable the definition does not declare. `available` lists the declared variables
    /// other than `$PGM`, each with its `$`.
    UnknownVariable {
        name: String,
        available: Vec<String>,
    },
    /// Declared variables, each with its `$`, that `finish` found unbound: `$PGM` first when
    /// the definition declares it, then the others in name order.
    Missing {
        names: Vec<String>,
    },
    /// The module named by a cell's parser attribute, or `STRING-SYNTAX` for a stream variable,
    /// is not part of the definition.
    ParserModuleNotFound {
        variable: String,
        module: String,
    },
    /// A configuration value that does not parse at its declared sort. `error` is the failure of
    /// the last grammar tried; where the variable was read with the syntax module's grammar first
    /// ([`variable_reading_modules`]), `syntax_attempt` is that grammar's failure and `error` the
    /// main module's.
    Parse {
        variable: String,
        sort: KastSort,
        error: Box<ProgramParseError>,
        syntax_attempt: Option<Box<ProgramParseError>>,
    },
    /// The program text does not parse at the requested start sort.
    Program(ProgramParseError),
    /// A malformed cell `parser` attribute.
    ParserAttribute(String),
    Parser(ProgramError),
    MacroExpansion(String),
    /// A ground value whose label instance the parsed sort and arguments do not determine.
    UndeterminedInstance {
        variable: String,
        error: Box<SortInjectionError>,
    },
    SortInjection(SortInjectionError),
    /// A value holding a located term while the main module's view does not declare `#location`.
    UnlocatableTerm(Box<UnlocatableTerm>),
    Conversion(TermConversionError),
    Definition(ResolveError),
    Unplaceable {
        variable: String,
        sort: KastSort,
    },
    /// A value bound without the parser ([`ConfigurationAssembler::bind_term`]) whose sort is
    /// not at most the variable's declared sort.
    ValueSort(Box<ValueSortMismatch>),
}

/// A value bound without the parser whose sort is not at most its variable's declared sort.
#[derive(Debug)]
pub struct ValueSortMismatch {
    /// The variable, with its `$`.
    pub variable: String,
    /// The variable's declared sort.
    pub declared: KastSort,
    /// The value's sort.
    pub actual: KastSort,
}

impl fmt::Display for ConfigurationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyName => f.write_str("configuration variable name cannot be empty"),
            Self::ProgramVariable => f.write_str(
                "$PGM is supplied by the program and cannot be bound as a configuration variable",
            ),
            Self::Duplicate { name } => {
                write!(
                    f,
                    "configuration variable `${name}` was provided more than once"
                )
            }
            Self::UnknownVariable { name, available } if available.is_empty() => {
                write!(f, "definition has no configuration variable `${name}`")
            }
            Self::UnknownVariable { name, available } => write!(
                f,
                "definition has no configuration variable `${name}`; available variables: {}",
                available.join(", ")
            ),
            Self::Missing { names } => write!(
                f,
                "missing required configuration variable{} {}",
                if names.len() == 1 { "" } else { "s" },
                names.join(", ")
            ),
            Self::ParserModuleNotFound { variable, module } => write!(
                f,
                "parser module `{module}` for configuration variable `${variable}` was not found"
            ),
            Self::Parse {
                variable,
                sort,
                error,
                syntax_attempt: None,
            } => write!(
                f,
                "could not parse configuration variable `${variable}` at sort {sort}: {error}"
            ),
            Self::Parse {
                variable,
                sort,
                error,
                syntax_attempt: Some(syntax_attempt),
            } => write!(
                f,
                "could not parse configuration variable `${variable}` at sort {sort}: syntax \
                 module attempt: {syntax_attempt}; main module attempt: {error}"
            ),
            Self::Program(error) => error.fmt(f),
            Self::ParserAttribute(message) | Self::MacroExpansion(message) => f.write_str(message),
            Self::Parser(error) => error.fmt(f),
            Self::UndeterminedInstance { variable, error } => write!(
                f,
                "configuration variable `{variable}` has an undetermined instance: {error}"
            ),
            Self::SortInjection(error) => error.fmt(f),
            Self::UnlocatableTerm(error) => error.fmt(f),
            Self::Conversion(error) => error.fmt(f),
            Self::Definition(error) => error.fmt(f),
            Self::Unplaceable { variable, sort } => write!(
                f,
                "configuration variable `{variable}` has actual sort {sort}, which cannot be placed at K"
            ),
            Self::ValueSort(mismatch) => {
                let ValueSortMismatch {
                    variable,
                    declared,
                    actual,
                } = mismatch.as_ref();
                write!(
                    f,
                    "configuration variable `{variable}` is declared at sort {declared}, but its value has sort {actual}"
                )
            }
        }
    }
}

impl std::error::Error for ConfigurationError {}

/// A configuration value holding a located term, `#location{sort}(t, file, ...)` for a sort that
/// declares `[locations]`, while the main module's view does not declare `#location`, so the value
/// is not a term of the definition.
#[derive(Debug)]
pub struct UnlocatableTerm {
    /// The configuration variable the value is for, `$PGM` for the program.
    pub variable: String,
    /// The sort the first located term (outermost, leftmost) is located at.
    pub sort: KastSort,
    /// Where that term's text is, `file:line:column-line:column`.
    pub place: String,
    pub main_module: String,
}

impl fmt::Display for UnlocatableTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            variable,
            sort,
            place,
            main_module,
        } = self;
        let locations = WellKnownModule::Locations.as_str();
        write!(
            f,
            "{place}: the value of `{variable}` holds a term of sort {sort}, which declares 'locations', so it is the located term #location{{{sort}}}(...); #location is declared by module {locations}, which the main module {main_module} does not import, so the value is not a term of this definition. Add `imports {locations}` to {main_module} to run it."
        )
    }
}

impl From<ProgramError> for ConfigurationError {
    fn from(error: ProgramError) -> Self {
        Self::Parser(error)
    }
}

impl From<SortInjectionError> for ConfigurationError {
    fn from(error: SortInjectionError) -> Self {
        Self::SortInjection(error)
    }
}

impl From<TermConversionError> for ConfigurationError {
    fn from(error: TermConversionError) -> Self {
        Self::Conversion(error)
    }
}

/// Builds `initGeneratedTopCell` patterns for one compiled definition from concrete text.
///
/// A compiled definition, a program text at a start sort, and a text for each declared
/// configuration variable denote one initial configuration. The assembler owns the decisions that
/// fix it:
///
/// - The program is parsed with the syntax module. A variable is parsed with the module its
///   cell's `parser` attribute names; without one, a `String`-sorted `$IO` or `$STDIN` is parsed
///   with `STRING-SYNTAX`, and any other variable as [`variable_reading_modules`] says: with the
///   syntax module's grammar first wherever that module has the variable's sort (or the sort is
///   `K` or `KItem`), then with the main module's, and with the main module's alone otherwise.
///   `$IO` and `$STDIN` are the stream variables whose `String` values the runner supplies, so
///   their text is a `String` literal and the `String` literal grammar is its parser when the
///   cell declares none. Every caller reads a variable's text with this one rule (krun's `-c`,
///   k-rust-fuzz, krs-exec and kink), so one text denotes one term in all of them.
/// - A `K`-sorted variable prefers an item reading, then tries the visible K grammar only
///   when there is no item reading or entry sort. Every payload travels as a boxed K value.
/// - Every value is macro-expanded in the main module and instantiated at its position,
///   `configuration_position` of its declared or start sort.
///   Outer placement at K preserves that instance and every sequence tail.
/// - Applications convert to KORE with the main module; tokens keep the lexical hooks of the
///   module that parsed them.
///
/// Parsers, the macro-expansion views, and the sort injectors are built on first use and kept, so
/// one assembler should serve every configuration built for its definition; the macro-expansion
/// definition is the grammar's ([`ProgramGrammar::macro_definition`]), and the expander itself
/// is built per value. The program has its own
/// sort injector, apart from the one the configuration values share; parsers are kept per module,
/// whichever input they were built for. `finish`
/// returns the pattern and leaves the assembler empty for the next configuration.
pub struct ConfigurationAssembler<'g> {
    grammar: &'g ProgramGrammar,
    main_module: String,
    syntax_module: String,
    variables: &'g BTreeMap<String, KastSort>,
    parser_modules: Option<BTreeMap<String, String>>,
    /// The module reading first each variable that [`variable_reading_modules`] selects, computed
    /// on first use.
    variable_modules: Option<BTreeMap<String, String>>,
    expansion: Option<ProgramExpansion<'g>>,
    parsers: BTreeMap<String, ProgramParser>,
    injector: Option<SortInjector<'g, 'g>>,
    /// The injector the program is instantiated with, apart from [`Self::injector`], which the
    /// configuration values and the assembly share.
    program_injector: Option<SortInjector<'g, 'g>>,
    program: Option<ConfigurationBinding>,
    bound: BTreeSet<String>,
    bindings: Vec<ConfigurationBinding>,
}

impl<'g> ConfigurationAssembler<'g> {
    /// `variables` maps each declared configuration variable, without its `$`, to its sort.
    pub fn new(
        grammar: &'g ProgramGrammar,
        main_module: impl Into<String>,
        syntax_module: impl Into<String>,
        variables: &'g BTreeMap<String, KastSort>,
    ) -> Self {
        Self {
            grammar,
            main_module: main_module.into(),
            syntax_module: syntax_module.into(),
            variables,
            parser_modules: None,
            variable_modules: None,
            expansion: None,
            parsers: BTreeMap::new(),
            injector: None,
            program_injector: None,
            program: None,
            bound: BTreeSet::new(),
            bindings: Vec::new(),
        }
    }

    /// Bind `$PGM` to `text`, read from no file, parsed with the syntax module at `start_sort`:
    /// [`Self::program_file`] with the file name [`UNNAMED_PROGRAM`].
    pub fn program(&mut self, start_sort: &KastSort, text: &str) -> Result<(), ConfigurationError> {
        self.program_file(start_sort, text, UNNAMED_PROGRAM)
    }

    /// Bind `$PGM` to `text`, read from the file `file`, parsed with the syntax module at
    /// `start_sort`; `file` is the name its locations carry
    /// ([`ProgramParser::parse_file`]).
    ///
    /// A definition that declares no `$PGM` still checks a supplied program. If its initializer
    /// is nullary, `finish` discards the checked value because no map is read.
    pub fn program_file(
        &mut self,
        start_sort: &KastSort,
        text: &str,
        file: &str,
    ) -> Result<(), ConfigurationError> {
        if self.program.is_some() {
            return Err(ConfigurationError::Duplicate { name: "PGM".into() });
        }
        // The syntax module's parser is kept with the configuration values' parsers, so a
        // variable parsed with the same module shares it.
        if !self.parsers.contains_key(&self.syntax_module) {
            self.parsers.insert(
                self.syntax_module.clone(),
                ProgramParser::from_resolved(self.grammar.resolved(), &self.syntax_module)?,
            );
        }
        let parser = &self.parsers[&self.syntax_module];
        let denoted = parser.start_sort(start_sort).clone();
        let program = parser
            .parse_file(start_sort, text, file)
            .map_err(ConfigurationError::Program)?;
        let position = configuration_position(&denoted);
        let program = self.expand(program, &position)?;
        // The program is instantiated independently of the configuration values; no sentence
        // sort variable may survive in either kind of ground value. Its injector draws its fresh
        // sort parameters from zero for each program, as a new injector does.
        if self.program_injector.is_none() {
            self.program_injector = Some(SortInjector::new(
                self.grammar.resolved(),
                &self.main_module,
            )?);
        }
        let injector = self
            .program_injector
            .as_ref()
            .expect("the program injector was created above");
        injector.reset_sort_parameters();
        let value = self.to_kore(injector, &self.syntax_module, &program, "$PGM")?;
        self.program = Some(ConfigurationBinding {
            name: "$PGM".to_owned(),
            value,
        });
        Ok(())
    }

    /// Bind `$PGM` to `term`, a term over this definition's labels built without the parser:
    /// [`Self::program`] after its parse, as [`Self::bind_term`] is [`Self::bind`] after its
    /// parse.
    ///
    /// The term is macro-expanded and typed as a parsed program is, and its tokens take the
    /// syntax module's lexical hooks, the module a program text is read with; its sort must be
    /// at most `$PGM`'s declared sort, which the parser guarantees for text by parsing at that
    /// sort. A failed bind leaves the configuration unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`ConfigurationError::UnknownVariable`] when the definition declares no `$PGM`,
    /// [`ConfigurationError::Duplicate`] when a program is already bound, and the expansion's
    /// or typing's error otherwise ([`ConfigurationError::ValueSort`] for a term of another
    /// sort).
    pub fn program_term(&mut self, term: Term) -> Result<(), ConfigurationError> {
        if self.program.is_some() {
            return Err(ConfigurationError::Duplicate { name: "PGM".into() });
        }
        let Some(sort) = self.variables.get("PGM").cloned() else {
            return Err(ConfigurationError::UnknownVariable {
                name: "PGM".into(),
                available: self
                    .variables
                    .keys()
                    .map(|candidate| format!("${candidate}"))
                    .collect(),
            });
        };
        let expanded = self.expand(
            ParsedProgram::from_term(term),
            &configuration_position(&sort),
        )?;
        let resolved = self.grammar.resolved();
        if self.program_injector.is_none() {
            self.program_injector = Some(SortInjector::new(resolved, &self.main_module)?);
        }
        let injector = self
            .program_injector
            .as_ref()
            .expect("the program injector was created above");
        injector.reset_sort_parameters();
        let value = ConfigurationValue::from_expanded_at(
            injector,
            resolved,
            &self.main_module,
            &self.syntax_module,
            &expanded,
            "$PGM",
            &sort,
        )?;
        self.program = Some(ConfigurationBinding {
            name: "$PGM".to_owned(),
            value,
        });
        Ok(())
    }

    /// Bind the configuration variable `name` (with or without its `$`) to `text`.
    ///
    /// The name is checked before the text is parsed, so a repeated or undeclared name is
    /// reported as such whatever its text. A failed bind leaves the configuration unchanged.
    pub fn bind(&mut self, name: &str, text: &str) -> Result<(), ConfigurationError> {
        let (name, sort) = self.unbound_variable(name)?;
        let (name, sort) = (name.as_str(), &sort);
        let resolved = self.grammar.resolved();
        let parse_sort = configuration_position(sort);
        // The first module whose grammar parses the text reads it. Where none does, each one's
        // failure is reported: the text is no value under the rule, which reads it with either
        // grammar, so neither failure alone says why (a text written as a program's input fails
        // where the syntax module's grammar stops, one that needs a production only the main
        // module has where the main module's does).
        let mut read = None;
        let mut syntax_attempt = None;
        for parser_module in self.parser_modules_of(name, sort)? {
            if !self.parsers.contains_key(&parser_module) {
                self.parsers.insert(
                    parser_module.clone(),
                    ProgramParser::from_resolved(resolved, &parser_module)?,
                );
            }
            let parsed = if sort.is_builtin(BuiltinSort::K) {
                self.parsers[&parser_module].parse_configuration_k_value(text)
            } else {
                self.parsers[&parser_module].parse(&parse_sort, text)
            };
            let done = parsed.is_ok();
            if let Some((_, Err(failed))) = read.replace((parser_module, parsed)) {
                syntax_attempt = Some(Box::new(failed));
            }
            if done {
                break;
            }
        }
        let (parser_module, parsed) = read.expect("a variable is read by at least one module");
        let parsed = parsed.map_err(|error| ConfigurationError::Parse {
            variable: name.into(),
            sort: sort.clone(),
            error: Box::new(error),
            syntax_attempt,
        })?;
        let expanded = self.expand(parsed, &parse_sort)?;
        if self.injector.is_none() {
            self.injector = Some(SortInjector::new(resolved, &self.main_module)?);
        }
        let injector = self
            .injector
            .as_ref()
            .expect("the injector was created above");
        let value = self.to_kore(injector, &parser_module, &expanded, &format!("${name}"))?;
        self.bound.insert(name.to_owned());
        self.bindings.push(ConfigurationBinding {
            name: format!("${name}"),
            value,
        });
        Ok(())
    }

    /// Bind the configuration variable `name` (with or without its `$`) to `term`, a term over
    /// this definition's labels built without the parser: [`Self::bind`] after its parse.
    ///
    /// The term is macro-expanded and typed as a parsed value is, so its labels and tokens need
    /// no injections; its sort must be at most the declared sort, which the parser guarantees
    /// for text by parsing at that sort. Its tokens take the lexical hooks of the module that
    /// would parse the variable's text. A failed bind leaves the configuration unchanged.
    pub fn bind_term(&mut self, name: &str, term: Term) -> Result<(), ConfigurationError> {
        let (name, sort) = self.unbound_variable(name)?;
        let token_module = self.parser_module(&name, &sort)?;
        let expanded = self.expand(
            ParsedProgram::from_term(term),
            &configuration_position(&sort),
        )?;
        let resolved = self.grammar.resolved();
        if self.injector.is_none() {
            self.injector = Some(SortInjector::new(resolved, &self.main_module)?);
        }
        let injector = self
            .injector
            .as_ref()
            .expect("the injector was created above");
        let variable = format!("${name}");
        let value = ConfigurationValue::from_expanded_at(
            injector,
            resolved,
            &self.main_module,
            &token_module,
            &expanded,
            &variable,
            &sort,
        )?;
        self.bound.insert(name);
        self.bindings.push(ConfigurationBinding {
            name: variable,
            value,
        });
        Ok(())
    }

    /// Bind the configuration variable `name` (with or without its `$`) to `pattern`, a KORE
    /// value over this definition's symbols that is already a ground term of exactly the
    /// variable's declared sort: one a front end lowered with the definition (an input's declared
    /// default), where [`Self::bind_term`] would type and lower it again. It is placed in the
    /// configuration map as every bound value is, at `K` by the declared sort's placement, then
    /// boxed; nothing in it is expanded or typed again, so its sort is the caller's statement. A
    /// failed bind leaves the configuration unchanged.
    ///
    /// # Errors
    ///
    /// As [`Self::bind`] for the name: [`ConfigurationError::ProgramVariable`] for `$PGM` (bind
    /// it with [`Self::program_pattern`]), [`ConfigurationError::Duplicate`] and
    /// [`ConfigurationError::UnknownVariable`]; [`ConfigurationError::Unplaceable`] for a sort
    /// with no placement at `K`.
    pub fn bind_pattern(&mut self, name: &str, pattern: Pattern) -> Result<(), ConfigurationError> {
        let (name, sort) = self.unbound_variable(name)?;
        if self.injector.is_none() {
            self.injector = Some(SortInjector::new(
                self.grammar.resolved(),
                &self.main_module,
            )?);
        }
        let injector = self
            .injector
            .as_ref()
            .expect("the injector was created above");
        let variable = format!("${name}");
        let value = ConfigurationValue::from_pattern_at(injector, pattern, &sort, &variable)?;
        self.bound.insert(name);
        self.bindings.push(ConfigurationBinding {
            name: variable,
            value,
        });
        Ok(())
    }

    /// Bind `$PGM` to `pattern`, a KORE value of exactly `$PGM`'s declared sort, as
    /// [`Self::bind_pattern`] binds any other variable: [`Self::program_term`] without the
    /// expansion and typing the caller already did.
    ///
    /// # Errors
    ///
    /// [`ConfigurationError::UnknownVariable`] when the definition declares no `$PGM`,
    /// [`ConfigurationError::Duplicate`] when a program is already bound, and
    /// [`ConfigurationError::Unplaceable`] for a sort with no placement at `K`.
    pub fn program_pattern(&mut self, pattern: Pattern) -> Result<(), ConfigurationError> {
        if self.program.is_some() {
            return Err(ConfigurationError::Duplicate { name: "PGM".into() });
        }
        let Some(sort) = self.variables.get("PGM").cloned() else {
            return Err(ConfigurationError::UnknownVariable {
                name: "PGM".into(),
                available: self
                    .variables
                    .keys()
                    .map(|candidate| format!("${candidate}"))
                    .collect(),
            });
        };
        if self.program_injector.is_none() {
            self.program_injector = Some(SortInjector::new(
                self.grammar.resolved(),
                &self.main_module,
            )?);
        }
        let injector = self
            .program_injector
            .as_ref()
            .expect("the program injector was created above");
        let value = ConfigurationValue::from_pattern_at(injector, pattern, &sort, "$PGM")?;
        self.program = Some(ConfigurationBinding {
            name: "$PGM".to_owned(),
            value,
        });
        Ok(())
    }

    /// The module whose grammar reads the value of the variable `name` of sort `sort` first
    /// ([`Self::parser_modules_of`]), whose lexical hooks a term bound without the parser takes.
    fn parser_module(&mut self, name: &str, sort: &KastSort) -> Result<String, ConfigurationError> {
        let mut modules = self.parser_modules_of(name, sort)?;
        Ok(modules.remove(0))
    }

    /// The modules whose grammars read the value of the variable `name` of sort `sort`, in the
    /// order they are tried: its cell's `parser` module alone; `STRING-SYNTAX` alone for a stream
    /// variable; the syntax module, then the main module, for a variable
    /// [`variable_reading_modules`] selects; or the main module alone.
    fn parser_modules_of(
        &mut self,
        name: &str,
        sort: &KastSort,
    ) -> Result<Vec<String>, ConfigurationError> {
        let declared_parser = self.parser_modules()?.get(name).cloned();
        let modules = match declared_parser {
            Some(parser_module) => vec![parser_module],
            None if matches!(name, "IO" | "STDIN") && sort.is_builtin(BuiltinSort::String) => {
                vec!["STRING-SYNTAX".to_owned()]
            }
            None => {
                let first = self.variable_modules()?.get(name).cloned();
                first
                    .filter(|module| *module != self.main_module)
                    .into_iter()
                    .chain([self.main_module.clone()])
                    .collect()
            }
        };
        for parser_module in &modules {
            if self.grammar.resolved().module_id(parser_module).is_none() {
                return Err(ConfigurationError::ParserModuleNotFound {
                    variable: name.into(),
                    module: parser_module.clone(),
                });
            }
        }
        Ok(modules)
    }

    /// The declared sort of `name` (with or without its `$`), checked to be a declared variable
    /// other than `$PGM` that is not bound yet.
    fn unbound_variable(&self, name: &str) -> Result<(String, KastSort), ConfigurationError> {
        let name = name.strip_prefix('$').unwrap_or(name);
        if name.is_empty() {
            return Err(ConfigurationError::EmptyName);
        }
        if name == "PGM" {
            return Err(ConfigurationError::ProgramVariable);
        }
        if self.bound.contains(name) {
            return Err(ConfigurationError::Duplicate { name: name.into() });
        }
        let variables = self.variables;
        let sort = variables
            .get(name)
            .ok_or_else(|| ConfigurationError::UnknownVariable {
                name: name.into(),
                available: variables
                    .keys()
                    .filter(|candidate| candidate.as_str() != "PGM")
                    .map(|candidate| format!("${candidate}"))
                    .collect(),
            })?;
        Ok((name.to_owned(), sort.clone()))
    }

    /// Bind each declared `String`-sorted stream variable that is still unbound: `$IO` to `on`
    /// or `off` after `io`, and `$STDIN` to the input `read_input` returns, or to the empty
    /// string when `io` is on or the program itself was read from that input. `read_input` runs
    /// only when its result is used.
    ///
    /// The definition's parser attributes are validated first, so a malformed definition is
    /// reported before any input is consumed.
    pub fn bind_stream_defaults<E: From<ConfigurationError>>(
        &mut self,
        io: bool,
        program_uses_input: bool,
        read_input: impl FnOnce() -> Result<Vec<u8>, E>,
    ) -> Result<(), E> {
        self.parser_modules()?;
        if self.injector.is_none() {
            self.injector = Some(
                SortInjector::new(self.grammar.resolved(), &self.main_module)
                    .map_err(ConfigurationError::from)?,
            );
        }
        let defaults = stream_defaults(
            self.injector
                .as_ref()
                .expect("the injector was created above"),
            self.variables,
            &mut self.bound,
            io,
            program_uses_input,
            read_input,
        )?;
        self.bindings.extend(defaults);
        Ok(())
    }

    /// Return the `initGeneratedTopCell` application: `$PGM` first, then the variables in the
    /// order they were bound.
    ///
    /// Every declared variable must be bound, `$PGM` by [`Self::program`] and the others by
    /// [`Self::bind`] or [`Self::bind_stream_defaults`]; otherwise nothing changes and the
    /// error names the unbound ones. On success the assembler is empty again.
    pub fn finish(&mut self) -> Result<Pattern, ConfigurationError> {
        let mut missing = Vec::new();
        if self.variables.contains_key("PGM") && self.program.is_none() {
            missing.push("$PGM".to_owned());
        }
        missing.extend(missing_variables(self.variables, &self.bound));
        if !missing.is_empty() {
            return Err(ConfigurationError::Missing { names: missing });
        }
        let resolved = self.grammar.resolved();
        let module = resolved.module_id(&self.main_module).ok_or_else(|| {
            ConfigurationError::ParserModuleNotFound {
                variable: "configuration initializer".into(),
                module: self.main_module.clone(),
            }
        })?;
        let sentences = resolved.sentences(module);
        let initializer_takes_map = |sentence: &Sentence| {
            matches!(sentence, Sentence::Production { items, .. }
                if items.iter().any(|item| matches!(item,
                    crate::definition::ProductionItem::NonTerminal { sort, .. }
                        if sort.is_builtin(BuiltinSort::Map))))
        };
        let top = sentences.iter().find(|sentence| {
            matches!(sentence, Sentence::Production { label: Some(label), .. }
                if label.name == crate::kast::GeneratedCell::Top.initializer())
        });
        // The compiled top initializer is synthesized after the frontend grammar is saved.
        // In that grammar, it takes the map exactly when a visible cell initializer does.
        // Use the generated arity rather than a decoder search: regular variables and streams
        // also require Init, including before stream expansion inserts the decoder read.
        let takes_map = top.map_or_else(
            || {
                sentences.iter().any(|sentence| {
                    sentence.attributes().has(AttributeKey::Initializer)
                        && initializer_takes_map(sentence)
                })
            },
            |sentence| initializer_takes_map(sentence),
        );
        // A nullary initializer has no map argument; supplied values have already been checked.
        if !takes_map {
            let initial = kore_application("LblinitGeneratedTopCell", Vec::new(), Vec::new());
            self.clear();
            return Ok(initial);
        }
        if self.injector.is_none() {
            self.injector = Some(SortInjector::new(resolved, &self.main_module)?);
        }
        let key = self
            .injector
            .as_ref()
            .expect("the injector was created above")
            .injection_witness(
                &KastSort::builtin(BuiltinSort::KConfigVar),
                &KastSort::builtin(BuiltinSort::KItem),
            )
            .ok_or_else(|| ConfigurationError::Unplaceable {
                variable: "configuration map key".into(),
                sort: KastSort::builtin(BuiltinSort::KConfigVar),
            })?;
        let initial = top_cell_initializer(self.program.as_ref(), &self.bindings, &key);
        self.clear();
        Ok(initial)
    }

    /// Discard the program and every binding without assembling them.
    pub fn clear(&mut self) {
        self.program = None;
        self.bound.clear();
        self.bindings.clear();
        // Reset temporary inference variables between configurations, including after a failed
        // binding. Successful ground values contain none of these variables.
        if let Some(injector) = &self.injector {
            injector.reset_sort_parameters();
        }
        if let Some(injector) = &self.program_injector {
            injector.reset_sort_parameters();
        }
    }

    /// [`variable_reading_modules`] of this assembler's grammar, syntax module and variables,
    /// computed on first use: like the `parser` attributes, it depends on the definition alone.
    fn variable_modules(&mut self) -> Result<&BTreeMap<String, String>, ConfigurationError> {
        if self.variable_modules.is_none() {
            self.variable_modules = Some(variable_reading_modules(
                self.grammar,
                &self.syntax_module,
                self.variables,
            )?);
        }
        Ok(self
            .variable_modules
            .as_ref()
            .expect("the variable modules were computed above"))
    }

    fn parser_modules(&mut self) -> Result<&BTreeMap<String, String>, ConfigurationError> {
        if self.parser_modules.is_none() {
            self.parser_modules = Some(
                parser_modules(self.grammar.resolved(), &self.main_module)
                    .map_err(ConfigurationError::ParserAttribute)?,
            );
        }
        Ok(self
            .parser_modules
            .as_ref()
            .expect("the parser modules were computed above"))
    }

    /// Expand the macros of a parsed value in the main module. The macro-expansion definition
    /// and its derived views depend on the grammar alone, so they are prepared once and shared
    /// by every value; each value gets its own expander and fresh-name allocator
    /// ([`ProgramExpansion::expand_program`]).
    fn expand(
        &mut self,
        program: ParsedProgram,
        position: &KastSort,
    ) -> Result<ExpandedProgram, ConfigurationError> {
        if self.expansion.is_none() {
            let grammar: &'g ProgramGrammar = self.grammar;
            self.expansion = Some(
                grammar
                    .macro_definition()
                    .map_err(ConfigurationError::MacroExpansion)?
                    .expansion(),
            );
        }
        self.expansion
            .as_ref()
            .expect("the expansion was prepared above")
            .expand_program(&self.main_module, program, position)
            .map_err(ConfigurationError::MacroExpansion)
    }

    /// Instantiate once, then place only the typed root at K for transport.
    fn to_kore(
        &self,
        injector: &SortInjector<'g, 'g>,
        token_module: &str,
        program: &ExpandedProgram,
        variable: &str,
    ) -> Result<ConfigurationValue, ConfigurationError> {
        ConfigurationValue::from_expanded(
            injector,
            self.grammar.resolved(),
            &self.main_module,
            token_module,
            program,
            variable,
        )
    }
}

use value::ConfigurationValue;

/// The sort and place (`file:line:column-line:column`) of the first located term of `term` in
/// pre-order, the outermost and leftmost; `None` when it holds no `#location` application of the
/// shape the program parsers build.
fn first_located_term(term: &Term) -> Option<(KastSort, String)> {
    let mut found = None;
    term.visit_preorder(&mut |term| {
        if found.is_some() {
            return;
        }
        let Term::Apply { label, arguments } = term else {
            return;
        };
        if label.name != LOCATION_LABEL {
            return;
        }
        let ([sort], [_, file, numbers @ ..]) = (label.parameters.as_slice(), arguments.as_slice())
        else {
            return;
        };
        let token = |term: &Term| {
            if let Term::Token { token, .. } = term.unannotated() {
                Some(token.clone())
            } else {
                None
            }
        };
        let Some(file) = token(file).and_then(|file| crate::kast::string::unquote(&file).ok())
        else {
            return;
        };
        let Some([start_line, start_column, end_line, end_column]) = numbers
            .iter()
            .map(token)
            .collect::<Option<Vec<_>>>()
            .and_then(|numbers| <[String; 4]>::try_from(numbers).ok())
        else {
            return;
        };
        found = Some((
            sort.clone(),
            format!("{file}:{start_line}:{start_column}-{end_line}:{end_column}"),
        ));
    });
    found
}

// Only these builders can create a transport payload. Each places a value of a known sort at `K`:
// a term the assembler typed, a string, or a lowered value at its variable's declared sort.
mod value {
    use super::*;

    #[derive(Debug)]
    pub(super) struct ConfigurationValue {
        pattern: Pattern,
    }

    impl ConfigurationValue {
        pub(super) fn from_expanded(
            injector: &SortInjector<'_, '_>,
            resolved: &ResolvedDefinition,
            main_module: &str,
            token_module: &str,
            program: &ExpandedProgram,
            variable: &str,
        ) -> Result<Self, ConfigurationError> {
            let (term, sort) = Self::typed(injector, main_module, program, variable)?;
            Self::placed(
                injector,
                resolved,
                main_module,
                token_module,
                term,
                sort,
                variable,
            )
        }

        /// [`Self::from_expanded`] for a value whose sort the parser did not establish: the
        /// value's sort must be at most `declared`.
        pub(super) fn from_expanded_at(
            injector: &SortInjector<'_, '_>,
            resolved: &ResolvedDefinition,
            main_module: &str,
            token_module: &str,
            program: &ExpandedProgram,
            variable: &str,
            declared: &KastSort,
        ) -> Result<Self, ConfigurationError> {
            let (term, sort) = Self::typed(injector, main_module, program, variable)?;
            if injector.placement(&sort, declared).is_none() {
                return Err(ConfigurationError::ValueSort(Box::new(ValueSortMismatch {
                    variable: variable.into(),
                    declared: declared.clone(),
                    actual: sort,
                })));
            }
            Self::placed(
                injector,
                resolved,
                main_module,
                token_module,
                term,
                sort,
                variable,
            )
        }

        fn typed(
            injector: &SortInjector<'_, '_>,
            main_module: &str,
            program: &ExpandedProgram,
            variable: &str,
        ) -> Result<(Term, KastSort), ConfigurationError> {
            injector.inject_ground(program).map_err(|error| {
                if let SortInjectionError::UnknownLabel(label) = &error
                    && label == LOCATION_LABEL
                    && let Some((sort, place)) = first_located_term(program.term())
                {
                    ConfigurationError::UnlocatableTerm(Box::new(UnlocatableTerm {
                        variable: variable.into(),
                        sort,
                        place,
                        main_module: main_module.into(),
                    }))
                } else if matches!(&error, SortInjectionError::UndeterminedInstance(_)) {
                    ConfigurationError::UndeterminedInstance {
                        variable: variable.into(),
                        error: Box::new(error),
                    }
                } else {
                    ConfigurationError::SortInjection(error)
                }
            })
        }

        fn placed(
            injector: &SortInjector<'_, '_>,
            resolved: &ResolvedDefinition,
            main_module: &str,
            token_module: &str,
            term: Term,
            sort: KastSort,
            variable: &str,
        ) -> Result<Self, ConfigurationError> {
            let placement = injector
                .placement(&sort, &KastSort::builtin(BuiltinSort::K))
                .ok_or_else(|| ConfigurationError::Unplaceable {
                    variable: variable.into(),
                    sort,
                })?;
            let term = placement.apply(term);
            let pattern = term_to_kore_from_resolved_with_token_module(
                resolved,
                main_module,
                token_module,
                &term,
            )?;
            Ok(Self { pattern })
        }

        /// A KORE value already of the variable's declared sort `declared`
        /// ([`ConfigurationAssembler::bind_pattern`]), placed at `K` as [`Self::placed`] places
        /// a typed term: from the value's own sort. A value at `K` is injected from its least
        /// sort, as every bound value is ([`Self::placed`] places a typed term from the sort
        /// its typing gives it), so where `pattern` is `inj{T, S}(inner)`, its declared sort `S`
        /// reached from a strict subsort `T`, `inner` is placed from `T` and the outer
        /// injection is not kept: the payload is `inj{T, KItem}(inner)`, the one the same value
        /// bound by hand gives, not `inj{S, KItem}(inj{T, S}(inner))`, which only an injection
        /// normalisation would make equal to it. Any other pattern is placed from `S`.
        pub(super) fn from_pattern_at(
            injector: &SortInjector<'_, '_>,
            pattern: Pattern,
            declared: &KastSort,
            variable: &str,
        ) -> Result<Self, ConfigurationError> {
            let k = KastSort::builtin(BuiltinSort::K);
            if let Some((own, inner)) = Self::injected_from(injector, &pattern, declared)
                && let Some(placement) = injector.placement(&own, &k)
            {
                return Ok(Self {
                    pattern: placement.apply_kore(inner.clone(), &[]),
                });
            }
            let placement = injector.placement(declared, &k).ok_or_else(|| {
                ConfigurationError::Unplaceable {
                    variable: variable.into(),
                    sort: declared.clone(),
                }
            })?;
            Ok(Self {
                pattern: placement.apply_kore(pattern, &[]),
            })
        }

        /// The sort `T` and the argument of `pattern` where it is `inj{T, S}(inner)` with `S`
        /// the encoding of `declared` and `T` a sort whose encoding is `T` and that is at most
        /// `declared`; `None` for any other pattern.
        fn injected_from<'p>(
            injector: &SortInjector<'_, '_>,
            pattern: &'p Pattern,
            declared: &KastSort,
        ) -> Option<(KastSort, &'p Pattern)> {
            let Pattern::Application { symbol, arguments } = pattern else {
                return None;
            };
            let ([source, target], [inner]) =
                (symbol.sort_parameters.as_slice(), arguments.as_slice())
            else {
                return None;
            };
            if symbol.name != crate::names::WellKnownSymbol::Inj.as_str()
                || *target != crate::kompile::encode_kore_sort(declared)
            {
                return None;
            }
            let own = crate::kast::convert::convert_sort(source).ok()?;
            (crate::kompile::encode_kore_sort(&own) == *source
                && own != *declared
                && injector.placement(&own, declared).is_some())
            .then_some((own, inner))
        }

        pub(super) fn from_string(
            injector: &SortInjector<'_, '_>,
            text: impl Into<KoreString>,
            variable: &str,
        ) -> Result<Self, ConfigurationError> {
            let sort = KastSort::builtin(BuiltinSort::String);
            let placement = injector
                .placement(&sort, &KastSort::builtin(BuiltinSort::K))
                .ok_or_else(|| ConfigurationError::Unplaceable {
                    variable: variable.into(),
                    sort,
                })?;
            Ok(Self {
                pattern: placement.apply_kore(string_domain_value(text), &[]),
            })
        }

        pub(super) fn boxed(&self) -> Pattern {
            kore_application(
                &crate::kompile::encode_kore_label(&crate::kast::Label::new(
                    crate::definition::configuration_value::BOX_LABEL,
                ))
                .name,
                Vec::new(),
                vec![self.pattern.clone()],
            )
        }
    }
}

/// A program read at a K-declared position prefers one item, using the same
/// instantiation preference as the assembler, so the generated parser's start
/// symbol is KItem and its result is a licensed item embedding.
pub fn program_start_position(declared: &KastSort) -> KastSort {
    configuration_position(declared)
}

/// The module whose grammar reads first each configuration variable of `variables` but `$PGM`
/// that no cell `parser` attribute assigns one and that is no stream variable (`$IO`, `$STDIN`
/// at `String`, read with `STRING-SYNTAX`): the syntax module `syntax_module`, a program's
/// grammar, wherever it has the variable's sort. [`ConfigurationAssembler`] reads every variable
/// with it.
///
/// A variable's text is input, as a program is, and the main module's grammar holds more than a
/// program can write: every token sort of the definition, so its scanner reads `word` as an `Id`
/// wherever it stands, also where a variable of a token sort `Word` means that `Word`. A `K` or
/// `KItem` variable takes any item, which the syntax module reads as it reads `$PGM`. Where the
/// syntax module's grammar does not parse the text, the main module's reads it: it also has the
/// productions only rules may use (a builtin collection's constructors, a production the
/// partition placed in the semantics module), with which a value can be written. A sort the
/// syntax module does not have (a builtin collection's, which K supplies only with a full
/// module) is read with the main module's grammar alone.
///
/// Every tool that reads a configuration variable's text for one definition reads it with this
/// rule, through [`ConfigurationAssembler`], so one text denotes one term in all of them: krun's
/// `-c` and k-rust-fuzz (through `KrunAssembler`), krs-exec and kink. A tool that needs to know
/// which variables a program's grammar reads (krs-exec's read-back of a print) calls it itself.
///
/// # Errors
///
/// Returns [`ConfigurationError::ParserAttribute`] for a malformed cell `parser` attribute.
pub fn variable_reading_modules(
    grammar: &ProgramGrammar,
    syntax_module: &str,
    variables: &BTreeMap<String, KastSort>,
) -> Result<BTreeMap<String, String>, ConfigurationError> {
    let resolved = grammar.resolved();
    let declared = parser_modules(resolved, &grammar.definition().main_module)
        .map_err(ConfigurationError::ParserAttribute)?;
    let program_sorts = resolved
        .module_id(syntax_module)
        .map(|module| {
            resolved
                .sentences(module)
                .into_iter()
                .filter_map(|sentence| {
                    let (Sentence::SyntaxSort { sort, .. } | Sentence::Production { sort, .. }) =
                        sentence
                    else {
                        return None;
                    };
                    Some(sort.name.clone())
                })
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    Ok(variables
        .iter()
        .filter(|(name, sort)| {
            name.as_str() != "PGM"
                && !declared.contains_key(name.as_str())
                && !(matches!(name.as_str(), "IO" | "STDIN")
                    && sort.is_builtin(BuiltinSort::String))
                && (sort.is_builtin(BuiltinSort::K)
                    || sort.is_builtin(BuiltinSort::KItem)
                    || program_sorts.contains(&sort.name))
        })
        .map(|(name, _)| (name.clone(), syntax_module.to_owned()))
        .collect())
}

/// KItem is the instantiation preference for an open result read at K; fixed K values retain K.
fn configuration_position(declared: &KastSort) -> KastSort {
    if declared.name == BuiltinSort::K.k_name() {
        KastSort::builtin(BuiltinSort::KItem)
    } else {
        declared.clone()
    }
}

pub fn parser_modules(
    definition: &ResolvedDefinition,
    module: &str,
) -> Result<BTreeMap<String, String>, String> {
    let module = definition
        .module_id(module)
        .ok_or_else(|| format!("definition has no module `{module}`"))?;
    let mut modules = BTreeMap::new();
    for sentence in definition.sentences(module) {
        let Sentence::Production { attributes, .. } = sentence else {
            continue;
        };
        if !attributes.has(AttributeKey::Cell) {
            continue;
        }
        let Some(parser) = attributes.string(AttributeKey::Parser) else {
            continue;
        };
        for entry in parser.split(';') {
            let fields = entry.split(',').map(str::trim).collect::<Vec<_>>();
            let [name, parser_module] = fields.as_slice() else {
                return Err(format!("Invalid value for parser attribute: {parser}"));
            };
            if name.is_empty() || parser_module.is_empty() {
                return Err(format!("Invalid value for parser attribute: {parser}"));
            }
            modules.insert(
                name.strip_prefix('$').unwrap_or(name).to_string(),
                (*parser_module).to_string(),
            );
        }
    }
    Ok(modules)
}

/// Bind each declared `String`-sorted stream variable that is still unbound, `$IO` before
/// `$STDIN`. Buffered stdin is read only for an unbound `$STDIN` when IO is off and the program
/// itself does not consume stdin; otherwise `$STDIN` is the empty string.
pub(crate) fn stream_defaults<E: From<ConfigurationError>>(
    injector: &SortInjector<'_, '_>,
    available: &BTreeMap<String, KastSort>,
    seen: &mut BTreeSet<String>,
    io: bool,
    program_uses_stdin: bool,
    read_buffered_stdin: impl FnOnce() -> Result<Vec<u8>, E>,
) -> Result<Vec<ConfigurationBinding>, E> {
    let mut bindings = Vec::new();
    let mut pending = seen.clone();
    let string_sort = KastSort::builtin(BuiltinSort::String);
    if available.get("IO") == Some(&string_sort) && !seen.contains("IO") {
        bindings.push(ConfigurationBinding {
            name: "$IO".into(),
            value: ConfigurationValue::from_string(injector, if io { "on" } else { "off" }, "$IO")?,
        });
        pending.insert("IO".into());
    }
    if available.get("STDIN") == Some(&string_sort) && !seen.contains("STDIN") {
        let input = if io || program_uses_stdin {
            Vec::new()
        } else {
            read_buffered_stdin()?
        };
        // Console input is bytes, and each is one character, the code point of its value, as
        // `IO.read` reads them.
        bindings.push(ConfigurationBinding {
            name: "$STDIN".into(),
            value: ConfigurationValue::from_string(
                injector,
                input
                    .iter()
                    .map(|byte| char::from(*byte))
                    .collect::<String>(),
                "$STDIN",
            )?,
        });
        pending.insert("STDIN".into());
    }
    *seen = pending;
    Ok(bindings)
}

/// The declared variables other than `$PGM` that `seen` does not bind, each with its `$`, in
/// name order.
pub(crate) fn missing_variables(
    available: &BTreeMap<String, KastSort>,
    seen: &BTreeSet<String>,
) -> Vec<String> {
    available
        .keys()
        .filter(|name| name.as_str() != "PGM" && !seen.contains(*name))
        .map(|name| format!("${name}"))
        .collect()
}

/// Build the `initGeneratedTopCell` application of a configuration map whose entries are the
/// program binding first, when there is one, then `bindings` in their order.
pub(crate) fn top_cell_initializer(
    program: Option<&ConfigurationBinding>,
    bindings: &[ConfigurationBinding],
    key_witness: &super::passes::Injectable,
) -> Pattern {
    let mut entries = program
        .into_iter()
        .chain(bindings)
        .map(|binding| configuration_map_entry(&binding.name, &binding.value, key_witness));
    let arguments = match entries.next() {
        Some(first) => vec![entries.fold(first, |left, right| {
            kore_application("Lbl'Unds'Map'Unds'", Vec::new(), vec![left, right])
        })],
        None => Vec::new(),
    };
    kore_application("LblinitGeneratedTopCell", Vec::new(), arguments)
}

fn configuration_map_entry(
    name: &str,
    value: &ConfigurationValue,
    key_witness: &super::passes::Injectable,
) -> Pattern {
    let key = key_witness.clone().apply_kore(
        Pattern::DomainValue {
            sort: kore_sort(BuiltinSort::KConfigVar.kore_name()),
            value: name.into(),
        },
        &[],
    );
    kore_application(
        "Lbl'UndsPipe'-'-GT-Unds'",
        Vec::new(),
        vec![key, value.boxed()],
    )
}

pub fn kore_application(
    name: &str,
    sort_parameters: Vec<Sort>,
    arguments: Vec<Pattern>,
) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.into(),
            sort_parameters,
        },
        arguments,
    }
}

pub fn kore_sort(name: &str) -> Sort {
    Sort::Application {
        name: name.into(),
        arguments: Vec::new(),
    }
}

fn string_domain_value(value: impl Into<KoreString>) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort(BuiltinSort::String.kore_name()),
        value: value.into(),
    }
}

#[cfg(test)]
mod tests {
    use crate::kore::printer::Printer;

    use super::*;

    #[test]
    fn program_start_position_prefers_kitem_for_k_and_keeps_other_sorts() {
        assert_eq!(
            program_start_position(&KastSort::builtin(BuiltinSort::K)),
            KastSort::builtin(BuiltinSort::KItem)
        );
        assert_eq!(
            program_start_position(&KastSort::builtin(BuiltinSort::KItem)),
            KastSort::builtin(BuiltinSort::KItem)
        );
        assert_eq!(
            program_start_position(&KastSort::new("Pgm")),
            KastSort::new("Pgm")
        );
    }

    #[test]
    fn top_initializer_combines_program_and_configuration_bindings() {
        let frontend = crate::outer::lower(
            &crate::outer::parse(
                "test.k",
                r#"
module MAIN
  syntax String [hook(STRING.String)]
  syntax KConfigVar [hook(KVAR.KVar)]
  syntax KItem ::= KConfigVar
endmodule
"#,
            )
            .unwrap(),
            "MAIN",
        )
        .unwrap();
        let resolved = ResolvedDefinition::resolve(&frontend).unwrap();
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let key = injector
            .injection_witness(&KastSort::new("KConfigVar"), &KastSort::new("KItem"))
            .unwrap();
        let program = ConfigurationBinding {
            name: "$PGM".into(),
            value: ConfigurationValue::from_string(&injector, "program", "$PGM").unwrap(),
        };
        let bindings = [ConfigurationBinding {
            name: "$ENV".into(),
            value: ConfigurationValue::from_string(&injector, "env", "$ENV").unwrap(),
        }];
        let initial = top_cell_initializer(Some(&program), &bindings, &key);
        let rendered = Printer::compact().print_pattern(&initial);

        assert!(rendered.contains("Lbl'Unds'Map'Unds'"), "{rendered}");
        assert!(rendered.contains("$PGM"), "{rendered}");
        assert!(rendered.contains("$ENV"), "{rendered}");
        assert!(
            rendered.contains("inj{SortString{}, SortKItem{}}"),
            "{rendered}"
        );
    }

    #[test]
    fn top_initializer_without_any_binding_is_nullary() {
        let key = super::super::passes::Injectable::between(
            &KastSort::new("KConfigVar"),
            &KastSort::new("KItem"),
            &crate::definition::PartialOrder::new([(
                KastSort::new("KConfigVar"),
                KastSort::new("KItem"),
            )])
            .unwrap(),
        )
        .unwrap();
        let initial = top_cell_initializer(None, &[], &key);
        assert_eq!(
            Printer::compact().print_pattern(&initial),
            "LblinitGeneratedTopCell{}()"
        );
    }
}
