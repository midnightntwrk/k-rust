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
};

use crate::{
    definition::{AttributeKey, Definition, ResolveError, ResolvedDefinition, Sentence},
    inner::{
        ParsedProgram, ProgramError, ProgramParseError, ProgramParser,
        definition_with_named_projections,
    },
    kast::Sort as KastSort,
    kompile::{
        ExpandedProgram, MacroExpansionDefinition, SortInjectionError, SortInjector,
        TermConversionError, term_to_kore_from_resolved_with_token_module,
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
pub struct ProgramGrammar {
    definition: Definition,
    resolved: ResolvedDefinition,
}

impl ProgramGrammar {
    pub fn new(frontend: &Definition) -> Result<Self, ConfigurationError> {
        let definition = definition_with_named_projections(frontend);
        let resolved =
            ResolvedDefinition::resolve(&definition).map_err(ConfigurationError::Definition)?;
        Ok(Self {
            definition,
            resolved,
        })
    }

    pub fn definition(&self) -> &Definition {
        &self.definition
    }

    pub fn resolved(&self) -> &ResolvedDefinition {
        &self.resolved
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
    /// A configuration value that does not parse at its declared sort.
    Parse {
        variable: String,
        sort: KastSort,
        error: Box<ProgramParseError>,
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
    Conversion(TermConversionError),
    Definition(ResolveError),
    Unplaceable {
        variable: String,
        sort: KastSort,
    },
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
            } => write!(
                f,
                "could not parse configuration variable `${variable}` at sort {sort}: {error}"
            ),
            Self::Program(error) => error.fmt(f),
            Self::ParserAttribute(message) | Self::MacroExpansion(message) => f.write_str(message),
            Self::Parser(error) => error.fmt(f),
            Self::UndeterminedInstance { variable, error } => write!(
                f,
                "configuration variable `{variable}` has an undetermined instance: {error}"
            ),
            Self::SortInjection(error) => error.fmt(f),
            Self::Conversion(error) => error.fmt(f),
            Self::Definition(error) => error.fmt(f),
            Self::Unplaceable { variable, sort } => write!(
                f,
                "configuration variable `{variable}` has actual sort {sort}, which cannot be placed at K"
            ),
        }
    }
}

impl std::error::Error for ConfigurationError {}

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
///   with `STRING-SYNTAX`, and any other variable with the main module. `$IO` and `$STDIN` are the
///   stream variables whose `String` values the runner supplies, so their text is a `String`
///   literal and the `String` literal grammar is its parser when the cell declares none.
/// - A `K`-sorted variable prefers an item reading, then tries the visible K grammar only
///   when there is no item reading or entry sort. Every payload travels as a boxed K value.
/// - Every value is macro-expanded in the main module and instantiated at its position,
///   `configuration_position` of its declared or start sort.
///   Outer placement at K preserves that instance and every sequence tail.
/// - Applications convert to KORE with the main module; tokens keep the lexical hooks of the
///   module that parsed them.
///
/// Parsers, the macro expander, and the sort injector are built on first use and kept, so one
/// assembler should serve every configuration built for its definition. `finish` returns the
/// pattern and leaves the assembler empty for the next configuration.
pub struct ConfigurationAssembler<'g> {
    grammar: &'g ProgramGrammar,
    main_module: String,
    syntax_module: String,
    variables: &'g BTreeMap<String, KastSort>,
    parser_modules: Option<BTreeMap<String, String>>,
    macro_definition: Option<MacroExpansionDefinition>,
    parsers: BTreeMap<String, ProgramParser>,
    injector: Option<SortInjector<'g, 'g>>,
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
            macro_definition: None,
            parsers: BTreeMap::new(),
            injector: None,
            program: None,
            bound: BTreeSet::new(),
            bindings: Vec::new(),
        }
    }

    /// Bind `$PGM` to `text` parsed with the syntax module at `start_sort`.
    ///
    /// A definition that declares no `$PGM` still checks a supplied program. If its initializer
    /// is nullary, `finish` discards the checked value because no map is read.
    pub fn program(&mut self, start_sort: &KastSort, text: &str) -> Result<(), ConfigurationError> {
        if self.program.is_some() {
            return Err(ConfigurationError::Duplicate { name: "PGM".into() });
        }
        let parser = ProgramParser::from_resolved(self.grammar.resolved(), &self.syntax_module)?;
        let denoted = parser.start_sort(start_sort).clone();
        let program = parser
            .parse(start_sort, text)
            .map_err(ConfigurationError::Program)?;
        let position = configuration_position(&denoted);
        let program = self.expand(program, &position)?;
        // The program is instantiated independently of the configuration values; no sentence
        // sort variable may survive in either kind of ground value.
        let injector = SortInjector::new(self.grammar.resolved(), &self.main_module)?;
        let value = self.to_kore(&injector, &self.syntax_module, &program, "$PGM")?;
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
        let declared_parser = self.parser_modules()?.get(name).cloned();
        let parser_module = match declared_parser {
            Some(parser_module) => parser_module,
            None if matches!(name, "IO" | "STDIN") && sort.is_builtin(BuiltinSort::String) => {
                "STRING-SYNTAX".to_owned()
            }
            None => self.main_module.clone(),
        };
        let resolved = self.grammar.resolved();
        if resolved.module_id(&parser_module).is_none() {
            return Err(ConfigurationError::ParserModuleNotFound {
                variable: name.into(),
                module: parser_module,
            });
        }
        if !self.parsers.contains_key(&parser_module) {
            self.parsers.insert(
                parser_module.clone(),
                ProgramParser::from_resolved(resolved, &parser_module)?,
            );
        }
        let parse_sort = configuration_position(sort);
        let parsed = if sort.is_builtin(BuiltinSort::K) {
            self.parsers[&parser_module].parse_configuration_k_value(text)
        } else {
            self.parsers[&parser_module].parse(&parse_sort, text)
        }
        .map_err(|error| ConfigurationError::Parse {
            variable: name.into(),
            sort: sort.clone(),
            error: Box::new(error),
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
        let injector = SortInjector::new(resolved, &self.main_module)?;
        let key = injector
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

    /// Expand the macros of a parsed value in the main module. The expander depends on the
    /// grammar alone, so it is prepared once and serves every value.
    fn expand(
        &mut self,
        program: ParsedProgram,
        position: &KastSort,
    ) -> Result<ExpandedProgram, ConfigurationError> {
        if self.macro_definition.is_none() {
            self.macro_definition = Some(
                MacroExpansionDefinition::prepare(self.grammar.definition())
                    .map_err(ConfigurationError::MacroExpansion)?,
            );
        }
        self.macro_definition
            .as_ref()
            .expect("the macro definition was prepared above")
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

// Only these builders can create a transport payload; neither takes an arbitrary pattern/sort pair.
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
            let (term, sort) = injector.inject_ground(program).map_err(|error| {
                if matches!(&error, SortInjectionError::UndeterminedInstance(_)) {
                    ConfigurationError::UndeterminedInstance {
                        variable: variable.into(),
                        error: Box::new(error),
                    }
                } else {
                    ConfigurationError::SortInjection(error)
                }
            })?;
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
        bindings.push(ConfigurationBinding {
            name: "$STDIN".into(),
            value: ConfigurationValue::from_string(injector, input, "$STDIN")?,
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
