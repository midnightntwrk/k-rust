//! Parse configuration and cell-expectation text through k-rust's program pipeline.
//! [`k_rust::kompile::ConfigurationAssembler`] owns krun's `-c` assembly of `initGeneratedTopCell`; this module adds the per-value surface parsing that cell expectations and the Java route's per-variable KORE need.
//! A program parser has no K sequence syntax, so a `K`-sorted cell expectation (`trap ~> .Instrs`) is read by a ground K-value parser ([`ProgramParser::for_ground_values`]): the main module's program grammar plus exactly `.K`, `K ~> K`, and a K bracket.

use k_rust::{
    definition::{AttributeKey, Attributes, Definition, Sentence},
    inner::{PresentedProgram, ProgramParser},
    kast::Sort as KastSort,
    kompile::{
        ConfigurationAssembler, ConfigurationError, MacroExpansionDefinition, ProgramGrammar,
        SortInjector, encode_kore_sort, initial_configuration::parser_modules,
        program_start_position, term_to_kore_from_resolved_with_token_module,
    },
    kore::ast::{Pattern, Sort, Symbol},
    names::BuiltinSort,
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
};

/// The value of one configuration variable for [`Configuration::assemble_pattern`].
pub(crate) enum Binding {
    /// Surface text, parsed at the declared sort.
    Text(String),
    /// A KAST term over the definition's labels, typed at the declared sort without a parse.
    Term(k_rust::kast::Term),
}

/// Why [`Configuration::assemble_pattern`] failed.
#[derive(Debug)]
pub(crate) enum AssemblyError {
    /// The value bound to `variable` without the parser is no term of its sort.
    Value {
        variable: String,
        error: Box<ConfigurationError>,
    },
    /// Any other failure, as the assembler reports it.
    Configuration(ConfigurationError),
}

impl From<ConfigurationError> for AssemblyError {
    fn from(error: ConfigurationError) -> Self {
        Self::Configuration(error)
    }
}

/// `frontend` with the sort predicates `isS` and projections `project:S` the compiled definition
/// generates for its sorts, declared in the main module only: the symbols a rule's `k::is!`,
/// `k::project!` and projected collection lookup apply.
///
/// A program's expansion writes an alias's or a desugar's result into the program, and the
/// expanded program is typed and converted to KORE in the main module. The result holds these
/// symbols exactly where the same term in a rule's result does, and the expanded program then
/// evaluates as that rule's result would, so the main module names them as the compiled
/// definition does; without them the expansion of `cn(1)` under `cn(x) => pair(x, isInt(x))`
/// names no production. The syntax module, which parses programs, is left as it is: there a
/// predicate's name, `isInt`, would be a keyword, which an identifier token spelled the same
/// could no longer be.
///
/// Only the helpers are taken. The passes also state facts of the compiled theory on sentences
/// the frontend already has: the projection pass marks a Map cell collection's key projection
/// (`RowCellMapKey`) `total` when the collection's instance cell is the only generator of its
/// sort. The main module keeps the frontend's own sentences as they are, as every other module
/// does, so such an attribute is not taken: a program is typed and converted by the productions'
/// syntax, sorts and labels, and `total` changes none of them.
fn with_sort_helpers(frontend: &Definition) -> Result<Definition, Box<dyn Error>> {
    let generated = k_rust::kompile::generate_sort_projections(
        &k_rust::kompile::generate_sort_predicate_syntax(frontend)?,
    )?;
    let mut helpers = Vec::new();
    for (module, with) in frontend.modules.iter().zip(&generated.modules) {
        // Each pass appends what it generates after a module's own sentences, which it keeps in
        // place, up to the attributes it adds to them.
        let own = module.local_sentences.len();
        if module.name != with.name
            || with.local_sentences.len() < own
            || !module
                .local_sentences
                .iter()
                .zip(&with.local_sentences)
                .all(|(own, with)| same_up_to_attributes(own, with))
        {
            return Err(format!("sort helper generation changed module `{}`", module.name).into());
        }
        helpers.extend(
            with.local_sentences[own..]
                .iter()
                .filter(|sentence| is_sort_helper(sentence))
                .cloned(),
        );
    }
    let mut output = frontend.clone();
    let main_module = output.main_module.clone();
    let main = output
        .modules
        .iter_mut()
        .find(|module| module.name == main_module)
        .ok_or_else(|| format!("the frontend definition has no main module `{main_module}`"))?;
    main.local_sentences.extend(helpers);
    Ok(output)
}

/// Whether `with` is the sentence `own` with at most its attributes changed.
fn same_up_to_attributes(own: &Sentence, with: &Sentence) -> bool {
    own == with || {
        let [mut own, mut with] = [own.clone(), with.clone()];
        *own.attributes_mut() = Attributes::default();
        *with.attributes_mut() = Attributes::default();
        own == with
    }
}

/// Whether `sentence` is a generated sort predicate (`isS`) or sort projection (`project:S`), or
/// the `Bool` token sort a predicate's result needs; the field projections, which a program value
/// may apply too, are the program grammar's own ([`ProgramGrammar::new`]).
fn is_sort_helper(sentence: &Sentence) -> bool {
    match sentence {
        Sentence::Production {
            label: Some(label),
            attributes,
            ..
        } => {
            attributes.has(AttributeKey::Predicate)
                || label
                    .name
                    .strip_prefix("project:")
                    .is_some_and(|sort| !sort.contains(':'))
        }
        Sentence::SyntaxSort { .. } => true,
        _ => false,
    }
}

/// The program grammar and declared variable sorts that every configuration of one loaded definition is assembled against.
struct Grammar {
    /// The grammar programs and values are typed, expanded and converted with, and the
    /// assembler's: [`with_sort_helpers`] of the frontend definition.
    program: ProgramGrammar,
    /// The grammar this module's own parsers read text with: the frontend definition's.
    parsing: ProgramGrammar,
    variables: BTreeMap<String, KastSort>,
}

/// The reusable surface parsing context for one loaded definition.
///
/// One value exists per compiled [`crate::Semantics`]; the program grammar it borrows is leaked for the life of the process.
pub struct Configuration {
    main_module: String,
    syntax_module: String,
    grammar: &'static Grammar,
    assembler: ConfigurationAssembler<'static>,
    parser_modules: BTreeMap<String, String>,
    /// The module tried before the main module for each variable no `parser` attribute names
    /// ([`k_rust::kompile::variable_reading_modules`]).
    variable_modules: BTreeMap<String, String>,
    parsers: BTreeMap<String, ProgramParser>,
    ground_value_parser: Option<ProgramParser>,
    /// The parsers a print is read back with, [`Readings::Listed`]: copies of the two above
    /// that list an ambiguity's readings.
    listing_parsers: BTreeMap<String, ProgramParser>,
    listing_ground_value_parser: Option<ProgramParser>,
    macro_definition: MacroExpansionDefinition,
    /// What [`Self::read_token_in`] read, by grammar, KORE sort name and text.
    token_reads: BTreeMap<(Reader, String, String), Option<Pattern>>,
}

/// What a parse of an ambiguous text gives.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Readings {
    /// An error: the text must read one way.
    One,
    /// Each of its readings, where the parser lists them
    /// ([`ProgramParser::parse_readings`]).
    Listed,
}

/// One of the two grammars a printed term is read back with.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Reader {
    /// The syntax module's, the one a program is read with.
    Program,
    /// The main module's, which also has the builtin collections' syntax and the productions
    /// the partition placed in the semantics module.
    Main,
}

impl Configuration {
    /// Prepare the program grammar, configuration parser modules, and macros once per session.
    ///
    /// The grammar is leaked so that the assembler, which borrows it, can live in the session: a session loads one definition, once, for the life of its process.
    /// Values are typed over the frontend definition with the sort predicates and projections the definition generates in its main module (`with_sort_helpers`); text is parsed over the frontend definition.
    ///
    /// # Errors
    ///
    /// Returns an error when the prepared frontend definition cannot be resolved.
    pub fn new(
        frontend_definition: &Definition,
        configuration_variables: BTreeMap<String, KastSort>,
    ) -> Result<Self, Box<dyn Error>> {
        let main_module = frontend_definition.main_module.clone();
        let grammar: &'static Grammar = Box::leak(Box::new(Grammar {
            program: ProgramGrammar::new(&with_sort_helpers(frontend_definition)?)?,
            parsing: ProgramGrammar::new(frontend_definition)?,
            variables: configuration_variables,
        }));
        let resolved = grammar.program.resolved();
        let syntax_module = k_rust::outer::resolve_syntax_module(resolved, None)?.name;
        let parser_modules = parser_modules(resolved, &main_module)?;
        // The rule every tool reads a variable's text with (`variable_reading_modules`), which
        // the assembler applies itself; `parse_variable` reads with it too.
        let variable_modules = k_rust::kompile::variable_reading_modules(
            &grammar.program,
            &syntax_module,
            &grammar.variables,
        )?;
        let macro_definition = MacroExpansionDefinition::prepare(grammar.program.definition())?;
        let assembler = ConfigurationAssembler::new(
            &grammar.program,
            main_module.clone(),
            syntax_module.clone(),
            &grammar.variables,
        );
        Ok(Self {
            main_module,
            syntax_module,
            grammar,
            assembler,
            parser_modules,
            variable_modules,
            parsers: BTreeMap::new(),
            ground_value_parser: None,
            listing_parsers: BTreeMap::new(),
            listing_ground_value_parser: None,
            macro_definition,
            token_reads: BTreeMap::new(),
        })
    }

    fn parse_surface(
        &mut self,
        parser_module: &str,
        sort: &KastSort,
        source: &str,
        k_item: bool,
    ) -> Result<(Pattern, Sort), Box<dyn Error>> {
        let mut values =
            self.parse_surface_readings(parser_module, sort, source, k_item, Readings::One)?;
        Ok(values.swap_remove(0))
    }

    /// [`Self::parse_surface`], with `readings` saying whether an ambiguous text gives each of
    /// its listed readings ([`ProgramParser::parse_readings`]) or fails. Each value is the
    /// reading expanded, typed and converted as a parse's one value is.
    fn parse_surface_readings(
        &mut self,
        parser_module: &str,
        sort: &KastSort,
        source: &str,
        k_item: bool,
        readings: Readings,
    ) -> Result<Vec<(Pattern, Sort)>, Box<dyn Error>> {
        let resolved = self.grammar.program.resolved();
        let parse_sort = if sort.is_builtin(BuiltinSort::K) && k_item {
            KastSort::builtin(BuiltinSort::KItem)
        } else {
            sort.clone()
        };
        // A `K` cell holds a sequence, which only the ground K-value grammar reads; the value is injected at `K`, where a lone item is the one-item sequence the cell stores.
        let k_value = sort.is_builtin(BuiltinSort::K) && !k_item;
        let values = match (readings, k_value) {
            (Readings::One, true) => vec![self.ground_value_parser()?.parse(&parse_sort, source)?],
            (Readings::One, false) => vec![self.parser(parser_module)?.parse(&parse_sort, source)?],
            (Readings::Listed, true) => self
                .listing_ground_value_parser()?
                .parse_readings(&parse_sort, source)?,
            (Readings::Listed, false) => self
                .listing_parser(parser_module)?
                .parse_readings(&parse_sort, source)?,
        };
        let injector = SortInjector::new(resolved, &self.main_module)?;
        values
            .into_iter()
            .map(|value| {
                let value =
                    self.macro_definition
                        .expand_program(&self.main_module, value, &parse_sort)?;
                // Type the expanded value at the position it was expanded at, as the assembler does for a configuration value.
                let value_sort = if k_value {
                    sort.clone()
                } else {
                    injector.term_sort(value.term(), Some(value.position()))?
                };
                let value = injector.inject(value.term(), &value_sort)?;
                let value = term_to_kore_from_resolved_with_token_module(
                    resolved,
                    &self.main_module,
                    parser_module,
                    &value,
                )?;
                Ok((value, encode_kore_sort(&value_sort)))
            })
            .collect()
    }

    fn parse_variable(
        &mut self,
        name: &str,
        source: &str,
    ) -> Result<(Pattern, Sort), Box<dyn Error>> {
        let sort = self
            .grammar
            .variables
            .get(name)
            .ok_or_else(|| format!("definition has no configuration variable `${name}`"))?;
        // As the assembler reads it: a variable without a `parser` attribute is read with the
        // syntax module's grammar where it has the variable's sort, and with the main module's
        // where that one does not parse the text.
        let modules = if name == "PGM" {
            vec![self.syntax_module.clone()]
        } else if let Some(module) = self.parser_modules.get(name) {
            vec![module.clone()]
        } else {
            self.variable_modules
                .get(name)
                .cloned()
                .into_iter()
                .chain([self.main_module.clone()])
                .collect()
        };
        let mut read: Result<(Pattern, Sort), Box<dyn Error>> =
            Err("no module reads the variable".into());
        for module in modules {
            read = self.parse_surface(&module, sort, source, true);
            if read.is_ok() {
                break;
            }
        }
        read.map_err(|error| {
            format!("could not parse configuration variable `${name}` at sort {sort}: {error}")
                .into()
        })
    }

    /// Parse surface text at a cell's declared sort through the configuration frontend.
    ///
    /// # Errors
    ///
    /// Returns an error if the cell sort or surface term cannot be resolved.
    pub fn parse_cell(
        &mut self,
        cell: &str,
        sort: &KastSort,
        source: &str,
    ) -> Result<Pattern, Box<dyn Error>> {
        let mut values = self.parse_cell_readings(cell, sort, source, Readings::One)?;
        Ok(values.swap_remove(0))
    }

    /// [`Self::parse_cell`], with `readings` saying whether an ambiguous text gives each of its
    /// listed readings or fails.
    pub(crate) fn parse_cell_readings(
        &mut self,
        cell: &str,
        sort: &KastSort,
        source: &str,
        readings: Readings,
    ) -> Result<Vec<Pattern>, Box<dyn Error>> {
        let parser_module = self.main_module.clone();
        self.parse_surface_readings(&parser_module, sort, source, false, readings)
            .map(|values| values.into_iter().map(|(value, _)| value).collect())
            .map_err(|error| format!("could not parse <{cell}> at sort {sort}: {error}").into())
    }

    /// Parse a computation head and inject its declared sort into `KItem`.
    ///
    /// # Errors
    ///
    /// Returns an error when the surface head cannot be parsed.
    pub fn parse_head(&mut self, cell: &str, source: &str) -> Result<Pattern, Box<dyn Error>> {
        let mut values = self.parse_head_readings(cell, source, Readings::One)?;
        Ok(values.swap_remove(0))
    }

    /// [`Self::parse_head`], with `readings` saying whether an ambiguous text gives each of its
    /// listed readings or fails.
    pub(crate) fn parse_head_readings(
        &mut self,
        cell: &str,
        source: &str,
        readings: Readings,
    ) -> Result<Vec<Pattern>, Box<dyn Error>> {
        let parser_module = self.main_module.clone();
        let item_sort = KastSort::builtin(BuiltinSort::KItem);
        let values = self
            .parse_surface_readings(&parser_module, &item_sort, source, false, readings)
            .map_err(|error| format!("could not parse <{cell}> head: {error}"))?;
        let kore_item_sort = encode_kore_sort(&item_sort);
        Ok(values
            .into_iter()
            .map(|(value, value_sort)| {
                if value_sort == kore_item_sort {
                    value
                } else {
                    Pattern::Application {
                        symbol: Symbol {
                            name: "inj".to_owned(),
                            sort_parameters: vec![value_sort, kore_item_sort.clone()],
                        },
                        arguments: vec![value],
                    }
                }
            })
            .collect())
    }

    /// Assemble `initGeneratedTopCell` from surface text for the declared variables.
    ///
    /// [`ConfigurationAssembler`] binds `$PGM` first with the syntax module, and then the remaining names in lexical order.
    /// `$PGM` starts at its declared sort, or at `KItem` when it is declared `K`, as K's generated program parser does; krun takes this start sort from `--sort`.
    /// `$IO` and `$STDIN`, when declared and omitted, receive stream defaults with IO off and empty stdin.
    /// Each supplied variable is also rendered on its own through the surface pipeline that cell expectations use, for routes that pass a value as KORE.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown, missing, or non-text variable, or a surface parse failure.
    pub fn configure(&mut self, variables: &Map<String, Value>) -> Result<Value, Box<dyn Error>> {
        self.configure_pattern(variables)
            .map(|(_, configured)| configured)
    }

    /// [`Self::configure`], with the assembled pattern itself.
    pub(crate) fn configure_pattern(
        &mut self,
        variables: &Map<String, Value>,
    ) -> Result<(Pattern, Value), Box<dyn Error>> {
        self.assembler.clear();
        let configured = self.assemble(variables);
        if configured.is_err() {
            self.assembler.clear();
        }
        configured
    }

    fn assemble(
        &mut self,
        variables: &Map<String, Value>,
    ) -> Result<(Pattern, Value), Box<dyn Error>> {
        let mut names = variables.keys().collect::<Vec<_>>();
        names.sort_by_key(|name| (name.as_str() != "PGM", name.as_str()));
        let mut rendered = Map::new();
        for name in names {
            let source = variables[name]
                .as_str()
                .ok_or_else(|| format!("configuration variable `${name}` must be surface text"))?;
            if name == "PGM" {
                let sort = self
                    .grammar
                    .variables
                    .get(name)
                    .ok_or("definition has no configuration variable `$PGM`")?;
                self.assembler
                    .program(&program_start_position(sort), source)?;
            } else {
                self.assembler.bind(name, source)?;
            }
            let (value, sort) = self.parse_variable(name, source)?;
            rendered.insert(
                name.clone(),
                json!({"sort": sort.to_string(), "kore": value.to_string()}),
            );
        }
        self.assembler
            .bind_stream_defaults(false, true, || Ok::<_, ConfigurationError>(Vec::new()))?;
        let pattern = self.assembler.finish()?;
        let configured = json!({"pattern": pattern.to_string(), "variables": rendered});
        Ok((pattern, configured))
    }

    /// The declared configuration variables (K names without `$`) and their sorts.
    #[must_use]
    pub fn variables(&self) -> &BTreeMap<String, KastSort> {
        &self.grammar.variables
    }

    /// The module whose grammar parses programs (`$PGM` and `krs parse`).
    #[must_use]
    pub fn syntax_module(&self) -> &str {
        &self.syntax_module
    }

    /// Assemble `initGeneratedTopCell` from a program and other variable texts, as krun does.
    ///
    /// `program` binds `$PGM`, as text parsed as a program or as a term; `variables` holds K
    /// names without `$`.
    /// The caller has already checked every name against [`Self::variables`].
    /// Declared `$IO` and `$STDIN` that are not supplied receive the stream defaults with IO off;
    /// `$STDIN` is `stdin` (already buffered as krun buffers it) or empty.
    ///
    /// # Errors
    ///
    /// Returns the assembler's typed error for a parse failure or a missing variable.
    pub(crate) fn assemble_pattern(
        &mut self,
        program: Option<&Binding>,
        variables: &BTreeMap<String, Binding>,
        stdin: Option<&[u8]>,
    ) -> Result<Pattern, AssemblyError> {
        self.assembler.clear();
        let result = self.assemble_typed(program, variables, stdin);
        self.assembler.clear();
        result
    }

    fn assemble_typed(
        &mut self,
        program: Option<&Binding>,
        variables: &BTreeMap<String, Binding>,
        stdin: Option<&[u8]>,
    ) -> Result<Pattern, AssemblyError> {
        match program {
            Some(Binding::Text(source)) => {
                let start_sort = self.grammar.variables.get("PGM").map_or_else(
                    || KastSort::builtin(BuiltinSort::KItem),
                    program_start_position,
                );
                self.assembler.program(&start_sort, source)?;
            }
            Some(Binding::Term(term)) => {
                if let Err(error) = self.assembler.program_term(term.clone()) {
                    return Err(AssemblyError::Value {
                        variable: "PGM".to_owned(),
                        error: Box::new(error),
                    });
                }
            }
            None => {}
        }
        for (name, binding) in variables {
            match binding {
                Binding::Text(source) => self.assembler.bind(name, source)?,
                Binding::Term(term) => {
                    if let Err(error) = self.assembler.bind_term(name, term.clone()) {
                        return Err(AssemblyError::Value {
                            variable: name.clone(),
                            error: Box::new(error),
                        });
                    }
                }
            }
        }
        // `program_uses_input` true binds an empty `$STDIN`; false binds the supplied bytes.
        self.assembler
            .bind_stream_defaults(false, stdin.is_none(), || {
                Ok::<_, ConfigurationError>(stdin.map(<[u8]>::to_vec).unwrap_or_default())
            })?;
        Ok(self.assembler.finish()?)
    }

    /// The term `printed`, a token's printed text, reads as at a position of sort `position`:
    /// parsed there alone with the syntax module's grammar, the one a program is read with
    /// ([`Self::read_token_in`]).
    pub(crate) fn read_token(&mut self, position: &Sort, printed: &str) -> Option<Pattern> {
        self.read_token_in(Reader::Program, position, printed)
    }

    /// The term `printed`, a token's printed text, reads as at a position of sort `position`:
    /// parsed there alone with `grammar`, its aliases expanded, and without the injection the
    /// position puts around it. The scanner reads a token whatever the parse expects there, so
    /// the text alone reads as it does inside a printed term, unless the token sort's regex can
    /// take in what is printed after it ([`crate::reversal`]).
    ///
    /// `None` where the text does not parse there, and where the position cannot be judged: a
    /// sort with parameters, which no `--sort` names, or a KORE name that is not the encoding of a
    /// K sort's name.
    pub(crate) fn read_token_in(
        &mut self,
        grammar: Reader,
        position: &Sort,
        printed: &str,
    ) -> Option<Pattern> {
        let Sort::Application { name, arguments } = position else {
            return None;
        };
        let kast = name
            .strip_prefix("Sort")
            .filter(|_| arguments.is_empty())
            .map(|name| KastSort::new(krs_unparse::decode_kore(name)))
            .filter(|kast| encode_kore_sort(kast) == *position)?;
        let key = (grammar, name.clone(), printed.to_owned());
        if let Some(read) = self.token_reads.get(&key) {
            return read.clone();
        }
        let module = self.module(grammar).to_owned();
        let read = self
            .parse_surface(&module, &kast, printed, false)
            .ok()
            .map(|(value, _)| without_injection(&value).clone());
        self.token_reads.insert(key, read.clone());
        read
    }

    /// Whether the syntax module's grammar, the one a program is read with, has a production
    /// that applies `symbol` ([`Self::writes_symbol_in`]).
    pub(crate) fn writes_symbol(&mut self, symbol: &str) -> Result<bool, Box<dyn Error>> {
        self.writes_symbol_in(Reader::Program, symbol)
    }

    /// Whether `grammar` has a production that applies `symbol`, a KORE symbol name
    /// (`LblSetItem`): whether its text can write an application of it. The syntax module's
    /// grammar has no builtin collection's constructors (K supplies them only with a full
    /// module), nor a production the partition placed in the semantics module; the main
    /// module's has both. A name that encodes no K label is written by neither.
    ///
    /// # Errors
    ///
    /// Returns the error that building the grammar's parser met.
    pub(crate) fn writes_symbol_in(
        &mut self,
        grammar: Reader,
        symbol: &str,
    ) -> Result<bool, Box<dyn Error>> {
        let Ok(label) = k_rust::kast::identifier::decode_label(symbol) else {
            return Ok(false);
        };
        let module = self.module(grammar).to_owned();
        Ok(self.parser(&module)?.has_label(&label))
    }

    /// The module whose grammar `grammar` is.
    fn module(&self, grammar: Reader) -> &str {
        match grammar {
            Reader::Program => &self.syntax_module,
            Reader::Main => &self.main_module,
        }
    }

    /// Parse program text at `sort` with the syntax module's grammar, as `kast --sort` does.
    ///
    /// # Errors
    ///
    /// Returns an error when the parser cannot be built or the text does not parse.
    pub fn parse_program(
        &mut self,
        sort: &KastSort,
        source: &str,
    ) -> Result<PresentedProgram, Box<dyn Error>> {
        let parser_module = self.syntax_module.clone();
        let parser = self.parser(&parser_module)?;
        Ok(parser.parse_for_presentation(sort, source)?)
    }

    /// Parse program text at `sort` once, and lower the one reading both ways: with its macros
    /// as parsed, the term `kast --output program` prints, and expanded, as
    /// [`Self::parse_program_kore`] does, the value the program is. A print of the first is read
    /// back as the second, so both come from one parse.
    ///
    /// # Errors
    ///
    /// Returns an error when the text does not parse or cannot be lowered.
    pub fn parse_program_forms(
        &mut self,
        sort: &KastSort,
        source: &str,
    ) -> Result<(Pattern, Pattern), Box<dyn Error>> {
        let parser_module = self.syntax_module.clone();
        let parse_sort = if sort.is_builtin(BuiltinSort::K) {
            KastSort::builtin(BuiltinSort::KItem)
        } else {
            sort.clone()
        };
        let parser = self.parser(&parser_module)?;
        let program = parser.parse(&parse_sort, source)?;
        let presented = parser.present(program.clone());
        let resolved = self.grammar.program.resolved();
        let injector = SortInjector::new(resolved, &self.main_module)?;
        let presented_sort = injector.term_sort(presented.term(), Some(sort))?;
        let presented = injector.inject(presented.term(), &presented_sort)?;
        let presented = term_to_kore_from_resolved_with_token_module(
            resolved,
            &self.main_module,
            &self.syntax_module,
            &presented,
        )?;
        let value =
            self.macro_definition
                .expand_program(&self.main_module, program, &parse_sort)?;
        let value_sort = injector.term_sort(value.term(), Some(value.position()))?;
        let value = injector.inject(value.term(), &value_sort)?;
        let expanded = term_to_kore_from_resolved_with_token_module(
            resolved,
            &self.main_module,
            &parser_module,
            &value,
        )?;
        Ok((presented, expanded))
    }

    /// Parse program text at `sort` and lower it to KORE through the configuration pipeline, as `kast --output kore` does.
    ///
    /// # Errors
    ///
    /// Returns an error when the text does not parse or cannot be lowered.
    pub fn parse_program_kore(
        &mut self,
        sort: &KastSort,
        source: &str,
    ) -> Result<Pattern, Box<dyn Error>> {
        let parser_module = self.syntax_module.clone();
        self.parse_surface(&parser_module, sort, source, true)
            .map(|(value, _)| value)
    }

    /// Every sort visible to the program grammar, by name.
    #[must_use]
    pub fn program_sorts(&self) -> BTreeSet<String> {
        program_sorts(&self.grammar.parsing, &self.syntax_module)
    }

    fn parser(&mut self, parser_module: &str) -> Result<&ProgramParser, Box<dyn Error>> {
        let resolved = self.grammar.parsing.resolved();
        if resolved.module_id(parser_module).is_none() {
            return Err(format!("parser module `{parser_module}` was not found").into());
        }
        if !self.parsers.contains_key(parser_module) {
            self.parsers.insert(
                parser_module.to_owned(),
                ProgramParser::from_resolved(resolved, parser_module)?,
            );
        }
        Ok(self
            .parsers
            .get(parser_module)
            .expect("parser was inserted above"))
    }

    /// [`Self::parser`], listing an ambiguity's readings.
    fn listing_parser(&mut self, parser_module: &str) -> Result<&ProgramParser, Box<dyn Error>> {
        if !self.listing_parsers.contains_key(parser_module) {
            let parser = self.parser(parser_module)?.clone().listing_readings();
            self.listing_parsers
                .insert(parser_module.to_owned(), parser);
        }
        Ok(self
            .listing_parsers
            .get(parser_module)
            .expect("parser was inserted above"))
    }

    /// [`Self::ground_value_parser`], listing an ambiguity's readings.
    fn listing_ground_value_parser(&mut self) -> Result<&ProgramParser, Box<dyn Error>> {
        if self.listing_ground_value_parser.is_none() {
            self.listing_ground_value_parser =
                Some(self.ground_value_parser()?.clone().listing_readings());
        }
        Ok(self
            .listing_ground_value_parser
            .as_ref()
            .expect("parser was built above"))
    }

    /// The ground K-value parser of the main module, built on first use.
    fn ground_value_parser(&mut self) -> Result<&ProgramParser, Box<dyn Error>> {
        if self.ground_value_parser.is_none() {
            self.ground_value_parser = Some(ProgramParser::for_ground_values(
                self.grammar.parsing.resolved(),
                &self.main_module,
            )?);
        }
        Ok(self
            .ground_value_parser
            .as_ref()
            .expect("parser was built above"))
    }
}

/// Every sort visible to the grammar of `module`, by name.
fn program_sorts(grammar: &ProgramGrammar, module: &str) -> BTreeSet<String> {
    let resolved = grammar.resolved();
    let Some(module) = resolved.module_id(module) else {
        return BTreeSet::new();
    };
    resolved
        .sentences(module)
        .into_iter()
        .filter_map(|sentence| match sentence {
            Sentence::SyntaxSort { sort, .. } | Sentence::Production { sort, .. } => {
                Some(sort.name.clone())
            }
            _ => None,
        })
        .collect()
}

/// `pattern` without the injection at its root, if it has one.
fn without_injection(pattern: &Pattern) -> &Pattern {
    match pattern {
        Pattern::Application { symbol, arguments }
            if symbol.name == "inj" && arguments.len() == 1 =>
        {
            &arguments[0]
        }
        _ => pattern,
    }
}

#[cfg(test)]
mod tests {
    use super::{AssemblyError, Binding, Configuration};
    use k_rust::kore::ast::Pattern;
    use k_rust::{
        definition::{Definition, Sentence},
        kast::Sort,
        names::BuiltinSort,
    };
    use serde_json::json;
    use std::collections::BTreeMap;

    #[test]
    fn k_cell_expectations_read_sequences_with_the_ground_value_grammar() {
        let parsed = k_rust::outer::parse(
            "sequence.k",
            r#"
module MAIN
  imports BASIC-K
  imports STRING-SYNTAX
  syntax Item ::= "a" [symbol(a)] | "b" [symbol(b)] | f(String) [symbol(f)]
  configuration <k> $PGM:K </k>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([("PGM".to_owned(), Sort::builtin(BuiltinSort::K))]),
        )
        .unwrap();
        let k = Sort::builtin(BuiltinSort::K);
        let mut cell = |source| {
            configuration
                .parse_cell("k", &k, source)
                .unwrap()
                .to_string()
        };
        let a = "kseq{}(inj{SortItem{}, SortKItem{}}(Lbla{}()), dotk{}())";
        assert_eq!(cell("a"), a);
        assert_eq!(cell("a ~> .K"), a);
        assert_eq!(cell(".K"), "dotk{}()");
        assert_eq!(
            cell("a ~> b"),
            "kseq{}(inj{SortItem{}, SortKItem{}}(Lbla{}()), kseq{}(inj{SortItem{}, SortKItem{}}(Lblb{}()), dotk{}()))"
        );
        // A `~>` inside a string token is not a sequence delimiter.
        assert_eq!(
            cell(r#"f("~>") ~> a"#),
            format!(
                r#"kseq{{}}(inj{{SortItem{{}}, SortKItem{{}}}}(Lblf{{}}(\dv{{SortString{{}}}}("~>"))), {a})"#
            )
        );
    }

    /// A token's printed text reads, alone at its position with the program grammar, as the token
    /// it names: a byte string as its bytes, a `Word` at its own sort as that `Word`, a float as
    /// the literal it is. Text that does not parse there reads as nothing, and so does any text at
    /// a position that cannot be judged: a sort variable, a sort with parameters, and a KORE name
    /// that encodes no K sort's name.
    #[test]
    fn a_token_reads_only_at_a_position_that_can_be_judged() {
        let parsed = k_rust::outer::parse(
            "tokens.k",
            r#"
module MAIN
  imports INT
  imports BYTES
  imports FLOAT
  imports BASIC-K
  syntax Word ::= r"w[a-z]*" [token]
  syntax Item ::= w(Word) [symbol(w)]
  configuration <k> $PGM:K </k>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([("PGM".to_owned(), Sort::builtin(BuiltinSort::K))]),
        )
        .unwrap();
        let sort = |text: &str| match &k_rust::kore::parser::parse_pattern(&format!(
            r#"\dv{{{text}}}("1")"#
        ))
        .unwrap()
        {
            Pattern::DomainValue { sort, .. } => sort.clone(),
            other => panic!("{other}"),
        };
        let mut read = |position: &str, printed: &str| {
            configuration
                .read_token(&sort(position), printed)
                .map(|read| read.to_string())
        };
        assert_eq!(
            read("SortBytes{}", r#"b"a\"b""#).as_deref(),
            Some(r#"\dv{SortBytes{}}("a\"b")"#)
        );
        assert_eq!(
            read("SortWord{}", "word").as_deref(),
            Some(r#"\dv{SortWord{}}("word")"#)
        );
        assert_eq!(
            read("SortKItem{}", "0.15000000000000000e1").as_deref(),
            Some(r#"\dv{SortFloat{}}("0.15000000000000000e1")"#)
        );
        assert_eq!(read("SortInt{}", "$x"), None);
        assert_eq!(read("S", "1"), None);
        assert_eq!(read("SortInt{SortInt{}}", "1"), None);
        assert_eq!(read("SortInt''{}", "1"), None);
        assert_eq!(
            read("SortInt{}", "1").as_deref(),
            Some(r#"\dv{SortInt{}}("1")"#)
        );
    }

    #[test]
    fn configure_assembles_through_the_upstream_assembler_and_recovers_after_errors() {
        let parsed = k_rust::outer::parse(
            "configure.k",
            r#"
module MAIN
  imports INT
  imports BASIC-K
  syntax Pgm ::= "run" [symbol(run)]
  configuration <k> $PGM:Pgm </k> <n> $N:Int </n>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([
                ("PGM".to_owned(), Sort::new("Pgm")),
                ("N".to_owned(), Sort::builtin(BuiltinSort::Int)),
            ]),
        )
        .unwrap();
        let unknown = configuration
            .configure(json!({"PGM": "run", "EXTRA": "1"}).as_object().unwrap())
            .unwrap_err();
        assert!(unknown.to_string().contains("$EXTRA"), "{unknown}");
        let missing = configuration
            .configure(json!({"PGM": "run"}).as_object().unwrap())
            .unwrap_err();
        assert!(missing.to_string().contains("$N"), "{missing}");
        let configured = configuration
            .configure(json!({"PGM": "run", "N": "3"}).as_object().unwrap())
            .unwrap();
        let pattern = configured["pattern"].as_str().unwrap();
        assert!(
            pattern.starts_with("LblinitGeneratedTopCell{}("),
            "{pattern}"
        );
        assert!(
            pattern.contains("\\dv{SortKConfigVar{}}(\"$PGM\")"),
            "{pattern}"
        );
        assert!(
            pattern.contains("\\dv{SortKConfigVar{}}(\"$N\")"),
            "{pattern}"
        );
        assert_eq!(configured["variables"]["N"]["sort"], "SortInt{}");
        assert_eq!(
            configured["variables"]["N"]["kore"],
            "\\dv{SortInt{}}(\"3\")"
        );
        assert_eq!(configured["variables"]["PGM"]["sort"], "SortPgm{}");
    }

    /// `$PGM` bound to a term without the parser denotes what its text denotes, and a term of a
    /// sort that is not at most `$PGM`'s is refused as the value it is.
    #[test]
    fn a_program_bound_as_a_term_is_the_program_its_text_parses_to() {
        let parsed = k_rust::outer::parse(
            "program-term.k",
            r#"
module MAIN
  imports INT
  imports BASIC-K
  syntax Pgm ::= "run" [symbol(run)]
  configuration <k> $PGM:Pgm </k> <n> $N:Int </n>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([
                ("PGM".to_owned(), Sort::new("Pgm")),
                ("N".to_owned(), Sort::builtin(BuiltinSort::Int)),
            ]),
        )
        .unwrap();
        let n = BTreeMap::from([("N".to_owned(), Binding::Text("3".to_owned()))]);
        let from_text = configuration
            .assemble_pattern(Some(&Binding::Text("run".to_owned())), &n, None)
            .unwrap();
        let from_term = configuration
            .assemble_pattern(
                Some(&Binding::Term(k_rust::kast::Term::apply("run", Vec::new()))),
                &n,
                None,
            )
            .unwrap();
        assert_eq!(from_term, from_text);
        let three = k_rust::kast::Term::Token {
            token: "3".to_owned(),
            sort: Sort::builtin(BuiltinSort::Int),
        };
        let refused = configuration
            .assemble_pattern(Some(&Binding::Term(three)), &n, None)
            .unwrap_err();
        assert!(
            matches!(&refused, AssemblyError::Value { variable, .. } if variable == "PGM"),
            "{refused:?}"
        );
    }

    /// A configuration variable is input, read as a program is, with the syntax module's grammar
    /// wherever it has the variable's sort: `word` given for a `Word` variable is that `Word`,
    /// although the main module's grammar, whose token sort `Name` the scanner prefers, reads it
    /// as a `Name`. A sort only the main module has (here `Name`) is read with its grammar, and so
    /// is a value the syntax module's grammar does not parse: one written with a production of
    /// the semantics module (`two`) or a builtin collection's constructor (`SetItem`, `.Map`).
    #[test]
    fn a_configuration_variable_is_read_with_the_grammar_a_program_is_read_with() {
        let parsed = k_rust::outer::parse(
            "variables.k",
            r#"
module MAIN-SYNTAX
  imports INT-SYNTAX
  syntax Word ::= r"w[a-z]*" [token]
  syntax Pgm ::= "run" [symbol(run)]
  syntax Data ::= one(Int) [symbol(one)]
endmodule

module MAIN
  imports MAIN-SYNTAX
  imports BASIC-K
  imports INT
  imports LIST
  imports SET
  imports MAP
  syntax Name ::= r"wor[a-z]*" [token, prec(2)]
  syntax Data ::= two(Int, List) [symbol(two)]
  configuration <k> $PGM:Pgm </k> <w> $W:Word </w> <n> $N:Name </n> <d> $D:Data </d>
                <e> $E:Data </e> <s> $S:KItem </s> <m> $M:KItem </m>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([
                ("PGM".to_owned(), Sort::new("Pgm")),
                ("W".to_owned(), Sort::new("Word")),
                ("N".to_owned(), Sort::new("Name")),
                ("D".to_owned(), Sort::new("Data")),
                ("E".to_owned(), Sort::new("Data")),
                ("S".to_owned(), Sort::builtin(BuiltinSort::KItem)),
                ("M".to_owned(), Sort::builtin(BuiltinSort::KItem)),
            ]),
        )
        .unwrap();
        let configured = configuration
            .configure(
                json!({
                    "PGM": "run",
                    "W": "word",
                    "N": "word",
                    "D": "two(1, .List)",
                    "E": "one(2)",
                    "S": "SetItem(1)",
                    "M": ".Map",
                })
                .as_object()
                .unwrap(),
            )
            .unwrap();
        let variable = |name: &str| configured["variables"][name]["kore"].as_str().unwrap();
        assert!(variable("D").starts_with("Lbltwo{}("), "{}", variable("D"));
        assert!(variable("E").starts_with("Lblone{}("), "{}", variable("E"));
        assert!(variable("S").contains("LblSetItem{}("), "{}", variable("S"));
        assert!(
            variable("M").contains("Lbl'Stop'Map{}()"),
            "{}",
            variable("M")
        );
        assert_eq!(
            configured["variables"]["W"]["kore"],
            "\\dv{SortWord{}}(\"word\")"
        );
        assert_eq!(
            configured["variables"]["N"]["kore"],
            "\\dv{SortName{}}(\"word\")"
        );
        let pattern = configured["pattern"].as_str().unwrap();
        assert!(pattern.contains("\\dv{SortWord{}}(\"word\")"), "{pattern}");
    }

    /// A printed cell is read back with the main module's grammar where it is no program text,
    /// and that grammar may read the print several ways: `size ( SetItem ( 1 ) )` is the
    /// definition's `size` over an item and the set's `size`. Read for a read-back, the text
    /// gives both readings, so a state holding either reads back; read as a program or a value
    /// the user writes, it is an ambiguity. A map whose key is a map has no text at all: `_|->_`
    /// is non-associative and no bracket groups a map there, so `( 1 |-> 2 ) |-> 0` does not
    /// parse (the printer reports its K default bracket: `Printed::grouped`).
    #[test]
    fn a_read_back_lists_the_readings_of_an_ambiguous_print() {
        let parsed = k_rust::outer::parse(
            "readings.k",
            r#"
module MAIN-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "run" [symbol(run)]
endmodule

module MAIN
  imports MAIN-SYNTAX
  imports BASIC-K
  imports INT
  imports SET
  imports MAP
  syntax KItem ::= hold(KItem) [symbol(hold)]
  syntax Int ::= size(KItem) [function, symbol(Size)]
  configuration <k> $PGM:Pgm </k> <env> .Map </env>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([("PGM".to_owned(), Sort::new("Pgm"))]),
        )
        .unwrap();
        let text = "hold(size ( SetItem ( 1 ) ))";
        let readings = configuration
            .parse_head_readings("k", text, super::Readings::Listed)
            .unwrap()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        assert_eq!(readings.len(), 2, "{readings:#?}");
        assert!(
            readings
                .iter()
                .any(|reading| reading
                    .contains("LblSize{}(inj{SortSet{}, SortKItem{}}(LblSetItem{}(")),
            "{readings:#?}"
        );
        assert!(
            readings
                .iter()
                .any(|reading| !reading.contains("LblSize{}")),
            "{readings:#?}"
        );
        let error = configuration.parse_head("k", text).unwrap_err().to_string();
        assert!(error.contains("Parsing ambiguity"), "{error}");
        let error = configuration
            .parse_cell_readings(
                "env",
                &Sort::builtin(BuiltinSort::Map),
                "( 1 |-> 2 ) |-> 0",
                super::Readings::Listed,
            )
            .unwrap_err()
            .to_string();
        assert!(error.contains("unexpected token '('"), "{error}");
    }

    #[test]
    fn configure_starts_a_k_declared_program_at_kitem() {
        let parsed = k_rust::outer::parse(
            "program.k",
            r#"
module MAIN
  syntax Command ::= "run" [symbol(run)]
  configuration <k> $PGM:K </k>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([("PGM".to_owned(), Sort::builtin(BuiltinSort::K))]),
        )
        .unwrap();
        let configured = configuration
            .configure(json!({"PGM": "run"}).as_object().unwrap())
            .unwrap();
        let pattern = configured["pattern"].as_str().unwrap();
        assert!(pattern.contains("Lblrun{}()"), "{pattern}");
    }

    /// The instance cell of the Map collection `row` is the only generator of its sort, so the
    /// compiled definition marks the collection's key projection `RowCellMapKey` total, an
    /// attribute on a production the frontend already declares. The program grammar is the
    /// frontend's with the sort helpers added: the definition loads, the key projection is the
    /// frontend's own, and `isInt` is declared in the main module.
    #[test]
    fn a_map_cell_collection_whose_key_projection_is_total_loads() {
        let parsed = k_rust::outer::parse(
            "rows.k",
            r#"
module MAIN
  imports INT
  imports MAP
  imports BASIC-K
  syntax Pgm ::= "run" [symbol(run)]
  configuration <k> $PGM:Pgm </k>
                <rows> <row multiplicity="*" type="Map"> <id> 0 </id> <v> 0 </v> </row> </rows>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let mut configuration = Configuration::new(
            loaded.definition(),
            BTreeMap::from([("PGM".to_owned(), Sort::new("Pgm"))]),
        )
        .unwrap();
        let main = |definition: &Definition| {
            definition
                .modules
                .iter()
                .find(|module| module.name == definition.main_module)
                .unwrap()
                .local_sentences
                .clone()
        };
        let label = |sentence: &Sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            _ => None,
        };
        let program = main(configuration.grammar.program.definition());
        let frontend = main(loaded.definition());
        let key = |sentences: &[std::sync::Arc<Sentence>]| {
            sentences
                .iter()
                .find(|sentence| label(sentence).as_deref() == Some("RowCellMapKey"))
                .cloned()
                .unwrap()
        };
        assert_eq!(key(&program), key(&frontend));
        assert!(
            program
                .iter()
                .any(|sentence| label(sentence).as_deref() == Some("isInt")),
        );
        let configured = configuration
            .configure(json!({"PGM": "run"}).as_object().unwrap())
            .unwrap();
        let pattern = configured["pattern"].as_str().unwrap();
        assert!(pattern.contains("Lblrun{}()"), "{pattern}");
    }
}
