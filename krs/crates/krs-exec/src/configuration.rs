//! Parse configuration and cell-expectation text through k-rust's program pipeline.
//! [`k_rust::kompile::ConfigurationAssembler`] owns krun's `-c` assembly of `initGeneratedTopCell`; this module adds the per-value surface parsing that cell expectations and the Java route's per-variable KORE need.
//! A program parser has no K sequence syntax, so a `K`-sorted cell expectation (`trap ~> .Instrs`) is read by a ground K-value parser ([`ProgramParser::for_ground_values`]): the main module's program grammar plus exactly `.K`, `K ~> K`, and a K bracket.

use k_rust::{
    definition::{Definition, Sentence},
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

/// The program grammar and declared variable sorts that every configuration of one loaded definition is assembled against.
struct Grammar {
    program: ProgramGrammar,
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
    parsers: BTreeMap<String, ProgramParser>,
    ground_value_parser: Option<ProgramParser>,
    macro_definition: MacroExpansionDefinition,
}

impl Configuration {
    /// Prepare the program grammar, configuration parser modules, and macros once per session.
    ///
    /// The grammar is leaked so that the assembler, which borrows it, can live in the session: a session loads one definition, once, for the life of its process.
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
            program: ProgramGrammar::new(frontend_definition)?,
            variables: configuration_variables,
        }));
        let resolved = grammar.program.resolved();
        let syntax_module = k_rust::outer::resolve_syntax_module(resolved, None)?.name;
        let parser_modules = parser_modules(resolved, &main_module)?;
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
            parsers: BTreeMap::new(),
            ground_value_parser: None,
            macro_definition,
        })
    }

    fn parse_surface(
        &mut self,
        parser_module: &str,
        sort: &KastSort,
        source: &str,
        k_item: bool,
    ) -> Result<(Pattern, Sort), Box<dyn Error>> {
        let resolved = self.grammar.program.resolved();
        self.parser(parser_module)?;
        let parse_sort = if sort.is_builtin(BuiltinSort::K) && k_item {
            KastSort::builtin(BuiltinSort::KItem)
        } else {
            sort.clone()
        };
        // A `K` cell holds a sequence, which only the ground K-value grammar reads; the value is injected at `K`, where a lone item is the one-item sequence the cell stores.
        let k_value = sort.is_builtin(BuiltinSort::K) && !k_item;
        let value = if k_value {
            self.ground_value_parser()?.parse(sort, source)?
        } else {
            self.parsers
                .get(parser_module)
                .expect("parser was inserted above")
                .parse(&parse_sort, source)?
        };
        let value = self
            .macro_definition
            .expand_program(&self.main_module, value, &parse_sort)?;
        // Type the expanded value at the position it was expanded at, as the assembler does for a configuration value.
        let injector = SortInjector::new(resolved, &self.main_module)?;
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
        let parser_module = if name == "PGM" {
            &self.syntax_module
        } else {
            self.parser_modules.get(name).unwrap_or(&self.main_module)
        }
        .clone();
        self.parse_surface(&parser_module, sort, source, true)
            .map_err(|error| {
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
        let parser_module = self.main_module.clone();
        self.parse_surface(&parser_module, sort, source, false)
            .map(|(value, _)| value)
            .map_err(|error| format!("could not parse <{cell}> at sort {sort}: {error}").into())
    }

    /// Parse a computation head and inject its declared sort into `KItem`.
    ///
    /// # Errors
    ///
    /// Returns an error when the surface head cannot be parsed.
    pub fn parse_head(&mut self, cell: &str, source: &str) -> Result<Pattern, Box<dyn Error>> {
        let parser_module = self.main_module.clone();
        let item_sort = KastSort::builtin(BuiltinSort::KItem);
        let (value, value_sort) = self
            .parse_surface(&parser_module, &item_sort, source, false)
            .map_err(|error| format!("could not parse <{cell}> head: {error}"))?;
        let kore_item_sort = encode_kore_sort(&item_sort);
        if value_sort == kore_item_sort {
            Ok(value)
        } else {
            Ok(Pattern::Application {
                symbol: Symbol {
                    name: "inj".to_owned(),
                    sort_parameters: vec![value_sort, kore_item_sort],
                },
                arguments: vec![value],
            })
        }
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
        self.assembler.clear();
        let configured = self.assemble(variables);
        if configured.is_err() {
            self.assembler.clear();
        }
        configured
    }

    fn assemble(&mut self, variables: &Map<String, Value>) -> Result<Value, Box<dyn Error>> {
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
        Ok(json!({"pattern": pattern.to_string(), "variables": rendered}))
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
    /// `program` binds `$PGM`; `variables` holds K names without `$`.
    /// The caller has already checked every name against [`Self::variables`].
    /// Declared `$IO` and `$STDIN` that are not supplied receive the stream defaults with IO off;
    /// `$STDIN` is `stdin` (already buffered as krun buffers it) or empty.
    ///
    /// # Errors
    ///
    /// Returns the assembler's typed error for a parse failure or a missing variable.
    pub fn assemble_pattern(
        &mut self,
        program: Option<&str>,
        variables: &BTreeMap<String, String>,
        stdin: Option<&[u8]>,
    ) -> Result<Pattern, ConfigurationError> {
        self.assembler.clear();
        let result = self.assemble_typed(program, variables, stdin);
        self.assembler.clear();
        result
    }

    fn assemble_typed(
        &mut self,
        program: Option<&str>,
        variables: &BTreeMap<String, String>,
        stdin: Option<&[u8]>,
    ) -> Result<Pattern, ConfigurationError> {
        if let Some(source) = program {
            let start_sort = self.grammar.variables.get("PGM").map_or_else(
                || KastSort::builtin(BuiltinSort::KItem),
                program_start_position,
            );
            self.assembler.program(&start_sort, source)?;
        }
        for (name, source) in variables {
            self.assembler.bind(name, source)?;
        }
        // `program_uses_input` true binds an empty `$STDIN`; false binds the supplied bytes.
        self.assembler
            .bind_stream_defaults(false, stdin.is_none(), || {
                Ok::<_, ConfigurationError>(stdin.map(<[u8]>::to_vec).unwrap_or_default())
            })?;
        self.assembler.finish()
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

    /// Parse program text at `sort` and lower it to KORE with its macros as parsed: the term `kast --output program` prints.
    ///
    /// # Errors
    ///
    /// Returns an error when the text does not parse or cannot be lowered.
    pub fn parse_program_presented_kore(
        &mut self,
        sort: &KastSort,
        source: &str,
    ) -> Result<Pattern, Box<dyn Error>> {
        let presented = self.parse_program(sort, source)?;
        let resolved = self.grammar.program.resolved();
        let injector = SortInjector::new(resolved, &self.main_module)?;
        let value_sort = injector.term_sort(presented.term(), Some(sort))?;
        let value = injector.inject(presented.term(), &value_sort)?;
        Ok(term_to_kore_from_resolved_with_token_module(
            resolved,
            &self.main_module,
            &self.syntax_module,
            &value,
        )?)
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
        let resolved = self.grammar.program.resolved();
        let Some(module) = resolved.module_id(&self.syntax_module) else {
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

    fn parser(&mut self, parser_module: &str) -> Result<&ProgramParser, Box<dyn Error>> {
        let resolved = self.grammar.program.resolved();
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

    /// The ground K-value parser of the main module, built on first use.
    fn ground_value_parser(&mut self) -> Result<&ProgramParser, Box<dyn Error>> {
        if self.ground_value_parser.is_none() {
            self.ground_value_parser = Some(ProgramParser::for_ground_values(
                self.grammar.program.resolved(),
                &self.main_module,
            )?);
        }
        Ok(self
            .ground_value_parser
            .as_ref()
            .expect("parser was built above"))
    }
}

#[cfg(test)]
mod tests {
    use super::Configuration;
    use k_rust::{kast::Sort, names::BuiltinSort};
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
}
