//! Parse configuration and cell-expectation text through k-rust's program pipeline.
//! [`k_rust::kompile::ConfigurationAssembler`] owns krun's `-c` assembly of `initGeneratedTopCell`; this module adds the per-value surface parsing that cell expectations and the Java route's per-variable KORE need.
//! `ProgramParser` uses visible program productions and adds `KItem` subsorts, but does not add the implicit `KSEQ` productions `K ::= ".K"` and `K ::= K "~>" K`.
//! `BASIC-K` supplies the subsort path for a single item at `K`, but supplies neither sequence production.
//! Cell expectations must therefore split top-level sequence delimiters outside quoted strings, parse each item at `KItem`, and assemble `Term::sequence`.

use k_rust::{
    definition::{Definition, Sentence},
    inner::{ParsedProgram, PresentedProgram, ProgramParser},
    kast::{Sort as KastSort, Term},
    kompile::{
        ConfigurationAssembler, ConfigurationError, MacroExpansionDefinition, ProgramGrammar,
        SortInjector, encode_kore_sort, initial_configuration::parser_modules,
        term_to_kore_from_resolved_with_token_module,
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
    macro_definition: MacroExpansionDefinition,
}

fn split_k_sequence(source: &str) -> Result<Option<Vec<&str>>, String> {
    let mut items = Vec::new();
    let mut start = 0;
    let mut depth = 0_u32;
    let mut quoted = false;
    let mut escaped = false;
    let mut chars = source.char_indices().peekable();
    while let Some((index, character)) = chars.next() {
        if quoted {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                quoted = false;
            }
            continue;
        }
        match character {
            '"' => quoted = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or("unbalanced K sequence delimiters")?;
            }
            '~' if depth == 0 && chars.peek().is_some_and(|(_, next)| *next == '>') => {
                chars.next();
                let item = source[start..index].trim();
                if item.is_empty() {
                    return Err("empty K sequence item".into());
                }
                items.push(item);
                start = index + 2;
            }
            _ => {}
        }
    }
    if quoted || depth != 0 {
        return Err("unbalanced K sequence delimiters".into());
    }
    if items.is_empty() {
        Ok(None)
    } else {
        let item = source[start..].trim();
        if item.is_empty() {
            return Err("empty K sequence item".into());
        }
        items.push(item);
        Ok(Some(items))
    }
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
        let program_definition = with_resolved_group_tags(frontend_definition);
        let grammar: &'static Grammar = Box::leak(Box::new(Grammar {
            program: ProgramGrammar::new(&program_definition)?,
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
        let parser = self
            .parsers
            .get(parser_module)
            .expect("parser was inserted above");
        let item_sort = KastSort::builtin(BuiltinSort::KItem);
        let value = if sort.is_builtin(BuiltinSort::K) && !k_item {
            if source.trim() == ".K" {
                ParsedProgram::from_term(Term::sequence(Vec::new()))
            } else if let Some(items) = split_k_sequence(source)? {
                let items = items
                    .into_iter()
                    .filter(|item| *item != ".K")
                    .map(|item| {
                        parser
                            .parse(&item_sort, item)
                            .map(|parsed| parsed.typed_term().clone())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                ParsedProgram::from_term(Term::sequence(items))
            } else {
                parser.parse(&item_sort, source)?
            }
        } else {
            parser.parse(&parse_sort, source)?
        };
        let value = self
            .macro_definition
            .expand_program(&self.main_module, value, &parse_sort)?;
        // Type the expanded value at the position it was expanded at, as the assembler does for a configuration value.
        let injector = SortInjector::new(resolved, &self.main_module)?;
        let value_sort = injector.term_sort(value.term(), Some(value.position()))?;
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
                self.assembler.program(&program_start_sort(sort), source)?;
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
    /// Declared `$IO` and `$STDIN` that are not supplied receive the stream defaults with IO off and empty stdin.
    ///
    /// # Errors
    ///
    /// Returns the assembler's typed error for a parse failure or a missing variable.
    pub fn assemble_pattern(
        &mut self,
        program: Option<&str>,
        variables: &BTreeMap<String, String>,
    ) -> Result<Pattern, ConfigurationError> {
        self.assembler.clear();
        let result = self.assemble_typed(program, variables);
        self.assembler.clear();
        result
    }

    fn assemble_typed(
        &mut self,
        program: Option<&str>,
        variables: &BTreeMap<String, String>,
    ) -> Result<Pattern, ConfigurationError> {
        if let Some(source) = program {
            let start_sort = self
                .grammar
                .variables
                .get("PGM")
                .map_or_else(|| KastSort::builtin(BuiltinSort::KItem), program_start_sort);
            self.assembler.program(&start_sort, source)?;
        }
        for (name, source) in variables {
            self.assembler.bind(name, source)?;
        }
        self.assembler
            .bind_stream_defaults(false, true, || Ok::<_, ConfigurationError>(Vec::new()))?;
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
}

/// Resolve `syntax priority` and associativity tags that name a production `group` to the labels of its members.
///
/// k-rust's outer loader resolves a group tag to its productions' labels before it builds the flat
/// definition, and the program parser's priority and associativity filters read labels. Definition IR
/// reaches the flat definition through the structured adapter, which keeps the group names, so without
/// this resolution the program grammar would ignore every precedence the author declared by group.
/// Only the program-parsing copy is rewritten; the compiled KORE is unaffected.
fn with_resolved_group_tags(definition: &Definition) -> Definition {
    let mut groups: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for sentence in definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        if let Sentence::Production {
            label: Some(label),
            attributes,
            ..
        } = &**sentence
            && let Some(Value::String(tags)) = attributes.get("group")
        {
            for group in tags
                .split(',')
                .map(str::trim)
                .filter(|group| !group.is_empty())
            {
                groups.entry(group).or_default().insert(label.name.clone());
            }
        }
    }
    let resolve = |tags: &[String]| -> Vec<String> {
        let mut resolved = Vec::new();
        for tag in tags {
            match groups.get(tag.as_str()) {
                Some(labels) => resolved.extend(labels.iter().cloned()),
                None => resolved.push(tag.clone()),
            }
        }
        resolved
    };
    let mut resolved = definition.clone();
    for module in &mut resolved.modules {
        for sentence in &mut module.local_sentences {
            let replacement = match &**sentence {
                Sentence::SyntaxPriority {
                    priorities,
                    attributes,
                } => Sentence::SyntaxPriority {
                    priorities: priorities.iter().map(|level| resolve(level)).collect(),
                    attributes: attributes.clone(),
                },
                Sentence::SyntaxAssociativity {
                    associativity,
                    tags,
                    attributes,
                } => Sentence::SyntaxAssociativity {
                    associativity: *associativity,
                    tags: resolve(tags),
                    attributes: attributes.clone(),
                },
                _ => continue,
            };
            *sentence = std::sync::Arc::new(replacement);
        }
    }
    resolved
}

/// The sort `$PGM` is parsed at: its declared sort, or `KItem` when it is declared `K`.
fn program_start_sort(declared: &KastSort) -> KastSort {
    if declared.is_builtin(BuiltinSort::K) {
        KastSort::builtin(BuiltinSort::KItem)
    } else {
        declared.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::{Configuration, split_k_sequence, with_resolved_group_tags};
    use k_rust::{inner::ProgramParser, kast::Sort, names::BuiltinSort};
    use serde_json::json;
    use std::collections::BTreeMap;

    #[test]
    fn splits_only_top_level_k_sequence_delimiters() {
        assert_eq!(
            split_k_sequence("trap ~> .Instrs").unwrap(),
            Some(vec!["trap", ".Instrs"])
        );
        assert_eq!(
            split_k_sequence("f(\"~>\") ~> g(1)").unwrap(),
            Some(vec!["f(\"~>\")", "g(1)"])
        );
        assert_eq!(split_k_sequence(r#""~>""#).unwrap(), None);
        assert_eq!(split_k_sequence(r#"f("~>")"#).unwrap(), None);
        assert_eq!(split_k_sequence(r#""\"~>""#).unwrap(), None);
        assert!(split_k_sequence("a ~> ").is_err());
    }

    #[test]
    fn program_grammar_does_not_supply_implicit_kseq_productions() {
        let parsed = k_rust::outer::parse(
            "sequence.k",
            r#"
module MAIN
  imports BASIC-K
  syntax Item ::= "a" [symbol(a)] | "b" [symbol(b)]
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        let parser = ProgramParser::new(loaded.definition(), "MAIN").unwrap();
        let sort = Sort::builtin(BuiltinSort::K);
        assert!(parser.parse(&sort, "a").is_ok());
        for source in [".K", "a ~> b", "a ~> .K"] {
            assert!(parser.parse(&sort, source).is_err(), "{source}");
        }
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

    #[test]
    fn program_parsing_applies_priorities_declared_by_group_name() {
        let parsed = k_rust::outer::parse(
            "groups.k",
            r#"
module MAIN
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "*" Exp [symbol(mul), group(times), left]
               | Exp "+" Exp [symbol(add), group(plus), left]
  syntax priority times > plus
  configuration <k> $PGM:Exp </k>
endmodule
"#,
        )
        .unwrap();
        let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
        let loaded =
            krs_k_rust::prepare_definition(definition, krs_k_rust::Backend::Haskell).unwrap();
        // The structured adapter keeps group names where the outer loader resolved labels.
        let mut structured = loaded.definition().clone();
        for module in &mut structured.modules {
            for sentence in &mut module.local_sentences {
                if let k_rust::definition::Sentence::SyntaxPriority { attributes, .. } = &**sentence
                {
                    *sentence = std::sync::Arc::new(k_rust::definition::Sentence::SyntaxPriority {
                        priorities: vec![vec!["times".to_owned()], vec!["plus".to_owned()]],
                        attributes: attributes.clone(),
                    });
                }
            }
        }
        let resolved = with_resolved_group_tags(&structured);
        let priorities = resolved
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
            .find_map(|sentence| match &**sentence {
                k_rust::definition::Sentence::SyntaxPriority { priorities, .. } => {
                    Some(priorities.clone())
                }
                _ => None,
            })
            .unwrap();
        assert_eq!(
            priorities,
            vec![vec!["mul".to_owned()], vec!["add".to_owned()]]
        );
        let mut configuration = Configuration::new(
            &structured,
            BTreeMap::from([("PGM".to_owned(), Sort::new("Exp"))]),
        )
        .unwrap();
        let program = configuration
            .parse_program(&Sort::new("Exp"), "1 + 2 * 3")
            .unwrap();
        assert!(
            program.to_kast_text().starts_with("add("),
            "{}",
            program.to_kast_text()
        );
    }
}
