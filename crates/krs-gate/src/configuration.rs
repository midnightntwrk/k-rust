//! Assemble krun's `-c` pipeline from k-rust's public parser, macro, injection, and initializer pieces.
//! Replace this assembly with a k-rust library function when one is available.
//! `ProgramParser` uses visible program productions and adds `KItem` subsorts, but does not add the implicit `KSEQ` productions `K ::= ".K"` and `K ::= K "~>" K`.
//! `BASIC-K` supplies the subsort path for a single item at `K`, but supplies neither sequence production.
//! Cell expectations must therefore split top-level sequence delimiters outside quoted strings, parse each item at `KItem`, and assemble `Term::sequence`.

use k_rust::{
    definition::ResolvedDefinition,
    inner::{ProgramParser, definition_with_named_projections},
    kast::{Sort as KastSort, Term},
    kompile::{
        MacroExpansionDefinition, SortInjector, encode_kore_sort,
        initial_configuration::{parser_modules, stream_defaults, top_cell_initializer},
        term_to_kore_from_resolved_with_token_module,
    },
    kore::ast::{Pattern, Sort, Symbol},
    names::BuiltinSort,
};
use krs_k_rust::ConfigurationContext;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
};

/// The reusable surface parsing context for one loaded definition.
pub struct Configuration {
    context: ConfigurationContext,
    main_module: String,
    syntax_module: String,
    resolved: ResolvedDefinition,
    parser_modules: BTreeMap<String, String>,
    parsers: BTreeMap<String, ProgramParser>,
    macro_definition: MacroExpansionDefinition,
}

fn validate_variables(
    available: &BTreeMap<String, KastSort>,
    variables: &Map<String, Value>,
) -> Result<(), String> {
    for name in variables.keys() {
        if !available.contains_key(name) {
            return Err(format!(
                "definition has no configuration variable `${name}`"
            ));
        }
        if !variables[name].is_string() {
            return Err(format!(
                "configuration variable `${name}` must be surface text"
            ));
        }
    }
    let string_sort = KastSort::builtin(BuiltinSort::String);
    let missing = available
        .iter()
        .filter(|(name, sort)| {
            !(variables.contains_key(*name)
                || matches!(name.as_str(), "IO" | "STDIN") && *sort == &string_sort)
        })
        .map(|(name, _)| format!("${name}"))
        .collect::<Vec<_>>();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "missing required configuration variable{} {}",
            if missing.len() == 1 { "" } else { "s" },
            missing.join(", ")
        ))
    }
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
    /// Prepare projections, configuration parser modules, and macros once per session.
    ///
    /// # Errors
    ///
    /// Returns an error when the prepared frontend definition cannot be resolved.
    pub fn new(context: ConfigurationContext) -> Result<Self, Box<dyn Error>> {
        let projected = definition_with_named_projections(&context.frontend_definition);
        let resolved = ResolvedDefinition::resolve(&projected)?;
        let syntax_module = k_rust::outer::resolve_syntax_module(&resolved, None)?.name;
        let parser_modules = parser_modules(&resolved, &context.frontend_definition.main_module)?;
        let macro_definition = MacroExpansionDefinition::prepare(&projected)?;
        Ok(Self {
            main_module: context.frontend_definition.main_module.clone(),
            syntax_module,
            context,
            resolved,
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
        if self.resolved.module_id(parser_module).is_none() {
            return Err(format!("parser module `{parser_module}` was not found").into());
        }
        if !self.parsers.contains_key(parser_module) {
            self.parsers.insert(
                parser_module.to_owned(),
                ProgramParser::from_resolved(&self.resolved, parser_module)?,
            );
        }
        let parse_sort = if sort.is_builtin(BuiltinSort::K) && k_item {
            KastSort::builtin(BuiltinSort::KItem)
        } else {
            sort.clone()
        };
        let parser = self
            .parsers
            .get(parser_module)
            .expect("parser was inserted above");
        let value = if sort.is_builtin(BuiltinSort::K) && !k_item {
            if source.trim() == ".K" {
                Term::sequence(Vec::new())
            } else if let Some(items) = split_k_sequence(source)? {
                Term::sequence(
                    items
                        .into_iter()
                        .filter(|item| *item != ".K")
                        .map(|item| parser.parse(&KastSort::builtin(BuiltinSort::KItem), item))
                        .collect::<Result<Vec<_>, _>>()?,
                )
            } else {
                parser.parse(&KastSort::builtin(BuiltinSort::KItem), source)?
            }
        } else {
            parser.parse(&parse_sort, source)?
        };
        let value = self
            .macro_definition
            .expand_term(&self.main_module, value)?;
        let injector = SortInjector::new(&self.resolved, &self.main_module)?;
        let value_sort = injector.term_sort(&value, None)?;
        let value = injector.inject_at_top(&value)?;
        let value = term_to_kore_from_resolved_with_token_module(
            &self.resolved,
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
            .context
            .configuration_variables
            .get(name)
            .ok_or_else(|| format!("definition has no configuration variable `${name}`"))?
            .clone();
        let parser_module = if name == "PGM" {
            &self.syntax_module
        } else {
            self.parser_modules.get(name).unwrap_or(&self.main_module)
        }
        .clone();
        self.parse_surface(&parser_module, &sort, source, true)
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

    /// Parse every declared variable and assemble `initGeneratedTopCell`.
    ///
    /// `$PGM` is first, followed by the remaining names in lexical order.
    /// `$IO` and `$STDIN`, when declared and omitted, receive stream defaults with IO off and empty stdin.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or missing variable, or a surface parse failure.
    pub fn configure(&mut self, variables: &Map<String, Value>) -> Result<Value, Box<dyn Error>> {
        validate_variables(&self.context.configuration_variables, variables)?;
        let mut seen = BTreeSet::new();
        let mut rendered = Map::new();
        let mut program = None;
        let mut bindings = Vec::new();
        let mut names = self
            .context
            .configuration_variables
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        names.sort_by_key(|name| (name != "PGM", name.clone()));
        for name in names {
            let Some(source) = variables.get(&name) else {
                continue;
            };
            let source = source
                .as_str()
                .ok_or_else(|| format!("configuration variable `${name}` must be surface text"))?;
            let (value, sort) = self.parse_variable(&name, source)?;
            rendered.insert(
                name.clone(),
                json!({"sort": sort.to_string(), "kore": value.to_string()}),
            );
            seen.insert(name.clone());
            if name == "PGM" {
                program = Some((value, sort));
            } else {
                bindings.push((format!("${name}"), value, sort));
            }
        }
        let defaults = stream_defaults(
            &self.context.configuration_variables,
            &mut seen,
            false,
            true,
            || Ok::<Vec<u8>, Box<dyn Error>>(Vec::new()),
        )?;
        for (name, value, sort) in &defaults {
            rendered.insert(
                name.trim_start_matches('$').to_owned(),
                json!({"sort": sort.to_string(), "kore": value.to_string()}),
            );
        }
        bindings.extend(defaults);
        Ok(
            json!({"pattern": top_cell_initializer(program, bindings).to_string(), "variables": rendered}),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{split_k_sequence, validate_variables};
    use k_rust::{inner::ProgramParser, kast::Sort, names::BuiltinSort};
    use serde_json::{Map, json};
    use std::collections::BTreeMap;

    #[test]
    fn validates_declared_names_and_surface_text() {
        let available = BTreeMap::from([
            ("PGM".to_owned(), Sort::builtin(BuiltinSort::K)),
            ("STACK".to_owned(), Sort::builtin(BuiltinSort::K)),
            ("STDIN".to_owned(), Sort::builtin(BuiltinSort::String)),
        ]);
        let mut variables = Map::new();
        variables.insert("PGM".into(), json!("run"));
        assert_eq!(
            validate_variables(&available, &variables).unwrap_err(),
            "missing required configuration variable $STACK"
        );
        variables.insert("STACK".into(), json!(".Stack"));
        validate_variables(&available, &variables).unwrap();
        variables.insert("EXTRA".into(), json!("x"));
        assert!(
            validate_variables(&available, &variables)
                .unwrap_err()
                .contains("$EXTRA")
        );
        variables.remove("EXTRA");
        variables.insert("STACK".into(), json!(1));
        assert!(
            validate_variables(&available, &variables)
                .unwrap_err()
                .contains("$STACK")
        );
    }

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
        let parser = ProgramParser::new(&loaded.definition, "MAIN").unwrap();
        let sort = Sort::builtin(BuiltinSort::K);
        assert!(parser.parse(&sort, "a").is_ok());
        for source in [".K", "a ~> b", "a ~> .K"] {
            assert!(parser.parse(&sort, source).is_err(), "{source}");
        }
    }
}
