//! krun's initial configuration: `$PGM`, `-c` bindings parsed with the cell's parser module,
//! `$IO`/`$STDIN` stream defaults, and the `initGeneratedTopCell` application (S18).

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    definition::{AttributeKey, ResolvedDefinition, Sentence},
    kast::Sort as KastSort,
    kore::ast::{KoreString, Pattern, Sort, Symbol},
    names::{BuiltinSort, WellKnownSymbol},
};

pub type ConfigurationBinding = (String, Pattern, Sort);

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

/// Supply the stream configuration variables in reference order and read buffered stdin only when
/// `$STDIN` is declared, absent, IO is disabled, and the parsed program does not consume stdin.
pub fn stream_defaults<E>(
    available: &BTreeMap<String, KastSort>,
    seen: &mut BTreeSet<String>,
    io: bool,
    program_uses_stdin: bool,
    read_buffered_stdin: impl FnOnce() -> Result<Vec<u8>, E>,
) -> Result<Vec<ConfigurationBinding>, E> {
    let mut bindings = Vec::new();
    let string_sort = KastSort::builtin(BuiltinSort::String);
    if available.get("IO") == Some(&string_sort) && !seen.contains("IO") {
        bindings.push((
            "$IO".into(),
            string_domain_value(if io { "on" } else { "off" }),
            kore_sort(BuiltinSort::String.kore_name()),
        ));
        seen.insert("IO".into());
    }
    if available.get("STDIN") == Some(&string_sort) && !seen.contains("STDIN") {
        let input = if io || program_uses_stdin {
            Vec::new()
        } else {
            read_buffered_stdin()?
        };
        bindings.push((
            "$STDIN".into(),
            string_domain_value(input),
            kore_sort(BuiltinSort::String.kore_name()),
        ));
        seen.insert("STDIN".into());
    }
    Ok(bindings)
}

pub fn missing_variables(
    available: &BTreeMap<String, KastSort>,
    seen: &BTreeSet<String>,
) -> Vec<String> {
    available
        .keys()
        .filter(|name| name.as_str() != "PGM" && !seen.contains(*name))
        .map(|name| format!("${name}"))
        .collect()
}

/// Build the `initGeneratedTopCell` application the way `llvm-krun` does from krun's `-c`
/// list: `$PGM` first, then supplied and synthesized configuration bindings in their input order.
pub fn top_cell_initializer(
    program: Option<(Pattern, Sort)>,
    config_vars: Vec<ConfigurationBinding>,
) -> Pattern {
    let mut entries = Vec::with_capacity(config_vars.len() + 1);
    if let Some((program, program_sort)) = program {
        entries.push(("$PGM".to_owned(), program, program_sort));
    }
    entries.extend(config_vars);
    let mut entries = entries
        .into_iter()
        .map(|(name, value, value_sort)| configuration_map_entry(&name, value, value_sort));
    let arguments = match entries.next() {
        Some(first) => vec![entries.fold(first, |left, right| {
            kore_application("Lbl'Unds'Map'Unds'", Vec::new(), vec![left, right])
        })],
        None => Vec::new(),
    };
    kore_application("LblinitGeneratedTopCell", Vec::new(), arguments)
}

fn configuration_map_entry(name: &str, value: Pattern, value_sort: Sort) -> Pattern {
    let config_var_sort = kore_sort(BuiltinSort::KConfigVar.kore_name());
    let item_sort = kore_sort(BuiltinSort::KItem.kore_name());
    let key = kore_application(
        WellKnownSymbol::Inj.as_str(),
        vec![config_var_sort.clone(), item_sort.clone()],
        vec![Pattern::DomainValue {
            sort: config_var_sort,
            value: name.into(),
        }],
    );
    let value = if value_sort == item_sort {
        value
    } else {
        kore_application(
            WellKnownSymbol::Inj.as_str(),
            vec![value_sort, item_sort],
            vec![value],
        )
    };
    kore_application("Lbl'UndsPipe'-'-GT-Unds'", Vec::new(), vec![key, value])
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
        let initial = top_cell_initializer(
            Some((
                Pattern::DomainValue {
                    sort: kore_sort("SortExp"),
                    value: "program".into(),
                },
                kore_sort("SortExp"),
            )),
            vec![(
                "$ENV".into(),
                kore_application("Lbl'Dot'Map", Vec::new(), Vec::new()),
                kore_sort("SortMap"),
            )],
        );
        let rendered = Printer::compact().print_pattern(&initial);

        assert!(rendered.contains("Lbl'Unds'Map'Unds'"), "{rendered}");
        assert!(rendered.contains("$PGM"), "{rendered}");
        assert!(rendered.contains("$ENV"), "{rendered}");
        assert!(
            rendered.contains("inj{SortMap{}, SortKItem{}}"),
            "{rendered}"
        );
    }

    #[test]
    fn top_initializer_without_any_binding_is_nullary() {
        let initial = top_cell_initializer(None, Vec::new());
        assert_eq!(
            Printer::compact().print_pattern(&initial),
            "LblinitGeneratedTopCell{}()"
        );
    }
}
