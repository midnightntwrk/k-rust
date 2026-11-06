//! Text that applies a function evaluated in one instance of a Map collection with its authored
//! arguments.
//!
//! Such a function receives each instance's key after its own arguments
//! (`krs_ir_levels::k_surface::instance_key_field`), so the main module's grammar holds it as
//! `pcPlus ( Int ) #instance ( Int )`. The keys are an emission detail: the text an author writes
//! against the declaration is `pcPlus ( 1 )`, which no grammar of the definition reads, so its
//! parse fails without saying why. An input is evaluated in no instance, so no reading of such
//! text could be configured anyway: where a variable's text does not parse, it is read once more
//! with the main module's grammar in which each such function has its authored items alone
//! ([`authored_definition`]), and a reading that applies one is refused with the reason every
//! other input route gives ([`crate::values::ValueIndex::instance_function`]).
//!
//! That grammar only reads: its terms are never configured, emitted or sent to a backend.

use std::sync::Arc;

use k_rust::{
    definition::{Definition, ProductionItem, Sentence},
    inner::ProgramParser,
    kast::{Sort as KastSort, Term},
    kompile::{ProgramGrammar, encode_kore_label, program_start_position},
    names::BuiltinSort,
};

use crate::values::{Decl, ValueIndex};
use crate::{ExecError, Semantics};

/// The parser of [`authored_definition`]'s main module, built on the first parse failure of a
/// definition with a function evaluated in one instance, or `None` where the definition has no
/// such function or that grammar does not resolve.
pub(crate) type AuthoredParser = Option<Option<ProgramParser>>;

impl Semantics {
    /// The refusal of `text`, the text bound to the configuration variable `variable` (without
    /// `$`) at its declared `sort`, which no grammar of the definition parses, where it applies a
    /// function evaluated in one instance of a Map collection with its authored arguments
    /// ([`authored_definition`]); `None` where it applies none, and the parse failure stands.
    pub(crate) fn instance_text_refusal(
        &mut self,
        variable: &str,
        sort: &KastSort,
        text: &str,
    ) -> Option<ExecError> {
        let parser = self
            .authored_parser
            .get_or_insert_with(|| {
                if !self.values.has_instance_functions() {
                    return None;
                }
                let definition = authored_definition(&self.frontend_definition, &self.values)?;
                let grammar = ProgramGrammar::new(&definition).ok()?;
                ProgramParser::from_resolved(grammar.resolved(), &self.main_module).ok()
            })
            .as_ref()?;
        let parsed = if sort.is_builtin(BuiltinSort::K) {
            parser.parse_configuration_k_value(text)
        } else {
            parser.parse(&program_start_position(sort), text)
        }
        .ok()?;
        let decl = instance_application(&self.values, parsed.typed_term())?;
        let reason = self
            .values
            .instance_function(&decl, "an input")
            .expect("an instance application applies an instance function");
        Some(ExecError::InstanceFunction {
            variable: variable.to_owned(),
            reason,
        })
    }
}

/// `frontend` with each production of a function evaluated in one instance of a Map collection
/// cut to its authored items: its keys, `#instance ( Key , .. )`, are the last `2 * keys + 2`
/// items, after its own. `None` where it has no such production.
fn authored_definition(frontend: &Definition, values: &ValueIndex) -> Option<Definition> {
    let mut definition = frontend.clone();
    let mut cut = false;
    for module in &mut definition.modules {
        for sentence in &mut module.local_sentences {
            let Sentence::Production {
                label: Some(label),
                items,
                ..
            } = sentence.as_ref()
            else {
                continue;
            };
            let Some((_, keys)) = values.instance_function_symbol(&encode_kore_label(label).name)
            else {
                continue;
            };
            let Some(authored) = items.len().checked_sub(2 * keys + 2) else {
                continue;
            };
            if !matches!(&items[authored], ProductionItem::Terminal(terminal) if terminal == "#instance")
            {
                continue;
            }
            let mut production = sentence.as_ref().clone();
            if let Sentence::Production { items, .. } = &mut production {
                items.truncate(authored);
            }
            *sentence = Arc::new(production);
            cut = true;
        }
    }
    cut.then_some(definition)
}

/// The first function evaluated in one instance of a Map collection that the parsed `term`
/// applies, in pre-order.
fn instance_application(values: &ValueIndex, term: &Term) -> Option<Decl> {
    let mut stack = vec![term];
    while let Some(term) = stack.pop() {
        if let Term::Apply { label, .. } = term.unannotated()
            && let Some((decl, _)) = values.instance_function_symbol(&encode_kore_label(label).name)
        {
            return Some(decl);
        }
        stack.extend(term.children().into_iter().rev());
    }
    None
}
