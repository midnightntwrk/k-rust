//! Applications whose instance no printed text fixes.
//!
//! A printed term is read back by a parser that infers a parametric production's instance: from
//! the sorts its arguments read at, and from the sort of the position it stands at. Printed, an
//! application is its production's text, which names no instance, so it reads back as the one
//! inference picks. Where that is not the term's own, the text names another term:
//! `Wrap::<KItem>(1)`, the production `{S} S ::= wrap(S)` at `S = KItem` over the `Int` 1, prints
//! `wrap(1)`, which reads back at `S = Int`, since the argument reads as an `Int` and nothing
//! in the text raises it.
//!
//! An instance is fixed by the text when each of its sort parameters is either the own sort of
//! an argument declared at exactly that parameter (an argument read back at its own sort makes
//! the parameter at least that sort, and the argument's declared sort makes it at most), or,
//! where the result sort is a parametric sort and not the parameter itself, by a position whose
//! sort is exactly the application's result sort (a sort `Wrap{S}` is below `Wrap{T}` only when
//! `S` is `T`). An argument under an injection reads at the injected sort, below the
//! parameter's instance, and a position under an injection admits any sort below it, so neither
//! fixes it. These are sufficient, not necessary: a parameter several arguments' sorts fix only
//! through their least upper bound is taken as not fixed.
//!
//! An application whose instance no text fixes prints as its KORE pattern, which names the
//! instance, and the print says so ([`crate::Warning::Instance`]).

use std::collections::BTreeSet;

use k_rust::kore::ast::Sort;

use crate::data::PrintData;
use crate::node::{App, Node, Sym, to_pattern};

/// The symbol of a subterm printed as its KORE text: its first argument, the text, beside the
/// term itself.
pub(crate) const KORE_TEXT: &str = "#krs-kore-text";

/// `node` with each application whose instance its text does not fix replaced by its KORE text
/// ([`KORE_TEXT`]); the KORE names of their symbols in `unfixed`. `position` is the sort of the
/// position `node` stands at exactly, `None` where it stands under an injection or where the
/// position is not known.
pub(crate) fn fix_instances(
    data: &PrintData,
    node: &Node,
    position: Option<&Sort>,
    unfixed: &mut BTreeSet<String>,
) -> Node {
    let Node::App(app) = node else {
        return node.clone();
    };
    if app.sym.name == "\\dv" {
        return node.clone();
    }
    if !fixed(data, app, position)
        && let Some(pattern) = to_pattern(node)
    {
        unfixed.insert(app.sym.name.clone());
        let mut sym = Sym::new(KORE_TEXT, Vec::new());
        sym.sort.clone_from(&app.sym.sort);
        // The term stays beside its text, so that the passes that count or compare a term's
        // variables (`singleton_vars`) still see them; only the text is printed.
        return Node::app(
            sym,
            vec![Node::Str(pattern.to_string().into_bytes()), node.clone()],
        );
    }
    let positions = |index: usize| {
        if app.sym.name == "inj" || app.sym.is_builtin() {
            None
        } else {
            app.sym.arguments.get(index)
        }
    };
    let args = app
        .args
        .iter()
        .enumerate()
        .map(|(index, argument)| fix_instances(data, argument, positions(index), unfixed))
        .collect();
    Node::app(app.sym.clone(), args)
}

/// Whether the text of `app`, standing exactly at `position`, fixes its instance.
fn fixed(data: &PrintData, app: &App, position: Option<&Sort>) -> bool {
    if app.sym.is_builtin() || app.sym.name == "inj" {
        return true;
    }
    let Some(declaration) = data.declarations.get(&app.sym.name) else {
        return true;
    };
    declaration
        .parameters
        .iter()
        .zip(&app.sym.formals)
        .all(|(parameter, instance)| {
            let variable = Sort::Variable(parameter.clone());
            let by_argument =
                declaration
                    .arguments
                    .iter()
                    .zip(&app.args)
                    .any(|(declared, argument)| {
                        *declared == variable && own_sort(argument) == Some(instance)
                    });
            let by_position = declaration.result != variable
                && position.is_some()
                && position == app.sym.sort.as_ref();
            by_argument || by_position
        })
}

/// The sort `node` reads back at: an injection's argument's, a domain value's own.
fn own_sort(node: &Node) -> Option<&Sort> {
    match node {
        Node::App(app) if matches!(app.sym.name.as_str(), "inj" | "\\dv") => {
            app.sym.formals.first()
        }
        other => other.sort(),
    }
}
