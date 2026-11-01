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
//! A sort parameter of an application is fixed by the text when a sort that mentions it is
//! met exactly, since a parametric sort is below another only at the same parameters
//! (`Box{S}` is below `Box{T}` only when `S` is `T`), and the parameter itself is below exactly
//! its instance only when it is that instance:
//!
//! - **By an argument:** the argument's declared sort mentions the parameter (`S`, `Box{S}`),
//!   and the argument reads back at exactly the declared sort's instance (`Int`, `Box{Int}`):
//!   it reads at its own sort, which must be below the declared sort's instance, and is it.
//! - **By the position:** the declared result sort is an application that mentions the parameter
//!   (`Box{S}`, not the bare `S` nor a sort without it, such as `String` for
//!   `{S} String ::= #unparseKORE(S)`), and the application stands at a position of exactly its
//!   instantiated result sort, which only that instance's result is below.
//!
//! An argument under an injection reads at the injected sort, below the parameter's instance,
//! and a position under an injection admits any sort below it, so neither fixes it. These are
//! sufficient, not necessary: a parameter several arguments' sorts fix only through their least
//! upper bound is taken as not fixed.
//!
//! The judgement is made on the tree as it is printed, after alias reversal, which can move an
//! application to another position or build one: the text read back is that tree's. An
//! application whose instance no text fixes prints as its KORE pattern, which names the instance,
//! and the print says so ([`crate::Warning::Instance`]). Where reversal printed one of its
//! arguments through an alias, that pattern applies the alias's symbol, which the definition
//! equates with its expansion.

use std::collections::BTreeSet;

use k_rust::kore::ast::Sort;

use crate::data::PrintData;
use crate::node::{App, Node, Sym, to_pattern};

/// The symbol of a subterm printed as its KORE text, its one argument.
pub(crate) const KORE_TEXT: &str = "#krs-kore-text";

/// Replace in `node` each application whose instance its text does not fix by its KORE text
/// ([`KORE_TEXT`]); the KORE names of their symbols are added to `unfixed`. `node` stands at no
/// known position.
pub(crate) fn fix_instances(data: &PrintData, node: &mut Node, unfixed: &mut BTreeSet<String>) {
    // Each entry is a node and the sort of the position it stands at exactly, `None` where it
    // stands under an injection or where the position is not known. Iterative: a `~>` sequence
    // or a cons list can be deeper than the stack.
    let mut stack: Vec<(&mut Node, Option<Sort>)> = vec![(node, None)];
    while let Some((node, position)) = stack.pop() {
        let Node::App(app) = node else {
            continue;
        };
        if matches!(app.sym.name.as_str(), "\\dv" | KORE_TEXT) {
            continue;
        }
        if !fixed(data, app, position.as_ref())
            && let Some(pattern) = to_pattern(node)
        {
            if let Node::App(app) = node {
                unfixed.insert(app.sym.name.clone());
            }
            let mut sym = Sym::new(KORE_TEXT, Vec::new());
            sym.sort = node.sort().cloned();
            *node = Node::app(sym, vec![Node::Str(pattern.to_string().into_bytes())]);
            continue;
        }
        let Node::App(app) = node else {
            continue;
        };
        let exact = !(app.sym.name == "inj" || app.sym.is_builtin());
        for (index, argument) in app.args.iter_mut().enumerate() {
            let position = exact
                .then(|| app.sym.arguments.get(index).cloned())
                .flatten();
            stack.push((argument, position));
        }
    }
}

/// Whether the text of `app`, standing exactly at `position`, fixes its instance.
fn fixed(data: &PrintData, app: &App, position: Option<&Sort>) -> bool {
    if app.sym.is_builtin() || app.sym.name == "inj" {
        return true;
    }
    let Some(declaration) = data.declarations.get(&app.sym.name) else {
        return true;
    };
    let at_result = position.is_some() && position == app.sym.sort.as_ref();
    declaration.parameters.iter().all(|parameter| {
        let by_argument = declaration
            .arguments
            .iter()
            .zip(&app.sym.arguments)
            .zip(&app.args)
            .any(|((declared, instance), argument)| {
                mentions(declared, parameter) && own_sort(argument) == Some(instance)
            });
        let by_position = at_result
            && matches!(&declaration.result, Sort::Application { arguments, .. }
                if arguments.iter().any(|argument| mentions(argument, parameter)));
        by_argument || by_position
    })
}

/// Whether `sort` is the sort variable `parameter` or an application with it among its
/// arguments, at any depth.
fn mentions(sort: &Sort, parameter: &str) -> bool {
    match sort {
        Sort::Variable(name) => name == parameter,
        Sort::Application { arguments, .. } => arguments
            .iter()
            .any(|argument| mentions(argument, parameter)),
    }
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
