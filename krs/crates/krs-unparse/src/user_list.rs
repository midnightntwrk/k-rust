//! A user list printed in its program spelling.
//!
//! A user list is a sort declared `List{Int, ","}` or `NeList{Int, ","}`: a cons production
//! `Int "," Ints` and a terminator `".Ints"`, both `userList`. A program writes a list as its
//! elements with the separator between them, and the empty list as no text: the parser builds
//! `intsCons(1, intsCons(2, intsNil))` from `1, 2`, putting the terminator in where the elements
//! end, and reads no text at all at a `List`'s position as its terminator alone. `.Ints`, the
//! terminator's own text, is K's rule syntax, which no program grammar reads, and a `NeList` has
//! no empty spelling at all. Every value grammar of the definition (the program's, the main
//! module's) reads lists so.
//!
//! So a print writes a cons whose tail is its list's terminator as the element alone ([`LAST`]),
//! and a terminator that stands alone as no text ([`EMPTY`]) where that text reads back as it:
//!
//! - its list is a `List`;
//! - a non-empty terminal of the enclosing production, or the edge of the printed text, stands
//!   right before it and right after it, through every production it is the first (the last)
//!   item of: beside a neighbour's text, the parser may read the empty text on the neighbour's
//!   other side (`Ints Ints` writes `[] [1]` as it writes `[1] []`);
//! - it is not the one element of a list, which would be no text too, and read back as that
//!   list's own empty list;
//! - no text reads at its position as it, or as a term the definition's overload axioms equate
//!   with it. A list reads no text as its terminator if it is a `List`, and as a one-element
//!   list if its elements can be no text (`List{Ints, ";"}` reads it as `[]` and as `[[]]`, an
//!   ambiguity). So no list below the sort of its position, its own included, may read it as a
//!   one-element list, and of their terminators the parser must read the one every other's
//!   overloads, the most specific (`Vals`'s in an `Exps`, where `Vals` is the `Exps` overload of
//!   K's `Vals` idiom), which is this one or one of its overloads. At the root the position is
//!   the term's own sort, or an injection's target: a print alone is read at that sort.
//!
//! Elsewhere the empty list has no program text: it prints as K's `.Ints`, and the print says so
//! ([`crate::Warning::EmptyList`]), as it does for a child no bracket of the definition groups.
//! A cons whose tail is no list (a variable, a function's application) has no program text
//! either; it prints as K writes it, and the read-back judges it.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::kore::ast::Sort;

use crate::brackets::item_position;
use crate::data::PrintData;
use crate::node::{Node, Sym};

/// The symbol of a list's last element, its one argument, printed alone: a cons whose tail is
/// the terminator. Its argument sort is the element's, its sort the list's.
pub(crate) const LAST: &str = "#krs-list-last";

/// The symbol of the empty list printed as no text. Its sort is the list's.
pub(crate) const EMPTY: &str = "#krs-list-empty";

/// The user lists of a definition, by their symbols' KORE names.
#[derive(Clone, Debug, Default)]
pub(crate) struct UserLists {
    /// Each list by its cons symbol.
    conses: BTreeMap<String, UserList>,
    /// Each terminator, and whether its list is a `NeList`.
    terminators: BTreeMap<String, bool>,
}

/// One user list, by its cons symbol.
#[derive(Clone, Debug)]
struct UserList {
    terminator: String,
    /// Whether its separator is a non-empty terminal (`List{Int, ""}` juxtaposes its elements).
    separated: bool,
}

impl UserLists {
    /// Add the list whose cons is `cons` and terminator `terminator`.
    pub fn insert(&mut self, cons: String, terminator: String, separated: bool, non_empty: bool) {
        self.terminators.insert(terminator.clone(), non_empty);
        self.conses.insert(
            cons,
            UserList {
                terminator,
                separated,
            },
        );
    }

    fn is_empty(&self) -> bool {
        self.conses.is_empty()
    }
}

impl UserList {
    /// Whether `tail`, a tail of this list's cons, is the empty list: its terminator, or an
    /// overload of it injected into the list's sort, which the definition's overload axioms
    /// equate with it (`Vals`'s terminator in an `Exps`, of K's `Vals` idiom). Either way the
    /// cons's element is the list's last.
    fn terminated_by(&self, data: &PrintData, mut tail: &Node) -> bool {
        while let Node::App(app) = tail {
            if app.sym.name == self.terminator
                || data
                    .overloads
                    .get(&app.sym.name)
                    .is_some_and(|greater| greater.contains(&self.terminator))
            {
                return true;
            }
            match (app.sym.name.as_str(), app.args.as_slice()) {
                ("inj", [argument]) => tail = argument,
                _ => return false,
            }
        }
        false
    }
}

/// What a node's position is read at.
#[derive(Clone, Debug)]
enum Position {
    /// The root of the print, read alone at the term's own sort.
    Root,
    /// A position whose sort is known.
    At(Sort),
    /// A position no production's sorts describe: a connective's argument.
    Unknown,
}

/// What a node is to the list around it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role {
    /// No part of a list's own structure.
    Other,
    /// The one element of a list, whose text is the list's.
    Sole,
    /// A cons's tail: a cons there continues a list, it does not start one.
    Tail,
}

/// Where a node stands in the printed text.
#[derive(Clone, Debug)]
struct Place {
    position: Position,
    /// A non-empty terminal, or the start of the text, stands right before its text.
    left: bool,
    /// A non-empty terminal, or the end of the text, stands right after its text.
    right: bool,
    role: Role,
}

impl Place {
    const fn root() -> Self {
        Self {
            position: Position::Root,
            left: true,
            right: true,
            role: Role::Other,
        }
    }

    const fn child(position: Position, left: bool, right: bool) -> Self {
        Self {
            position,
            left,
            right,
            role: Role::Other,
        }
    }
}

/// Rewrite `node`, a tree ready to print, so that each user list prints in its program
/// spelling (module documentation): a cons whose tail is its terminator becomes [`LAST`] of its
/// element, and a terminator alone becomes [`EMPTY`] where no text reads back as it. The K
/// names of the sorts of the empty lists left in K's spelling, which no program text writes
/// where they stand, are added to `unwritten`. An application of a symbol with no format is
/// left as it is: it prints as KAST, which writes lists in K's spelling.
pub(crate) fn spell(
    data: &PrintData,
    lists: &UserLists,
    node: &mut Node,
    unwritten: &mut BTreeSet<String>,
) {
    if lists.is_empty() {
        return;
    }
    let silent = Silent::new(data, lists);
    // Iterative: a cons list or a `~>` sequence can be deeper than the stack.
    let mut stack: Vec<(&mut Node, Place)> = vec![(node, Place::root())];
    while let Some((node, place)) = stack.pop() {
        let Some(app) = node.as_app() else {
            continue;
        };
        if let Some(&non_empty) = lists.terminators.get(&app.sym.name) {
            if !non_empty && silent.written(data, &app.sym.name, app.sym.sort.as_ref(), &place) {
                let mut sym = Sym::new(EMPTY, Vec::new());
                sym.sort.clone_from(&app.sym.sort);
                *node = Node::app(sym, Vec::new());
            } else {
                unwritten.insert(crate::brackets::sort_name(app.sym.sort.as_ref()));
            }
            continue;
        }
        let list = lists
            .conses
            .get(&app.sym.name)
            .filter(|_| app.args.len() == 2);
        if let Some(list) = list
            && list.terminated_by(data, &app.args[1])
        {
            let Node::App(mut cons) = std::mem::replace(node, Node::Str(Vec::new())) else {
                unreachable!("an application")
            };
            let element = cons.args.swap_remove(0);
            let mut sym = Sym::new(LAST, Vec::new());
            sym.arguments = cons.sym.arguments.first().cloned().into_iter().collect();
            sym.sort = cons.sym.sort;
            let element_position = position_of(sym.arguments.first());
            *node = Node::app(sym, vec![element]);
            let Node::App(alone) = node else {
                unreachable!("just built")
            };
            let mut element_place = Place::child(element_position, place.left, place.right);
            if place.role != Role::Tail {
                element_place.role = Role::Sole;
            }
            stack.extend(
                alone
                    .args
                    .iter_mut()
                    .map(|element| (element, element_place.clone())),
            );
            continue;
        }
        let Node::App(app) = node else {
            continue;
        };
        if let Some(list) = list {
            let element_position = position_of(app.sym.arguments.first());
            let tail_position = position_of(app.sym.arguments.get(1));
            let [element, tail] = app.args.as_mut_slice() else {
                unreachable!("two arguments")
            };
            let mut tail_place = Place::child(tail_position, list.separated, place.right);
            tail_place.role = Role::Tail;
            stack.push((tail, tail_place));
            stack.push((
                element,
                Place::child(element_position, place.left, list.separated),
            ));
            continue;
        }
        let name = app.sym.name.as_str();
        match name {
            "\\dv" | crate::instance::KORE_TEXT => continue,
            "inj" => {
                // An injection prints its argument: it stands where the injection does, at the
                // injection's target.
                let position = match app.sym.formals.get(1) {
                    Some(target) => Position::At(target.clone()),
                    None => Position::Unknown,
                };
                let inner = Place { position, ..place };
                stack.extend(
                    app.args
                        .iter_mut()
                        .map(|argument| (argument, inner.clone())),
                );
                continue;
            }
            _ => {}
        }
        if !data.format.contains_key(name) {
            continue;
        }
        let places = (0..app.args.len())
            .map(|index| argument_place(data, app, index, &place))
            .collect::<Vec<_>>();
        stack.extend(app.args.iter_mut().zip(places));
    }
}

/// Where the `index`-th argument of `app`, standing at `place`, stands: delimited by the
/// production's terminals beside it, or by what delimits `app` where it is the first (the
/// last) item; at the sort the production declares there.
fn argument_place(data: &PrintData, app: &crate::node::App, index: usize, place: &Place) -> Place {
    let terminals = data
        .terminals
        .get(&app.sym.name)
        .map(String::as_bytes)
        .unwrap_or_default();
    let at = item_position(terminals, index);
    let (left, right) = if at < terminals.len() {
        (
            if at == 0 {
                place.left
            } else {
                terminals[at - 1] == b'1'
            },
            if at + 1 == terminals.len() {
                place.right
            } else {
                terminals[at + 1] == b'1'
            },
        )
    } else {
        (false, false)
    };
    let position = if app.sym.is_builtin() {
        Position::Unknown
    } else {
        position_of(app.sym.arguments.get(index))
    };
    Place::child(position, left, right)
}

fn position_of(sort: Option<&Sort>) -> Position {
    sort.map_or(Position::Unknown, |sort| Position::At(sort.clone()))
}

/// The lists that read no text, each as its terminator alone or as a one-element list.
struct Silent {
    /// Each such list's terminator, its sort, and whether its elements can be no text (it then
    /// reads no text as a one-element list).
    lists: Vec<(String, Sort, bool)>,
}

impl Silent {
    fn new(data: &PrintData, lists: &UserLists) -> Self {
        // Each list's terminator, sort, element sort, and whether it is a `List`.
        let all = lists
            .conses
            .iter()
            .filter_map(|(cons, list)| {
                let sort = data.declarations.get(&list.terminator)?.result.clone();
                let element = data.declarations.get(cons)?.arguments.first()?.clone();
                let star = !lists.terminators.get(&list.terminator).copied()?;
                Some((list.terminator.clone(), sort, element, star))
            })
            .collect::<Vec<_>>();
        // A list reads no text if it is a `List`, or if its elements can be no text: a fixed
        // point, since a list's element can be a list.
        let mut silent = all.iter().map(|(_, _, _, star)| *star).collect::<Vec<_>>();
        let nested = |silent: &[bool], element: &Sort| {
            all.iter()
                .zip(silent)
                .any(|((_, sort, _, _), silent)| *silent && data.less_than_eq(sort, element))
        };
        loop {
            let next = all
                .iter()
                .zip(&silent)
                .map(|((_, _, element, _), was)| *was || nested(&silent, element))
                .collect::<Vec<_>>();
            if next == silent {
                break;
            }
            silent = next;
        }
        Self {
            lists: all
                .iter()
                .zip(&silent)
                .filter(|(_, silent)| **silent)
                .map(|((terminator, sort, element, _), _)| {
                    (terminator.clone(), sort.clone(), nested(&silent, element))
                })
                .collect(),
        }
    }

    /// Whether no text, at `place`, reads back as the `List` terminator `terminator` of sort
    /// `sort` alone (module documentation).
    fn written(
        &self,
        data: &PrintData,
        terminator: &str,
        sort: Option<&Sort>,
        place: &Place,
    ) -> bool {
        if !place.left || !place.right || place.role == Role::Sole {
            return false;
        }
        let Some(position) = (match &place.position {
            Position::Root => sort,
            Position::At(position) => Some(position),
            Position::Unknown => None,
        }) else {
            return false;
        };
        // The lists that read no text at the position: none may read it as a one-element list,
        // and the parser reads it as the terminator every other one's overloads.
        let readings = self
            .lists
            .iter()
            .filter(|(other, other_sort, _)| {
                other == terminator || data.less_than_eq(other_sort, position)
            })
            .collect::<Vec<_>>();
        if readings.iter().any(|(_, _, nested)| *nested) {
            return false;
        }
        let greater = |lesser: &str, greater: &str| {
            lesser == greater
                || data
                    .overloads
                    .get(lesser)
                    .is_some_and(|overloads| overloads.contains(greater))
        };
        readings.iter().any(|(least, _, _)| {
            readings.iter().all(|(other, _, _)| greater(least, other)) && greater(least, terminator)
        })
    }
}
