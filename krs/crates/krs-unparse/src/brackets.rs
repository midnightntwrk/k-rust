//! Bracket insertion: the simple, linear algorithm of K's printers (`addBrackets.cpp` of the LLVM
//! backend, `AddBrackets.java` of the frontend).
//!
//! A child needs brackets when priority, associativity or sorts forbid it at its position, or when
//! it begins (ends) with a non-terminal and could be captured by the nearest production to its left
//! (right) that ends (begins) with a non-terminal. The algorithm is unsound by design, exactly as
//! K's: it is what `krun --output pretty` and `kast --output program` use. Injections are removed.

use k_rust::kore::ast::Sort;

use crate::data::PrintData;
use crate::node::{App, Node, Sym};

const BARE_LEFT: u8 = 1;
const BARE_RIGHT: u8 = 2;

/// What to do when a child needs brackets and its sort has no bracket production.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Fallback {
    /// `kprint`: a bare `( .. )`.
    Parentheses,
    /// `kast --output program`: print the child as it is.
    Nothing,
}

pub(crate) struct Brackets<'a> {
    data: &'a PrintData,
    fallback: Fallback,
}

/// `get_nt_position_in_prod`: the item index of the `position`-th non-terminal.
fn item_position(terminals: &[u8], position: usize) -> usize {
    let mut nonterminal = 0;
    for (index, item) in terminals.iter().enumerate() {
        if *item == b'0' {
            if nonterminal == position {
                return index;
            }
            nonterminal += 1;
        }
    }
    terminals.len()
}

fn terminal_at(terminals: &[u8], position: Option<usize>) -> bool {
    position.is_some_and(|position| terminals.get(position) == Some(&b'1'))
}

impl<'a> Brackets<'a> {
    pub fn new(data: &'a PrintData, fallback: Fallback) -> Self {
        Self { data, fallback }
    }

    fn terminals(&self, sym: &Sym) -> Option<&'a [u8]> {
        self.data.terminals.get(&sym.name).map(String::as_bytes)
    }

    /// The fixity of the `position`-th argument within `sym`'s production.
    fn argument_fixity(&self, position: usize, sym: &Sym) -> u8 {
        let Some(terminals) = self.terminals(sym) else {
            return 0;
        };
        let at = item_position(terminals, position);
        let mut fixity = 0;
        if !terminal_at(terminals, at.checked_add(1)) {
            fixity |= BARE_RIGHT;
        }
        if !terminal_at(terminals, at.checked_sub(1)) {
            fixity |= BARE_LEFT;
        }
        fixity
    }

    /// Whether `sym`'s production begins and ends with a non-terminal.
    fn fixity(&self, sym: &Sym) -> u8 {
        let Some(terminals) = self.terminals(sym) else {
            return 0;
        };
        let mut fixity = 0;
        if terminals.first() == Some(&b'0') {
            fixity |= BARE_LEFT;
        }
        if terminals.last() == Some(&b'0') {
            fixity |= BARE_RIGHT;
        }
        fixity
    }

    fn is_priority_wrong(&self, outer: &App, inner: &App, position: usize) -> bool {
        let outer_name = outer.sym.name.as_str();
        let inner_name = inner.sym.name.as_str();
        if let (Some(inner_sort), Some(outer_sort)) = (
            return_sort(inner),
            argument_sort(
                &outer.sym,
                position,
                outer.args.first().and_then(Node::sort),
            ),
        ) && !self.data.less_than_eq(&inner_sort, &outer_sort)
        {
            return true;
        }
        if self
            .data
            .priorities
            .get(outer_name)
            .is_some_and(|lower| lower.contains(inner_name))
        {
            return true;
        }
        let Some(terminals) = self.terminals(&outer.sym) else {
            return false;
        };
        let at = item_position(terminals, position);
        if self
            .data
            .left_assoc
            .get(outer_name)
            .is_some_and(|names| names.contains(inner_name))
            && at + 1 == terminals.len()
        {
            return true;
        }
        self.data
            .right_assoc
            .get(outer_name)
            .is_some_and(|names| names.contains(inner_name))
            && at == 0
    }

    fn requires_bracket(
        &self,
        outer: &App,
        left_capture: Option<&App>,
        right_capture: Option<&App>,
        inner: &Node,
        position: usize,
    ) -> bool {
        let Node::App(inner) = inner else {
            return false;
        };
        let inner_name = inner.sym.name.as_str();
        if inner_name == outer.sym.name && self.data.assoc.contains(inner_name) {
            return false;
        }
        if inner_name == "\\dv" {
            return false;
        }
        if self.argument_fixity(position, &outer.sym) == 0 {
            return false;
        }
        if self.is_priority_wrong(outer, inner, position) {
            return true;
        }
        if self.terminals(&inner.sym) == Some(b"0".as_slice()) {
            return false;
        }
        let inner_fixity = self.fixity(&inner.sym);
        if inner_fixity & BARE_RIGHT != 0
            && let Some(capture) = right_capture
        {
            let inverse =
                self.is_priority_wrong(inner, capture, inner.args.len().saturating_sub(1));
            if !inverse && self.fixity(&capture.sym) & BARE_LEFT != 0 {
                return true;
            }
        }
        if inner_fixity & BARE_LEFT != 0
            && let Some(capture) = left_capture
        {
            let inverse = self.is_priority_wrong(inner, capture, 0);
            return !inverse && self.fixity(&capture.sym) & BARE_RIGHT != 0;
        }
        false
    }

    fn wrap(&self, inner: &Node, outer: &App, position: usize) -> Node {
        let outer_sort = argument_sort(
            &outer.sym,
            position,
            outer.args.first().and_then(Node::sort),
        );
        let inner_sort = match inner {
            Node::App(app) => return_sort(app),
            _ => inner.sort().cloned(),
        };
        if let (Some(outer_sort), Some(inner_sort)) = (&outer_sort, &inner_sort) {
            for (sort, symbols) in &self.data.brackets {
                if !self.data.less_than_eq(sort, outer_sort) {
                    continue;
                }
                for symbol in symbols {
                    if symbol
                        .argument
                        .as_ref()
                        .is_some_and(|argument| self.data.less_than_eq(inner_sort, argument))
                    {
                        let mut sym = Sym::new(symbol.name.clone(), Vec::new());
                        sym.arguments = symbol.argument.iter().cloned().collect();
                        sym.sort = Some(sort.clone());
                        return Node::app(sym, vec![inner.clone()]);
                    }
                }
            }
        }
        match self.fallback {
            Fallback::Nothing => inner.clone(),
            Fallback::Parentheses => {
                let mut sym = Sym::new("bracket", Vec::new());
                sym.sort = inner_sort;
                Node::app(sym, vec![inner.clone()])
            }
        }
    }

    fn child(
        &self,
        inner: &Node,
        outer: &App,
        left_capture: Option<&App>,
        right_capture: Option<&App>,
        position: usize,
    ) -> Node {
        if let Node::App(app) = inner
            && app.sym.name == "inj"
            && let Some(child) = app.args.first()
        {
            return self.child(child, outer, left_capture, right_capture, position);
        }
        if self.requires_bracket(outer, left_capture, right_capture, inner, position) {
            self.wrap(inner, outer, position)
        } else {
            inner.clone()
        }
    }

    /// `add_brackets(t, previous_left_capture, previous_right_capture)`.
    pub fn add(
        &self,
        node: &Node,
        left_capture: Option<&App>,
        right_capture: Option<&App>,
    ) -> Node {
        let Node::App(outer) = node else {
            return node.clone();
        };
        if outer.sym.name == "\\dv" {
            return node.clone();
        }
        let outer_fixity = self.fixity(&outer.sym);
        let last = outer.args.len().saturating_sub(1);
        let args = outer
            .args
            .iter()
            .enumerate()
            .map(|(position, inner)| {
                let left = if position == 0 && outer_fixity & BARE_LEFT != 0 {
                    left_capture
                } else {
                    Some(outer)
                };
                let right = if position == last && outer_fixity & BARE_RIGHT != 0 {
                    right_capture
                } else {
                    Some(outer)
                };
                let child = self.child(inner, outer, left, right, position);
                self.add(&child, left, right)
            })
            .collect();
        Node::app(outer.sym.clone(), args)
    }
}

const SAME_SORT_CONNECTIVES: &[&str] = &[
    "\\and",
    "\\not",
    "\\or",
    "\\implies",
    "\\iff",
    "\\ceil",
    "\\floor",
    "\\equals",
    "\\in",
    "\\next",
    "\\rewrites",
    "weakAlwaysFinally",
    "weakExistsFinally",
    "allPathGlobally",
];

/// `get_arg_sort`: the sort expected at argument `position` of `sym`.
fn argument_sort(sym: &Sym, position: usize, first_argument: Option<&Sort>) -> Option<Sort> {
    if !sym.is_builtin() {
        return sym.arguments.get(position).cloned();
    }
    let name = sym.name.as_str();
    if SAME_SORT_CONNECTIVES.contains(&name) {
        return sym.formals.first().cloned();
    }
    match name {
        "\\forall" | "\\exists" if position == 0 => first_argument.cloned(),
        "\\forall" | "\\exists" => sym.formals.first().cloned(),
        "\\mu" | "\\nu" => first_argument.cloned(),
        _ => None,
    }
}

/// `get_return_sort`: the sort of an application.
fn return_sort(app: &App) -> Option<Sort> {
    let sym = &app.sym;
    if !sym.is_builtin() {
        return sym.sort.clone();
    }
    match sym.name.as_str() {
        "\\top" | "\\bottom" | "\\and" | "\\not" | "\\or" | "\\implies" | "\\iff" | "\\exists"
        | "\\forall" | "\\next" | "\\rewrites" | "weakAlwaysFinally" | "weakExistsFinally"
        | "allPathGlobally" => sym.formals.first().cloned(),
        "\\ceil" | "\\floor" | "\\equals" | "\\in" => sym.formals.get(1).cloned(),
        "\\mu" | "\\nu" => app.args.first().and_then(Node::sort).cloned(),
        _ => None,
    }
}
