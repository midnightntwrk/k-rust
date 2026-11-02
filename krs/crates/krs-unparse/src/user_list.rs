//! A user list printed in its program spelling.
//!
//! A user list is a sort declared `List{Int, ","}` or `NeList{Int, ","}`: a cons production
//! `Int "," Ints` and a terminator `".Ints"`, both `userList`. A program writes a list as its
//! elements with the separator between them, and the empty list as no text: the program parser
//! reads `1, 2` as `intsCons(1, intsCons(2, intsNil))`, putting the terminator in where the
//! elements end, and reads no text at all at a `List`'s position as its terminator alone, or as
//! a one-element list whose element is no text. `.Ints`, the terminator's own text, is K's rule
//! syntax, which no program grammar reads, and a `NeList` has no empty spelling at all.
//!
//! The program spelling leaves out text the K spelling writes, so a print takes it only where
//! what is left reads back as the term. Each judgement below is made on the grammar the
//! definition declares, before the text exists, and is sufficient, not necessary:
//!
//! - A cons whose tail is its list's terminator prints as its element alone ([`LAST`]) except
//!   where the text right after the list, through every production it is the last item of,
//!   would continue it: a terminal beginning with the list's separator, unless it is the
//!   separator alone and the argument after it can be neither no text nor a list with that
//!   separator (`Ints "," Ints` writes `[1, 2] [3]` as `1 , 2 , 3`, which `[1] [2, 3]` writes
//!   too; `frame({items}, {env})` with a `Map` `env` reads `1 , .Map` one way only), or, for a
//!   list that juxtaposes its elements, another argument's text (`Gaps Gaps` writes `[1] [2, 3]`
//!   as `1 2 3`). A list with a separator continues only after one, so an argument's text right
//!   after it (`Ints Ints` writes `[1] [2]` as `1 2`) is judged as the text of any two
//!   adjacent arguments is, by the grammar's own reading of them.
//! - A terminator alone prints as no text ([`EMPTY`]) only where all four hold:
//!   - its list is a `List`;
//!   - a non-empty terminal, or the edge of the text, stands right before it and right after it,
//!     through every production it is the first (the last) item of: beside a neighbour's text,
//!     the parser may read the empty text on the neighbour's other side (`Ints Ints` writes
//!     `[] [1]` as it writes `[1] []`);
//!   - no text has exactly one reading where it stands ([`Spelling`]): at the position of the
//!     largest term around the terminator that prints nothing else (through an injection, a
//!     production whose format writes only its argument, or a list whose one element it is),
//!     or, right after a list's separator, as that list's next element. Readings are counted
//!     over every production of the definition, a sort reading what the sorts below it read: a
//!     `List` reads no text as its terminator, and as a one-element list where its elements can
//!     be no text (`List{Ints, ";"}` reads it as `[]` and as `[[]]`); a production whose
//!     format writes no text of its own reads it where each of its arguments can. A greater
//!     overload's no-text production is one reading with its more specific overload's, which
//!     the definition's overload axioms equate with it (`Vals`'s terminator in an `Exps`, K's
//!     `Vals` idiom);
//!   - no other production writes the text of the production whose terminals delimit it, with
//!     the no text left out ([`Spelling::competes`]): `f()` beside `f({args})` reads the empty
//!     `args` as that other production.
//!
//! Elsewhere the list keeps K's spelling there, its terminator printed as K's `.Ints`, and the
//! print says so ([`crate::Warning::EmptyList`]), as it does for a child no bracket of the
//! definition groups. A cons whose tail is no list (a variable, a function's application) has no
//! program text either; it prints as K writes it, and the read-back judges it.
//!
//! The judgement does not see a production whose arguments write the delimiting production's
//! terminals (`S ::= "f" Paren` beside `f()`), or a reading across the delimiting production's
//! text. A grammar ambiguous so at a print is ambiguous at every program that writes the term
//! too; the read-back (`KRS_CHECK_PRINTS`, K7) judges those prints, and a [`crate::Mode::Program`]
//! print that does not read back is printed in K's spelling with the warning
//! ([`crate::ListSpelling::K`], `Semantics::unparse_program` in krs-exec).

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use k_rust::kore::ast::Sort;

use crate::data::PrintData;
use crate::node::{App, Node, Sym};

/// The symbol of a list's last element, its one argument, printed alone: a cons whose tail is
/// the terminator. Its argument sort is the element's, its sort the list's.
pub(crate) const LAST: &str = "#krs-list-last";

/// The symbol of the empty list printed as no text. Its sort is the list's.
pub(crate) const EMPTY: &str = "#krs-list-empty";

/// More than one reading: counts saturate here.
const MANY: u8 = 2;

/// The user lists of a definition, by their symbols' KORE names.
#[derive(Clone, Debug, Default)]
pub(crate) struct UserLists {
    /// Each list the program parser reads in its program spelling, by its cons symbol.
    conses: BTreeMap<String, UserList>,
    /// Each such list's terminator, and whether its list is a `NeList`.
    terminators: BTreeMap<String, bool>,
    /// The cons of every user list, these and any other (a parametric or left-recursive one),
    /// and its separator's text, without white space: a one-element list of each is its
    /// element's text.
    every_cons: BTreeMap<String, String>,
}

/// One user list, by its cons symbol.
#[derive(Clone, Debug)]
struct UserList {
    terminator: String,
    /// Its separator's text, without white space; empty for `List{Int, ""}`, which juxtaposes
    /// its elements.
    separator: String,
}

impl UserLists {
    /// Add the list whose cons is `cons`, separator `separator` and terminator `terminator`.
    pub fn insert(&mut self, cons: String, terminator: String, separator: &str, non_empty: bool) {
        let separator = without_space(separator);
        self.terminators.insert(terminator.clone(), non_empty);
        self.every_cons.insert(cons.clone(), separator.clone());
        self.conses.insert(
            cons,
            UserList {
                terminator,
                separator,
            },
        );
    }

    /// Add the cons of a list the program parser reads by its productions as they are written.
    pub fn insert_other(&mut self, cons: String, separator: &str) {
        self.every_cons
            .entry(cons)
            .or_insert_with(|| without_space(separator));
    }
}

impl UserList {
    const fn separated(&self) -> bool {
        !self.separator.is_empty()
    }

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

fn without_space(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

/// One part of a format, as it prints: a terminal's text (white space and layout codes left
/// out) or an argument (from 0).
#[derive(Clone, Debug, Eq, PartialEq)]
enum Piece {
    Text(String),
    Argument(usize),
}

/// The parts of `format`, a `kprint` format: `%N` the N-th argument, `%n %i %d %c %r` layout
/// and colour, which print no text, any other `%x` the character `x`. Adjacent texts are one.
fn pieces(format: &str) -> Vec<Piece> {
    let mut pieces = Vec::new();
    let mut text = String::new();
    let mut characters = format.chars().peekable();
    while let Some(character) = characters.next() {
        let literal = if character == '%' {
            match characters.next() {
                Some(digit) if digit.is_ascii_digit() => {
                    let mut number = String::from(digit);
                    while let Some(&digit) = characters.peek().filter(|c| c.is_ascii_digit()) {
                        number.push(digit);
                        characters.next();
                    }
                    if !text.is_empty() {
                        pieces.push(Piece::Text(std::mem::take(&mut text)));
                    }
                    if let Some(index) = number
                        .parse::<usize>()
                        .ok()
                        .and_then(|number| number.checked_sub(1))
                    {
                        pieces.push(Piece::Argument(index));
                    }
                    continue;
                }
                Some('n' | 'i' | 'd' | 'c' | 'r') | None => continue,
                Some(other) => other,
            }
        } else {
            character
        };
        if !literal.is_whitespace() {
            text.push(literal);
        }
    }
    if !text.is_empty() {
        pieces.push(Piece::Text(text));
    }
    pieces
}

/// A part of a production's printed text, for comparing two productions' texts: one character
/// of a terminal, or an argument, which may write no text where its sort reads no text.
#[derive(Clone, Copy, Debug)]
enum Unit {
    Character(char),
    Argument { silent: bool },
}

/// A production of the definition, by its symbol: its sort and its printed text.
#[derive(Clone, Debug)]
struct Production {
    symbol: String,
    sort: Sort,
    units: Vec<Unit>,
}

/// What a production with no text of its own reads no text as.
#[derive(Clone, Debug)]
enum Silent {
    /// A `List`'s terminator, or a production that writes nothing at all: one reading.
    Once,
    /// A list's cons, as a one-element list: one reading per reading of its element, and many
    /// where its separator is no text and its element can be no text.
    OneElement { element: Sort, separated: bool },
    /// A production whose format writes only its arguments: one reading per combination of
    /// theirs.
    Arguments(Vec<Sort>),
}

/// The user lists, and what the definition's grammar reads no text as ([`Self::new`]).
#[derive(Clone, Debug, Default)]
pub(crate) struct Spelling {
    lists: UserLists,
    /// Each printable symbol's format, by parts.
    pieces: BTreeMap<String, Vec<Piece>>,
    /// Each sort whose own productions read no text, and how many ways (up to [`MANY`]).
    own: BTreeMap<Sort, u8>,
    /// A parametric production can write no text: no count is known.
    unknown: bool,
    /// The definition's productions, whose texts [`Self::competes`] compares.
    productions: Vec<Production>,
}

impl Spelling {
    /// The spelling of `lists` in the grammar `data` describes: the readings of no text at
    /// each sort, the least fixed point over the productions that write no text of their own.
    pub fn new(data: &PrintData, lists: UserLists) -> Self {
        if lists.conses.is_empty() {
            return Self::default();
        }
        let pieces = data
            .format
            .iter()
            .map(|(symbol, format)| (symbol.clone(), self::pieces(format)))
            .collect::<BTreeMap<_, _>>();
        let (silent, unknown) = silent_productions(data, &lists, &pieces);
        let mut spelling = Self {
            lists,
            pieces,
            own: BTreeMap::new(),
            unknown,
            productions: Vec::new(),
        };
        // The counts only grow, and saturate, so the fixed point is reached.
        loop {
            let mut own = BTreeMap::<Sort, u8>::new();
            for (sort, kind) in &silent {
                let count = match kind {
                    Silent::Once => 1,
                    Silent::OneElement { element, separated } => {
                        spelling.next_element(data, element, *separated)
                    }
                    Silent::Arguments(arguments) => {
                        arguments.iter().fold(1_u8, |product, argument| {
                            product
                                .saturating_mul(spelling.count(data, argument))
                                .min(MANY)
                        })
                    }
                };
                if count > 0 {
                    let entry = own.entry(sort.clone()).or_default();
                    *entry = entry.saturating_add(count).min(MANY);
                }
            }
            if own == spelling.own {
                break;
            }
            spelling.own = own;
        }
        spelling.productions = spelling.productions(data);
        spelling
    }

    /// The definition's productions, each by its printed text ([`Unit`]).
    fn productions(&self, data: &PrintData) -> Vec<Production> {
        self.pieces
            .iter()
            .filter(|(symbol, _)| symbol.as_str() != "inj" && !symbol.starts_with('\\'))
            .filter_map(|(symbol, parts)| {
                let declaration = data.declarations.get(symbol)?;
                let units = parts
                    .iter()
                    .flat_map(|piece| match piece {
                        Piece::Text(text) => text.chars().map(Unit::Character).collect(),
                        Piece::Argument(index) => vec![Unit::Argument {
                            silent: declaration
                                .arguments
                                .get(*index)
                                .is_none_or(|sort| self.count(data, sort) > 0),
                        }],
                    })
                    .collect();
                Some(Production {
                    symbol: symbol.clone(),
                    sort: declaration.result.clone(),
                    units,
                })
            })
            .collect()
    }

    /// How many ways no text reads at `sort`: as each sort at or below it reads it.
    fn count(&self, data: &PrintData, sort: &Sort) -> u8 {
        if self.unknown {
            return MANY;
        }
        self.own
            .iter()
            .filter(|(own, _)| data.less_than_eq(own, sort))
            .fold(0_u8, |sum, (_, count)| sum.saturating_add(*count).min(MANY))
    }

    /// How many ways no text reads as a list's next element, of sort `element`: as the element,
    /// and, where the list juxtaposes its elements, as any number of them.
    fn next_element(&self, data: &PrintData, element: &Sort, separated: bool) -> u8 {
        match self.count(data, element) {
            0 => 0,
            count if separated => count,
            _ => MANY,
        }
    }

    /// Whether text of sort `next`, right after a list's separator `separator`, can continue
    /// the list: `next` reads no text, or holds a list with that separator.
    fn continues(&self, data: &PrintData, separator: &str, next: &Sort) -> bool {
        self.count(data, next) > 0
            || self.lists.every_cons.iter().any(|(cons, other)| {
                other == separator
                    && data
                        .declarations
                        .get(cons)
                        .is_none_or(|declaration| data.less_than_eq(&declaration.result, next))
            })
    }

    /// How many ways no text reads as `reading` says.
    fn readings(&self, data: &PrintData, reading: &Reading) -> u8 {
        match reading {
            Reading::At(sort) => self.count(data, sort),
            Reading::Element { element, separated } => self.next_element(data, element, *separated),
            Reading::Unknown => MANY,
        }
    }

    /// Whether a production other than `host`'s writes the text of `host`'s production with
    /// its argument `host.index` left out, where `host` stands: its characters the same, its
    /// arguments matching `host`'s or writing no text where their sorts read no text, `host`'s
    /// other arguments matching any of its text, but a token's, which is its own text
    /// ([`writes_same`]). An overload of `host`'s symbol is one term with it.
    fn competes(&self, data: &PrintData, host: &Host) -> bool {
        let Some(parts) = self.pieces.get(&host.symbol) else {
            return true;
        };
        let declaration = data.declarations.get(&host.symbol);
        let written = parts
            .iter()
            .flat_map(|piece| match piece {
                Piece::Text(text) => text.chars().map(Unit::Character).collect(),
                Piece::Argument(index) if *index == host.index => Vec::new(),
                Piece::Argument(index) => match host.tokens.get(*index) {
                    Some(Some(token)) => token.chars().map(Unit::Character).collect(),
                    _ => vec![Unit::Argument {
                        silent: declaration
                            .and_then(|declaration| declaration.arguments.get(*index))
                            .is_none_or(|sort| self.count(data, sort) > 0),
                    }],
                },
            })
            .collect::<Vec<_>>();
        let related = |other: &str| {
            data.overloads
                .get(other)
                .is_some_and(|greater| greater.contains(&host.symbol))
                || data
                    .overloads
                    .get(&host.symbol)
                    .is_some_and(|greater| greater.contains(other))
        };
        self.productions.iter().any(|production| {
            production.symbol != host.symbol
                && !related(&production.symbol)
                && host
                    .position
                    .as_ref()
                    .is_none_or(|position| data.less_than_eq(&production.sort, position))
                && writes_same(&written, &production.units)
        })
    }
}

/// The productions of `data` that write no text of their own, by their sorts, and what each
/// reads no text as; beside whether a parametric one can write no text, which leaves the counts
/// unknown. A greater overload's no-text production reads as its more specific overload's,
/// which is counted at the more specific sort, below the greater one, so it is left out.
fn silent_productions(
    data: &PrintData,
    lists: &UserLists,
    pieces: &BTreeMap<String, Vec<Piece>>,
) -> (Vec<(Sort, Silent)>, bool) {
    let mut unknown = false;
    let mut silent = Vec::<(String, Sort, Silent)>::new();
    for (symbol, declaration) in &data.declarations {
        if symbol == "inj" || symbol.starts_with('\\') {
            continue;
        }
        let Some(parts) = pieces.get(symbol) else {
            continue;
        };
        let kind = if let Some(&non_empty) = lists.terminators.get(symbol) {
            if non_empty {
                continue;
            }
            Silent::Once
        } else if let Some(separator) = lists.every_cons.get(symbol) {
            let Some(element) = declaration
                .arguments
                .iter()
                .find(|argument| **argument != declaration.result)
                .or_else(|| declaration.arguments.first())
            else {
                continue;
            };
            Silent::OneElement {
                element: element.clone(),
                separated: !separator.is_empty(),
            }
        } else if parts.iter().any(|piece| matches!(piece, Piece::Text(_))) {
            continue;
        } else if declaration.arguments.is_empty() {
            Silent::Once
        } else {
            Silent::Arguments(declaration.arguments.clone())
        };
        if !declaration.parameters.is_empty() {
            unknown = true;
            continue;
        }
        silent.push((symbol.clone(), declaration.result.clone(), kind));
    }
    let once = silent
        .iter()
        .filter(|(_, _, kind)| matches!(kind, Silent::Once))
        .map(|(symbol, _, _)| symbol.clone())
        .collect::<BTreeSet<_>>();
    let silent = silent
        .into_iter()
        .filter(|(symbol, _, kind)| {
            !matches!(kind, Silent::Once)
                || !once.iter().any(|lesser| {
                    data.overloads
                        .get(lesser)
                        .is_some_and(|greater| greater.contains(symbol))
                })
        })
        .map(|(_, sort, kind)| (sort, kind))
        .collect();
    (silent, unknown)
}

/// Whether some text is written both by `host`, a production's text with an argument left out,
/// and by `other`, another production's: `host`'s arguments write any text, or none where they
/// can be no text; `other`'s arguments are written by `host`'s, or write no text where they can.
fn writes_same(host: &[Unit], other: &[Unit]) -> bool {
    // `reach[i][j]`: the first `i` units of `host` can write what the first `j` of `other` do.
    let mut reach = vec![vec![false; other.len() + 1]; host.len() + 1];
    reach[0][0] = true;
    for i in 0..=host.len() {
        for j in 0..=other.len() {
            if !reach[i][j] {
                continue;
            }
            if let Some(Unit::Argument { silent: true }) = other.get(j) {
                reach[i][j + 1] = true;
            }
            match host.get(i) {
                Some(Unit::Argument { silent }) => {
                    if *silent {
                        reach[i + 1][j] = true;
                    }
                    for reached in &mut reach[i + 1][j + 1..] {
                        *reached = true;
                    }
                }
                Some(Unit::Character(character)) => {
                    if let Some(Unit::Character(written)) = other.get(j)
                        && written == character
                    {
                        reach[i + 1][j + 1] = true;
                    }
                }
                None => {}
            }
        }
    }
    reach[host.len()][other.len()]
}

/// What no text standing at a place reads as.
#[derive(Clone, Debug)]
enum Reading {
    /// A term of this sort.
    At(Sort),
    /// A list's next element, after its separator (or, with none, after an element).
    Element { element: Sort, separated: bool },
    /// Nothing known.
    Unknown,
}

/// What stands right after a node's text.
#[derive(Clone, Debug, Eq, PartialEq)]
enum After {
    /// The end of the printed text.
    End,
    /// A non-empty terminal's text, without white space, and the sort of the argument right after
    /// it in the same production, if one is.
    Terminal(String, Option<Sort>),
    /// Another argument's text.
    Text,
}

impl After {
    const fn delimits(&self) -> bool {
        !matches!(self, Self::Text)
    }

    /// Whether this ends a list whose separator is `separator` (without white space), after
    /// its last element, in `spelling`: where the list juxtaposes its elements, it delimits;
    /// where it begins with the separator, it is the separator alone, and the argument after
    /// it reads neither no text nor a list with that separator, so that the list cannot take
    /// any of that argument's text as its next elements (`frame({items}, {env})` with a `Map`
    /// `env`; not `pair({a}, {b})` with two `Ints`).
    fn ends(&self, separator: &str, data: &PrintData, spelling: &Spelling) -> bool {
        match self {
            Self::End => true,
            Self::Terminal(text, next) => {
                separator.is_empty()
                    || !text.starts_with(separator)
                    || (text == separator
                        && next
                            .as_ref()
                            .is_some_and(|next| !spelling.continues(data, separator, next)))
            }
            Self::Text => !separator.is_empty(),
        }
    }
}

/// The production whose terminals delimit a no text: its symbol, the argument the no text
/// stands in, the sort its application stands at, where known, and the text of each of its
/// arguments that is a token, which prints as it is.
#[derive(Debug)]
struct Host {
    symbol: String,
    index: usize,
    position: Option<Sort>,
    tokens: Rc<Vec<Option<String>>>,
}

/// The text of each of `app`'s arguments that is a token (below its injections), as it prints,
/// without white space; a string's or a byte string's is quoted, and left unknown.
fn tokens(data: &PrintData, app: &App) -> Rc<Vec<Option<String>>> {
    Rc::new(
        app.args
            .iter()
            .map(|mut argument| {
                while let Node::App(App { sym, args }) = argument
                    && sym.name == "inj"
                    && let [inner] = args.as_slice()
                {
                    argument = inner;
                }
                let Node::App(App { sym, args }) = argument else {
                    return None;
                };
                let (true, [Node::Str(text)], Some(Sort::Application { name, .. })) =
                    (sym.name == "\\dv", args.as_slice(), sym.formals.first())
                else {
                    return None;
                };
                if matches!(
                    data.hooks.get(name).map(String::as_str),
                    Some("STRING.String" | "BYTES.Bytes")
                ) {
                    return None;
                }
                Some(without_space(&String::from_utf8_lossy(text)))
            })
            .collect(),
    )
}

/// Where a node stands in the printed text.
#[derive(Clone, Debug)]
struct Place {
    /// The sort its position declares, where known.
    position: Option<Sort>,
    /// A non-empty terminal, or the start of the text, stands right before its text.
    left: bool,
    after: After,
    /// What its text reads as where it is no text: the reading of the largest term around it
    /// that prints nothing else.
    reading: Reading,
    host: Option<Rc<Host>>,
    /// A cons's tail: a cons there continues a list, after its separator.
    tail: bool,
}

/// A delimiting production's judgement ([`Spelling::competes`]), by what it depends on.
type Judged = (String, usize, Option<Sort>, Rc<Vec<Option<String>>>);

/// Rewrite `node`, a tree ready to print, so that each user list prints in its program
/// spelling where that reads back as it (module documentation): a cons whose tail is its
/// terminator becomes [`LAST`] of its element, and a terminator alone [`EMPTY`]. The K names of
/// the sorts of the terminators left in K's spelling are added to `unwritten`. With `spelled`
/// false, every list keeps K's spelling. An application of a symbol with no format is left as it
/// is: it prints as KAST, which writes lists in K's spelling.
pub(crate) fn spell(
    data: &PrintData,
    spelling: &Spelling,
    node: &mut Node,
    unwritten: &mut BTreeSet<String>,
    spelled: bool,
) {
    let lists = &spelling.lists;
    if lists.conses.is_empty() {
        return;
    }
    if !spelled {
        let mut stack = vec![&*node];
        while let Some(node) = stack.pop() {
            if let Node::App(app) = node {
                if lists.terminators.contains_key(&app.sym.name) {
                    unwritten.insert(crate::brackets::sort_name(app.sym.sort.as_ref()));
                }
                stack.extend(&app.args);
            }
        }
        return;
    }
    let root = Place {
        position: None,
        left: true,
        after: After::End,
        reading: node
            .as_app()
            .and_then(|app| app.sym.sort.clone())
            .map_or(Reading::Unknown, Reading::At),
        host: None,
        tail: false,
    };
    let mut judge = Speller {
        data,
        spelling,
        competing: BTreeMap::new(),
    };
    // Iterative: a cons list or a `~>` sequence can be deeper than the stack.
    let mut stack: Vec<(&mut Node, Place)> = vec![(node, root)];
    while let Some((node, place)) = stack.pop() {
        let Some(app) = node.as_app() else {
            continue;
        };
        if let Some(&non_empty) = lists.terminators.get(&app.sym.name) {
            if !non_empty && judge.no_text(&place) {
                let mut sym = Sym::new(EMPTY, Vec::new());
                sym.sort.clone_from(&app.sym.sort);
                *node = Node::app(sym, Vec::new());
            } else {
                unwritten.insert(crate::brackets::sort_name(app.sym.sort.as_ref()));
            }
            continue;
        }
        if let Some(list) = lists
            .conses
            .get(&app.sym.name)
            .filter(|_| app.args.len() == 2)
        {
            judge.cons(list, node, place, &mut stack);
            continue;
        }
        let Node::App(app) = node else {
            continue;
        };
        let name = app.sym.name.as_str();
        match name {
            "\\dv" | crate::instance::KORE_TEXT => {}
            "inj" => {
                // An injection prints its argument: it stands where the injection does, at the
                // injection's target.
                let target = app.sym.formals.get(1).cloned();
                let reading = match (&place.reading, &target) {
                    (Reading::Unknown, Some(target)) => Reading::At(target.clone()),
                    (reading, _) => reading.clone(),
                };
                let inner = Place {
                    position: target,
                    reading,
                    ..place
                };
                stack.extend(
                    app.args
                        .iter_mut()
                        .map(|argument| (argument, inner.clone())),
                );
            }
            _ => {
                if let Some(parts) = spelling.pieces.get(name) {
                    let tokens = tokens(data, app);
                    let places = (0..app.args.len())
                        .map(|index| argument_place(app, parts, index, &place, &tokens))
                        .collect::<Vec<_>>();
                    stack.extend(app.args.iter_mut().zip(places));
                }
            }
        }
    }
}

/// The judgements [`spell`] makes on one print.
struct Speller<'a> {
    data: &'a PrintData,
    spelling: &'a Spelling,
    /// Each delimiting production's judgement, once per print.
    competing: BTreeMap<Judged, bool>,
}

impl Speller<'_> {
    /// Whether a `List`'s terminator standing at `place` prints as no text (module
    /// documentation).
    fn no_text(&mut self, place: &Place) -> bool {
        !place.tail
            && place.left
            && place.after.delimits()
            && self.spelling.readings(self.data, &place.reading) == 1
            && place.host.as_ref().is_none_or(|host| {
                let (data, spelling) = (self.data, self.spelling);
                !*self
                    .competing
                    .entry((
                        host.symbol.clone(),
                        host.index,
                        host.position.clone(),
                        host.tokens.clone(),
                    ))
                    .or_insert_with(|| spelling.competes(data, host))
            })
    }

    /// Spell `node`, a cons of `list` standing at `place`, pushing its parts on `stack`: as its
    /// element alone where its tail is the terminator and nothing after the list continues it.
    fn cons<'n>(
        &self,
        list: &UserList,
        node: &'n mut Node,
        place: Place,
        stack: &mut Vec<(&'n mut Node, Place)>,
    ) {
        let Node::App(app) = &mut *node else {
            unreachable!("an application")
        };
        let element_sort = app.sym.arguments.first().cloned();
        if list.terminated_by(self.data, &app.args[1])
            && place.after.ends(&list.separator, self.data, self.spelling)
        {
            let element = app.args.swap_remove(0);
            let mut sym = Sym::new(LAST, Vec::new());
            sym.arguments = element_sort.iter().cloned().collect();
            sym.sort = app.sym.sort.take();
            *node = Node::app(sym, vec![element]);
            let Node::App(alone) = node else {
                unreachable!("just built")
            };
            // The element's text is the list's; after a separator, the next element's.
            let reading = match (&element_sort, place.tail) {
                (Some(element), true) => Reading::Element {
                    element: element.clone(),
                    separated: list.separated(),
                },
                (None, true) => Reading::Unknown,
                (_, false) => place.reading.clone(),
            };
            let element_place = Place {
                position: element_sort,
                reading,
                tail: false,
                ..place
            };
            stack.extend(
                alone
                    .args
                    .iter_mut()
                    .map(|element| (element, element_place.clone())),
            );
            return;
        }
        let Node::App(app) = node else {
            unreachable!("an application")
        };
        let tokens = tokens(self.data, app);
        let host = |index| {
            Some(Rc::new(Host {
                symbol: app.sym.name.clone(),
                index,
                position: place.position.clone(),
                tokens: tokens.clone(),
            }))
        };
        let element_place = Place {
            position: element_sort.clone(),
            left: place.left,
            after: if list.separated() {
                After::Terminal(list.separator.clone(), app.sym.arguments.get(1).cloned())
            } else {
                After::Text
            },
            reading: element_sort.map_or(Reading::Unknown, Reading::At),
            host: host(0),
            tail: false,
        };
        let tail_place = Place {
            position: app.sym.arguments.get(1).cloned(),
            left: list.separated(),
            after: place.after.clone(),
            reading: Reading::Unknown,
            host: host(1),
            tail: true,
        };
        let [element, tail] = app.args.as_mut_slice() else {
            unreachable!("two arguments")
        };
        stack.push((tail, tail_place));
        stack.push((element, element_place));
    }
}

/// Where the `index`-th argument of `app`, whose format is `parts`, standing at `place`,
/// stands: delimited by the format's text beside it, or by what delimits `app` where it is the
/// first (the last) part, at the sort the production declares there. Where the format writes
/// only the argument, its text is `app`'s, read where `app` is.
fn argument_place(
    app: &App,
    parts: &[Piece],
    index: usize,
    place: &Place,
    tokens: &Rc<Vec<Option<String>>>,
) -> Place {
    let position = if app.sym.is_builtin() {
        None
    } else {
        app.sym.arguments.get(index).cloned()
    };
    let mut at = parts
        .iter()
        .enumerate()
        .filter(|(_, piece)| **piece == Piece::Argument(index))
        .map(|(at, _)| at);
    let (Some(at), None) = (at.next(), at.next()) else {
        // Printed twice or not at all: nothing is known of what stands beside it.
        return Place {
            position,
            left: false,
            after: After::Text,
            reading: Reading::Unknown,
            host: None,
            tail: false,
        };
    };
    let left = match at.checked_sub(1).map(|before| &parts[before]) {
        None => place.left,
        Some(Piece::Text(_)) => true,
        Some(Piece::Argument(_)) => false,
    };
    let after = match parts.get(at + 1) {
        None => place.after.clone(),
        Some(Piece::Text(text)) => After::Terminal(
            text.clone(),
            match parts.get(at + 2) {
                Some(Piece::Argument(next)) if !app.sym.is_builtin() => {
                    app.sym.arguments.get(*next).cloned()
                }
                _ => None,
            },
        ),
        Some(Piece::Argument(_)) => After::Text,
    };
    if parts.len() == 1 {
        return Place {
            position,
            left,
            after,
            reading: place.reading.clone(),
            host: place.host.clone(),
            tail: false,
        };
    }
    Place {
        reading: position.clone().map_or(Reading::Unknown, Reading::At),
        host: Some(Rc::new(Host {
            symbol: app.sym.name.clone(),
            index,
            position: place.position.clone(),
            tokens: tokens.clone(),
        })),
        position,
        left,
        after,
        tail: false,
    }
}

#[cfg(test)]
mod tests {
    use super::{Piece, Unit, pieces, writes_same};

    #[test]
    fn a_format_prints_its_text_and_arguments_without_layout() {
        assert_eq!(
            pieces("%cf%r%c(%r%1%c ,%r %2%n)"),
            [
                Piece::Text("f(".to_owned()),
                Piece::Argument(0),
                Piece::Text(",".to_owned()),
                Piece::Argument(1),
                Piece::Text(")".to_owned()),
            ]
        );
        assert_eq!(
            pieces("%i%1%d%n%2"),
            [Piece::Argument(0), Piece::Argument(1)]
        );
        assert_eq!(pieces("100%%"), [Piece::Text("100%".to_owned())]);
    }

    /// A production's text in a test's shorthand: `A` an argument that always writes text, `S`
    /// one that can write none, any other character a terminal's.
    fn units(text: &str) -> Vec<Unit> {
        text.chars()
            .map(|character| match character {
                'A' => Unit::Argument { silent: false },
                'S' => Unit::Argument { silent: true },
                other => Unit::Character(other),
            })
            .collect()
    }

    /// `f()` writes `f({args})` without its argument, and so does `{callee}()`, whose callee
    /// can be `f`; a bracket `({e})` does not, nor does `f({x})`, whose argument always writes
    /// text.
    #[test]
    fn two_productions_write_the_same_text_where_their_arguments_allow() {
        assert!(writes_same(&units("f()"), &units("f()")));
        assert!(writes_same(&units("f()"), &units("f(S)")));
        assert!(!writes_same(&units("f()"), &units("f(A)")));
        assert!(writes_same(&units("A()"), &units("f()")));
        assert!(!writes_same(&units("A()"), &units("(A)")));
        assert!(!writes_same(&units("A()"), &units("(S)")));
        assert!(writes_same(&units("tail"), &units("tail")));
        assert!(!writes_same(&units("tail"), &units("tails")));
        assert!(writes_same(&units("gS)"), &units("g)")));
    }
}
