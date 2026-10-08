//! User token sorts (KF-003).
//!
//! `Name` is a closed token sort: its values are the identifiers its regex
//! matches and the terminal `main`, so `main` is a token of `Name` and never
//! a keyword. K's scanner takes the longest match and a terminal outranks a
//! regex of equal length, so `call while` is a parse error: `while` is a
//! terminal of `Loop`, not a `Name`. The alias `DollarName` adds a third
//! token production to `Name`.
//!
//! The scanner is global: K's rule parser lexes this module's rules with
//! these tokens too, so `Name`'s regex differs from K's own `#LowerId`
//! (`[a-z][a-zA-Z0-9]*`, `prec(2)`), which then still lexes the `k` of `<k>`.
//!
//! `k::lexeme!(Name, "main")` is the token term `#token("main","Name")`.
//! The `cells!` rule `call_main` and the readable rule `call_foo` match two
//! different lexemes, which never overlap; `call bar` matches neither rule.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
    impl KItem for Name;
}

/// Identifiers. `main` is also a token of this sort, so `main` never becomes a keyword.
#[k::token(regex = r"[a-z][a-z0-9_]*")]
#[k::token(terminal = "main")]
pub struct Name(pub String);

/// `$`-prefixed names are names too.
#[k::token(regex = r"\$[a-z][a-z0-9_]*")]
pub type DollarName = Name;

/// Double-quoted text: a regex that contains a quote.
#[k::token(regex = r#"\"[a-z]*\""#)]
pub struct Quoted(pub String);

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Call, Say, Loop, Halt, Other))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("call {target}")]
    Call { target: Name },
    #[k::syntax("say {text}")]
    Say { text: Quoted },
    #[k::syntax("while")]
    Loop(),
    #[k::syntax("halt")]
    Halt(),
    #[k::syntax("other")]
    Other(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::rule(label = "call-main")]
pub fn call_main(
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Call(k::lexeme!(Name, "main")), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(StmtSyntax::Halt(), ..tail), ..state }
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    call_foo: Call(k::lexeme!(Name, "foo"))     => Other();
    say_hi  : Say(k::lexeme!(Quoted, "\"hi\"")) => Halt();
}
