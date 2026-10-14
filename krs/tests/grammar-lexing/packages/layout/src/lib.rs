//! Layout and named lexicals (KF-004).
//!
//! Layout is what the scanner throws away. `k::layout!` declares it, and
//! declaring any layout replaces K's default whitespace and `//`/`/* */`
//! comments, so this definition declares whitespace again beside its `;`
//! line comment. Programs here therefore cannot use `//` comments.
//!
//! Layout is global: K's rule parser reads this module's rules with it too,
//! so the comment marker is one that no terminal starts with.
//!
//! `k::lexical!` names regex fragments; it adds no syntax. `Name`'s regex
//! refers to them as `{Alpha}` and `{AlphaNum}`.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
    impl KItem for Name;
}

k::lexical! {
    /// One ASCII letter.
    Alpha = r"[a-zA-Z]";
    AlphaNum = r"[a-zA-Z0-9_]";
}

k::layout! {
    r"(;[^\n\r]*)",     // `;` starts a comment to the end of the line
    r"([\ \n\r\t])",    // whitespace: declaring any layout replaces K's default
}

/// Identifiers, built from the named lexicals.
#[k::token(regex = r"{Alpha}{AlphaNum}*")]
pub struct Name(pub String);

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Call, Halt, Other))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("call {target}")]
    Call { target: Name },
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

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    call_main: Call(k::lexeme!(Name, "main"))  => Halt();
    call_foo : Call(k::lexeme!(Name, "Foo_1")) => Other();
}
