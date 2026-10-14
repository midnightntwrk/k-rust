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
