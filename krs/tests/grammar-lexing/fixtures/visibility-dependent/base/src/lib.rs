//! A package with a pub production and a private helper production.

use k::KResult;

k::sorts! {
    Exp;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc))]
pub enum ExpSyntax {
    #[k::syntax("inc {value}")]
    Inc { value: Exp },
}

/// Private to this package: dependents cannot name it.
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Wrap))]
enum Helper {
    #[k::syntax("helper({value})")]
    Wrap { value: Exp },
}
