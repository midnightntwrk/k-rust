use renamed_krs as k;

k::sorts! {
    Expr;
}

#[k::constructors(sort = Expr, result = k::KResult)]
#[k::precedence((Leaf))]
pub enum Tree {
    #[k::syntax("leaf")]
    Leaf(),
}

// `Some` resolves to the prelude's `Option::Some`, which no KRS macro
// declared: it is no term head.
k::rules! {
    for Expr;
    use Tree::*;

    wrap: Leaf() => Some(Leaf()); //~ ERROR [krs::expand::not-a-declaration] `Option<_>` is not a KRS declaration of this name
}

fn main() {}
