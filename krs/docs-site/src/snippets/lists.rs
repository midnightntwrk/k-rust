/// A comma-separated list of integers: `1, 2, 3`.
#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

/// A nonempty `|`-separated list of integers.
#[k::syntax_list(separator = "|", non_empty)]
pub enum Alts {
    Cons { head: Int, tail: Alts },
    Nil(),
}

#[k::function(partial, sort = Int, syntax = "sum({items})")]
pub struct Sum {
    pub items: Term<Ints>,
}

#[k::equation]
fn sum_one(k::term![Sum(Ints::Cons(i, Ints::Nil()))]: Term<Int>) -> Term<Int> {
    i
}

#[k::equation]
fn sum_more(k::term![Sum(Ints::Cons(i1, Ints::Cons(i2, is)))]: Term<Int>) -> Term<Int> {
    Sum(Ints::Cons(int::add(i1, i2), is))
}
