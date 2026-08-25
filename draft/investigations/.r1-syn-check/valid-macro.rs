#[k::requires(x != 0)]
fn rule(x: Term) -> Term {
    match x {
        k![<k> $PGM => result ... </k>] => term![result],
        _ => x,
    }
}
