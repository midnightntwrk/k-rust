fn rule(x: Term) -> Term {
    match x {
        value: Value => value,
        _ => x,
    }
}
