k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    /// Replace an identifier at the head of `k` with its mapped value.
    var: {
        k: [name, ..],
        env: { name -> value, .. },
    } => {
        k: [value, ..],
    }
    where name: Id;

    /// Consume a value assignment and update the environment map.
    assign: {
        k: [Assign(name, value), ..],
        env: e,
    } => {
        k: [..],
        env: map::update(e, name, value),
    }
    where value: Value;
}
