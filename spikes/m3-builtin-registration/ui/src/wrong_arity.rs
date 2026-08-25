use dialect::int;

#[dialect::builtin_application]
fn rejected(x: int::Int) -> int::add {
    int::add(x)
}

fn main() {}

