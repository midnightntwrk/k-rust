use dialect::int;

#[dialect::builtin_application]
fn rejected(x: int::Int, text: String) -> int::add {
    int::add(x, text)
}

fn main() {}

