use dialect::int::Int;

fn ordinary_function(x: Int, _y: Int) -> Int {
    x
}

#[dialect::builtin_application]
fn rejected(x: Int, y: Int) -> Int {
    ordinary_function(x, y)
}

fn main() {}

