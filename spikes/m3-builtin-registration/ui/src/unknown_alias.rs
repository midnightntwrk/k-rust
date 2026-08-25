use dialect::int::Int;

#[dialect::builtin_application]
fn rejected(x: Int, y: Int) -> Int {
    missing_module::add(x, y)
}

fn main() {}

