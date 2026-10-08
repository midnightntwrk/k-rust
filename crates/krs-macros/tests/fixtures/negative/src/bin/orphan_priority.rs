use renamed_krs as k;

#[k::priority(40)] //~ ERROR `#[k::priority(..)]` is retired; write `#[k::equation(priority = 40)]`
fn not_an_equation() {}

fn main() {}
