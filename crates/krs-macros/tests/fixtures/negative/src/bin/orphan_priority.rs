use renamed_krs as k;

#[k::priority(40)] //~ ERROR is an equation helper; place it immediately before `#[k::equation]`
fn not_an_equation() {}

fn main() {}
