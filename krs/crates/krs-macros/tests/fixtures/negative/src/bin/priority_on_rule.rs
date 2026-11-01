use renamed_krs as k;

#[k::priority(40)] //~ ERROR `#[k::priority(..)]` is retired; write `#[k::rule(priority = 40)]`
#[k::rule]
fn transition() {}

fn main() {}
