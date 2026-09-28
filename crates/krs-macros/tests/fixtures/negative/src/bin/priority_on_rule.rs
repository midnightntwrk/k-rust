use renamed_krs as k;

#[k::priority(40)] //~ ERROR is an equation helper; place it immediately before `#[k::equation]`
#[k::rule]
fn transition() {}

fn main() {}
