use renamed_krs as k;

#[k::alias] //~ ERROR on a production is a constructor helper; place `#[k::constructor(...)]` before it
pub struct MissingConstructor;

fn main() {}
