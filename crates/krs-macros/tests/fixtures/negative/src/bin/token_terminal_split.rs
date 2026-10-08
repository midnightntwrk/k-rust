use renamed_krs as k;

#[k::token(terminal = "a+")] //~ ERROR a token terminal must be exactly one K terminal
pub struct Name(pub String);

fn main() {}
