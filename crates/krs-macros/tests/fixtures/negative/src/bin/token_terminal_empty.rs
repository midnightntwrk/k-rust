use renamed_krs as k;

#[k::token(terminal = "")] //~ ERROR the token terminal must not be empty
pub struct Name(pub String);

fn main() {}
