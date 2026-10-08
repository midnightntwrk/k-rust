use renamed_krs as k;

#[k::token(prec = 1)] //~ ERROR a token attribute takes exactly one of `regex = r".."` or `terminal = ".."`
pub struct Name(pub String);

fn main() {}
