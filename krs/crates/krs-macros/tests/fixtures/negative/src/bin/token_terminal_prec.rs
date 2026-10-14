use renamed_krs as k;

#[k::token(terminal = "main", prec = 1)] //~ ERROR `prec` orders regex tokens only; a terminal already outranks every regex token
pub struct Name(pub String);

fn main() {}
