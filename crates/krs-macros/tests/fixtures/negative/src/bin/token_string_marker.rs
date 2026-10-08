use renamed_krs as k;

use k::builtin::string::String;

#[k::token(regex = r"[a-z]+")]
pub struct Name(pub String); //~ ERROR this field resolves to the K String marker

fn main() {}
