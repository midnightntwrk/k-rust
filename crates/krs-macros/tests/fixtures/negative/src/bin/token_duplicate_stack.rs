use renamed_krs as k;

#[k::token(regex = r"[a-z]+")]
#[k::token(terminal = "main")]
#[k::token(terminal = "main")] //~ ERROR repeats an earlier one on the same item
pub struct Name(pub String);

fn main() {}
