use renamed_krs as k;

#[k::token(regex = r"[a-z]+", terminal = "main")] //~ ERROR stack one `#[k::token]` attribute per production
pub struct Name(pub String);

fn main() {}
