use renamed_krs as k;

#[k::token(regex = r"[a-z]+")]
pub struct Name(pub String);

fn main() {
    let _ = k::lexeme!(Name); //~ ERROR `k::lexeme!` takes exactly a token sort path and a string literal
    let _ = k::lexeme!(Name, ""); //~ ERROR `k::lexeme!` text must not be empty
}
