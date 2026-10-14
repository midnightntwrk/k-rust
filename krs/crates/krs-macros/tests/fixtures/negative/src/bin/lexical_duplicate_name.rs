use renamed_krs as k;

k::lexical! {
    Alpha = r"[a-z]";
    Alpha = r"[A-Z]"; //~ ERROR a lexical name is declared once in a `k::lexical!` block
}

fn main() {}
