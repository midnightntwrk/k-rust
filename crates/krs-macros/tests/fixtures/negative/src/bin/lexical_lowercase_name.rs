use renamed_krs as k;

k::lexical! {
    alpha = r"[a-z]"; //~ ERROR a lexical name matches `[A-Z][A-Za-z0-9]*`
}

fn main() {}
