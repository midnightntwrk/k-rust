use renamed_krs as k;

k::lexical! {
    Alpha = ""; //~ ERROR the regex must not be empty
}

fn main() {}
