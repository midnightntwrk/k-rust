use renamed_krs as k;

k::layout! {
    r"([\ \n\t]", //~ ERROR unclosed parenthesis
}

fn main() {}
