use renamed_krs as k;

k::precedence! { additive } //~ ERROR a precedence chain must contain at least one `>`

fn main() {}
