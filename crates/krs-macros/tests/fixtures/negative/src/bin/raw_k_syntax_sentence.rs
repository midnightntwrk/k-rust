use renamed_krs as k;

k::raw_k!("syntax Foo ::= \"foo\""); //~ ERROR `raw_k!` text must start with `rule`, `claim` or `context`, not `syntax`

fn main() {}
