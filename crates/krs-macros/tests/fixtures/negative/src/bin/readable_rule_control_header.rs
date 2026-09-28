use renamed_krs as k;

k::rules! {
    for Stmt in k; //~ ERROR control-flow rule surface and is not implemented yet
    step: Sequence(first, second) => first;
}

fn main() {}
