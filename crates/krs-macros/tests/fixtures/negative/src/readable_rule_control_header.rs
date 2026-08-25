use renamed_krs as k;

k::rules! {
    for Stmt in k;
    step: Sequence(first, second) => first;
}

fn main() {}
