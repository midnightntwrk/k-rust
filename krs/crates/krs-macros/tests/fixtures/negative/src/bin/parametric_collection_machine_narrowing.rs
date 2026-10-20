use renamed_krs as k;

k::rules! {
    for Machine;

    bad: {
        k: [value, ..],
    } => {
        k: [..],
    } where value: k::builtin::Set<Int>; //~ ERROR write `k::builtin::Set` without generic arguments
}

fn main() {}
