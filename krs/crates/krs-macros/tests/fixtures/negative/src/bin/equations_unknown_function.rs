use renamed_krs as k;

k::equations! {
    for NoSuchFunction; //~ ERROR cannot find type `NoSuchFunction`
    zero: 0 => 1;
}

fn main() {}
