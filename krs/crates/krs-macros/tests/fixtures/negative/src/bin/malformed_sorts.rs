use renamed_krs as k;

k::sorts! {
    impl Value for Int,,; //~ ERROR expected identifier
}

fn main() {}
