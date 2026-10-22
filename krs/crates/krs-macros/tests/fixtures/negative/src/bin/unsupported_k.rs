use krs_macros::k;

fn main() {
    let _ = k![*left]; //~ ERROR root must be a named path
}
