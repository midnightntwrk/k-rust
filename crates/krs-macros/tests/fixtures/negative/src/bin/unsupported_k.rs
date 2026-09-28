use krs_macros::k;

fn main() {
    let _ = k![left + right]; //~ ERROR root must be a named path
}
