use krs_macros::term;

fn main() {
    let _ = term![left + right]; //~ ERROR root must be a named path
}
