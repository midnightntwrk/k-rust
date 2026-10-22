use krs_macros::term;

fn main() {
    let _ = term![*left]; //~ ERROR root must be a named path
}
