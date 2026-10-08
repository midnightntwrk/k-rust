use renamed_krs as k;

fn main() {
    let _ = k::is!(k::builtin::Int); //~ ERROR `k::is!` expects `Sort, term`
    let _ = k::project!(k::builtin::Int, 1, 2); //~ ERROR `k::project!` expects `Sort, term`
}
