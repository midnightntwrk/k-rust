#[renamed_krs::cell]
struct Jobs {
    #[renamed_krs::cell(multiplicity = "*", cell_type = "Bag", nested)] //~ ERROR cell bags are unsupported by K's LLVM and Haskell backends
    job: Job,
}

#[renamed_krs::cell]
struct Job {
    #[renamed_krs::cell]
    id: renamed_krs::builtin::Int,
}

fn main() {}
