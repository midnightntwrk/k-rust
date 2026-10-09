use renamed_krs as k;

fn main() {
    let _ = k::matches!(e, Pair(x, _) if x); //~ ERROR K's :=K has no guard; conjoin a separate condition with bool::and
    let _ = k::matches!(e); //~ ERROR `k::matches!` expects `subject, pattern`
}
