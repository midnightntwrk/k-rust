// Known gap: an i128 compared with an immediate (checked i128 add/sub/mul,
// i128 abs, min/max and negation with overflow checks at opt-level 0, signum).
use std::hint::black_box;

#[inline(never)]
fn checked(a: i128, b: i128) -> Option<i128> {
    a.checked_sub(b)
}

fn main() {
    println!("{:?} {:?}", checked(black_box(-3), black_box(4)), checked(black_box(i128::MIN), black_box(1)));
}
