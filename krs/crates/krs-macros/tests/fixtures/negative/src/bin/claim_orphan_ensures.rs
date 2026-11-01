#[renamed_krs::ensures(check(0))] //~ ERROR `#[k::ensures]` is a helper of a sentence, and this item has no sentence marker
fn orphan() {}

fn main() {}
