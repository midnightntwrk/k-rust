use renamed_krs as k;

#[k::function(total, internal)]
pub fn Pick<S: ?Sized>(value: k::Term<S>) -> k::Term<S> { //~ ERROR is not generic
    value
}

fn main() {}
