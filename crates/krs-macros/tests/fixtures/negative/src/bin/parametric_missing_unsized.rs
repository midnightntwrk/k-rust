use renamed_krs as k;
use renamed_krs::Term;

#[k::function(total, sort = S, syntax = "first({value})")]
pub struct First<S> { //~ ERROR sort markers like `dyn ExprSort` are unsized
    pub value: Term<S>,
}

fn main() {}
