use renamed_krs as k;
use renamed_krs::Term;

#[k::function(total, sort = S, syntax = "first({value})")]
pub struct First<S: ?Sized>
where //~ ERROR a production struct cannot have a where clause
    S: 'static,
{
    pub value: Term<S>,
}

fn main() {}
