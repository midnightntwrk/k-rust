#[k::rule(label = "eval-add")]
pub fn eval_add(
    lhs: k::Term<k::builtin::Int>,
    rhs: k::Term<k::builtin::Int>,
    k::cells! {
        k : k::configuration::KCell(crate ::Op::Add(lhs, rhs), tail @ ..), state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k : k::configuration::KCell(k::builtin::int::add(lhs, rhs), ..tail), ..state
    }
}
