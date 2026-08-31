#[rule]
#[language_host::requires(language_host::builtin::int::gt(value, 0))]
pub fn guarded_term(Guarded { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    Halt
}
