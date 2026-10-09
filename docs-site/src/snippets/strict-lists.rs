k::sorts! {
    Exp;
    Val: Exp + KResult;
    impl Val for Int;
    impl Exps for Vals;
    impl KResult for Vals;
}

/// Call arguments, evaluated left to right.
#[k::syntax_list(separator = ",", result = KResult)]
pub enum Exps {
    #[k::seqstrict]
    Cons {
        head: Exp,
        tail: Exps,
    },
    Nil(),
}

/// Evaluated call arguments.
#[k::syntax_list(separator = ",")]
pub enum Vals {
    Cons { head: Val, tail: Vals },
    Nil(),
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Tick, Call))]
#[rustfmt::skip]
pub enum Syntax {
    #[k::syntax("tick")] Tick(),
    #[k::syntax("{callee}({args})")] #[k::strict(args)]
    Call { callee: Id, args: Exps },
}
