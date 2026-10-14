#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    stmt (Assign, IfThenElse, IfThen, While, Block, EmptyBlock)
    > right seq_stmt (Sequence)
)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("{name} = {value};")] #[k::strict(value)]
    Assign { name: Id, value: Expr },

    /// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.
    #[k::syntax("if ({condition}) {then_branch} else {else_branch}", avoid)]
    #[k::strict(condition)]
    IfThenElse { condition: Expr, then_branch: Stmt, else_branch: Stmt },

    #[k::syntax("if ({condition}) {body}")]
    IfThen { condition: Expr, body: Stmt },

    /// Deliberately not strict: the `[while]` rule unfolds the loop instead.
    #[k::syntax("while ({condition}) {body}")]
    While { condition: Expr, body: Stmt },

    #[k::syntax("{{{body}}}")] #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },

    #[k::syntax("{{}}")]
    EmptyBlock(),

    #[k::syntax("{first} {second}")] #[k::format("{first}%n{second}")]
    Sequence { first: Stmt, second: Stmt },
}

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    /// K's computation cell: the continuation, head-first.
    #[k::cell(color = "green")]
    pub k: KSequence,
    #[k::cell(color = "yellow")]
    pub env: Map<Id, Value>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, env: Map<Id, Value>) -> Self {
        Self { k: k::k![pgm], env }
    }
}
