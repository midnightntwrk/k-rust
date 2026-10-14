k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Expose the right-associated statement pair as K sequencing.
    step    : Sequence(s1, s2)         => k::k![s1, s2];

    /// Select the true branch of an evaluated conditional.
    if_true : IfThenElse(true, s1, _)  => s1;
    /// Select the false branch of an evaluated conditional.
    if_false: IfThenElse(false, _, s2) => s2;

    /// Normalize the no-else form with an explicit empty branch.
    if_else : IfThen(c, s)             => IfThenElse(c, s, EmptyBlock());

    /// Unfold one loop test without making the constructor strict.
    r#while : While(c, s)              => IfThen(c, Block(Sequence(s, While(c, s))));

    /// Expose a nonempty block body followed by an empty block.
    block   : Block(s)                 => k::k![s, EmptyBlock()];

    /// Remove an empty block from the computation cell.
    done    : EmptyBlock()             => ();
}
