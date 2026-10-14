// Functional reconstruction of the independent IMP static-form oracle.
// The original blob is unavailable; retained complete-IMP policies freeze its semantics.
requires "imp-verification.k"

module KRS-IMP-STATIC-SYNTAX
  imports IMP-VERIFICATION-SYNTAX
  imports IMP-SYNTAX

  syntax Int ::= "#" "addOne" "(" Int ")"
    [function, total, symbol(addOne)]
  syntax Int ::= "#" "nonnegativeIdentity" "(" Int ")"
    [function, symbol(nonnegativeIdentity)]
  syntax Int ::= "#" "priorityChoice" "(" Int ")"
    [function, total, symbol(priorityChoice)]

  syntax Expr ::= "zeroAlias"
    [alias, symbol(zeroAlias)]
  syntax Expr ::= "double" "(" Expr ")"
    [seqstrict(operandEval; 1), symbol(double)]
endmodule

module KRS-IMP-STATIC
  imports KRS-IMP-STATIC-SYNTAX
  imports IMP-VERIFICATION

  rule [add-one]:
    # addOne ( I:Int ) => I +Int 1

  rule [nonnegative-identity]:
    # nonnegativeIdentity ( I:Int ) => I
    requires 0 <=Int I

  rule [priority-choice-zero]:
    # priorityChoice ( 0 ) => 111
    [priority(40)]

  rule [priority-choice-fallback]:
    # priorityChoice ( _ ) => 222
    [priority(80)]

  rule [zero-alias]:
    zeroAlias => 0

  context alias [operandEval]:
    <k> HERE ... </k>

  rule [double]:
    double ( I:Int ) => I +Int I
endmodule
