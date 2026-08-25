// Functional reconstruction of the independent M3D static-form oracle.
// The original blob is unavailable; retained M4 policies freeze its semantics.
requires "imp-verification.k"

module KRS-M3D-STATIC-SYNTAX
  imports IMP-VERIFICATION-SYNTAX
  imports IMP-SYNTAX

  syntax Int ::= "#" "m3dTotal" "(" Int ")"
    [function, total, symbol(m3dTotal)]
  syntax Int ::= "#" "m3dPositive" "(" Int ")"
    [function, symbol(m3dPositive)]
  syntax Int ::= "#" "m3dPriority" "(" Int ")"
    [function, total, symbol(m3dPriority)]

  syntax Expr ::= "m3dZero"
    [alias, symbol(m3dZero)]
  syntax Expr ::= "m3dTwice" "(" Expr ")"
    [seqstrict(m3dEval; 1), symbol(m3dTwice)]
endmodule

module KRS-M3D-STATIC
  imports KRS-M3D-STATIC-SYNTAX
  imports IMP-VERIFICATION

  rule [m3d-total]:
    # m3dTotal ( I:Int ) => I +Int 1

  rule [m3d-positive]:
    # m3dPositive ( I:Int ) => I
    requires 0 <=Int I

  rule [m3d-priority-zero]:
    # m3dPriority ( 0 ) => 111
    [priority(40)]

  rule [m3d-priority-fallback]:
    # m3dPriority ( _ ) => 222
    [priority(80)]

  rule [m3d-zero-alias]:
    m3dZero => 0

  context alias [m3dEval]:
    <k> HERE ... </k>

  rule [m3d-twice]:
    m3dTwice ( I:Int ) => I +Int I
endmodule
