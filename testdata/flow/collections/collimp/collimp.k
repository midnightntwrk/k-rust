// CS-15: an IMP-shaped definition (a <state> Map, strict addition, a guarded declaration).
module COLLIMP-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax AExp ::= Int | Id
                | AExp "+" AExp [left, strict]
  syntax Stmt ::= "var" Id ";"
                | Id "=" AExp ";" [strict(2)]
                > Stmt Stmt [left]
endmodule

module COLLIMP
  imports COLLIMP-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports SET
  syntax KResult ::= Int
  configuration <k> $PGM:Stmt </k> <state> .Map </state>

  rule [lookup]: <k> X:Id => I ... </k> <state> ... X |-> I ... </state>
  rule [plus]: I1 + I2 => I1 +Int I2
  rule [decl]: <k> var X ; => .K ... </k> <state> Rho (.Map => X |-> 0) </state>
    requires notBool (X in keys(Rho))
  rule [assign]: <k> X = I:Int ; => .K ... </k> <state> ... X |-> (_ => I) ... </state>
  rule [seq]: S1:Stmt S2:Stmt => S1 ~> S2
endmodule
