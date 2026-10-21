// Flow fixture (F-02): one register, written by `put(E)` and read by `get`.
// For F-04/F-05's correlated mutation of `put` and `get` together; the
// register is a single non-collection cell.
module REGISTER-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "get" [symbol(get)]
               | Exp "+" Exp [left, strict, symbol(plus)]
  syntax Stmt ::= "put" "(" Exp ")" [strict, symbol(put)]
                | Stmt ";" Stmt [right, symbol(seq)]
endmodule

module REGISTER
  imports REGISTER-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <reg> 0 </reg>

  syntax KResult ::= Int
  rule [seq]: S1:Stmt ; S2:Stmt => S1 ~> S2
  rule [put]: <k> put(I:Int) => .K ... </k> <reg> _ => I </reg>
  rule [get]: <k> get => I ... </k> <reg> I </reg>
  rule I1:Int + I2:Int => I1 +Int I2
endmodule
