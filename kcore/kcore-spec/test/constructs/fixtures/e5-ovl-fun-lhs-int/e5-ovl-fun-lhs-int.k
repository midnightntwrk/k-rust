module E5-OVL-FUN-LHS-INT
  imports INT
  syntax Exp ::= Int | dbl(Exp) [symbol(dblExp), overload(dbl)]
  syntax Int ::= dbl(Int) [function, total, symbol(dblInt), overload(dbl)]
  syntax Pgm ::= run(Exp) [symbol(run)] | done(Int) [symbol(done)]
  configuration <k> $PGM:Pgm </k>
  rule dbl(I:Int) => 2 *Int I
  rule <k> run(dbl(_:Exp)) => done(0) </k>
  rule <k> run(_:Exp) => done(1) </k> [owise]
endmodule
