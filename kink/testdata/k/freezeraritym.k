// The mutant of freezerarity.k (PJ-35, U35b review): `foo` is not strict, and
// `context foo(HOLE, 1)` heats its first argument with a freezer of no argument, under the name
// `#freezerfoo0_` that freezerarity.k gives its strict first position's freezer of one argument.
module FREEZERARITYM-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | foo(Exp, Exp)        [symbol(foo)]
               | Exp "-" Exp          [strict, symbol(minus)]
endmodule

module FREEZERARITYM
  imports FREEZERARITYM-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  context foo(HOLE, 1)
  rule foo(I1:Int, I2:Int) => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
endmodule
