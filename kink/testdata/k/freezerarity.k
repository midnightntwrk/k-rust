// Freezer names (PJ-35, U35b review): `foo`'s strict first position gives `#freezerfoo0_` one
// argument; freezeraritym.k drops the strictness and writes `context foo(HOLE, 1)`, whose freezer
// has the same name and no argument. The name is declared on both sides with another arity, so
// an end holding it is not compared across the two definitions.
module FREEZERARITY-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | foo(Exp, Exp)        [strict(1), symbol(foo)]
               | Exp "-" Exp          [strict, symbol(minus)]
endmodule

module FREEZERARITY
  imports FREEZERARITY-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  rule foo(I1:Int, I2:Int) => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
endmodule
