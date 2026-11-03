// CF-01: a skippable operand below notBool (Foldiboy's conj-bitrange-explicit shape) is reading-
// dependent unless its partial applications are defined, which the analysis reads from the
// loaded definition's ceil theory: each Int hook with a ceil equation in domains.md
// (INT-SYMBOLIC-KORE: /Int, %Int, modInt, >>Int, <<Int; INT-SYMBOLIC-KORE-AMENDMENTS: divInt,
// bitRangeInt, ^Int, ^%Int, log2Int) at arguments that make the equation's condition \top owes
// nothing beyond its arguments, so cdiv .. cpowm do not depend on the reading. log2Int(X) owes
// X >Int 0 and X /Int Y owes Y =/=Int 0, which the guard X >=Int 0 does not give where the operand
// is skipped, so clog and cdy do.
module SCCEIL-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= res(Int) [symbol(res)]
  syntax Int ::= cdiv(Int) [function, symbol(cdiv)] | cmod(Int) [function, symbol(cmod)]
               | cemod(Int) [function, symbol(cemod)] | cshr(Int) [function, symbol(cshr)]
               | cshl(Int) [function, symbol(cshl)] | cediv(Int) [function, symbol(cediv)]
               | cbr(Int) [function, symbol(cbr)] | cpow(Int) [function, symbol(cpow)]
               | cpowm(Int) [function, symbol(cpowm)] | clog(Int) [function, symbol(clog)]
               | cdy(Int, Int) [function, symbol(cdy)]
endmodule
module SCCEIL
  imports SCCEIL-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule cdiv(X) => 1 requires notBool (X >=Int 0 andThenBool X /Int 16 ==Int 0)
  rule cmod(X) => 1 requires notBool (X >=Int 0 andThenBool X %Int 16 ==Int 0)
  rule cemod(X) => 1 requires notBool (X >=Int 0 andThenBool X modInt 16 ==Int 0)
  rule cshr(X) => 1 requires notBool (X >=Int 0 andThenBool X >>Int 2 ==Int 0)
  rule cshl(X) => 1 requires notBool (X >=Int 0 andThenBool X <<Int 2 ==Int 0)
  rule cediv(X) => 1 requires notBool (X >=Int 0 andThenBool X divInt 16 ==Int 0)
  rule cbr(X) => 1 requires notBool (X >=Int 0 andThenBool bitRangeInt(X, 4, 4) ==Int 0)
  rule cpow(X) => 1 requires notBool (X >=Int 0 andThenBool X ^Int 2 ==Int 0)
  rule cpowm(X) => 1 requires notBool (X >=Int 0 andThenBool X ^%Int 2 7 ==Int 0)
  rule clog(X) => 1 requires notBool (X >=Int 0 andThenBool log2Int(X) ==Int 0)
  rule cdy(X, Y) => 1 requires notBool (X >=Int 0 andThenBool X /Int Y ==Int 0)
endmodule
