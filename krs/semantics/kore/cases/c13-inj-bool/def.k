// A function of sort Val whose result, an Int, is placed at sort Exp (composed injections); an
// undefined function result under an injection; Bool literals in left sides; an injected Bool
// against a pattern of sort Bool and an injected Int against it; a selected #if branch.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Val ::= Int | Bool
  syntax Exp ::= Val | go(Int) | sel(Bool) | out(Exp) | flag(Bool)
  syntax Val ::= w(Int) [function]
  syntax Int ::= d(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Exp </k>
  rule w(I) => I
  rule d(I) => (10 /Int I) +Int (10 %Int I)
  rule <k> go(I) => out(w(I)) </k>
  rule <k> go(I) => out(d(I)) </k>
  rule <k> go(I) => sel(I >Int 0) </k>
  rule <k> go(I) => sel(I ==Int 0) </k>
  rule <k> sel(true) => #if true #then true #else false #fi </k>
  rule <k> sel(false) => false </k>
  rule <k> out(B:Bool) => flag(B) </k>
endmodule
