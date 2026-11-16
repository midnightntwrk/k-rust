// The probe of strict evaluation (KcoreSpec/Lazy.lean): `inv`'s `#if` guards a partial division
// and `t3`'s `andBool` a partial predicate. Evaluation is strict, so `inv(0)` (its then-branch
// `100 /Int 0` undefined) and `false andBool p(0)` are undefined, and `t1` and `t3` have no step;
// a short-circuiting reading would give `res(0)` and `resB(false)`. Both are lazy obligations of
// the generated package, listed by rule name. `t4`'s and `t5`'s skipped arguments, literals and
// calls of a `[total]` function, are shown defined by `definedArg`.
module LAZY-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "t1" [symbol(t1)] | "t2" [symbol(t2)] | "t3" [symbol(t3)] | "t4" [symbol(t4)]
               | "t5" [symbol(t5)]
endmodule

module LAZY
  imports LAZY-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Cmd </k>
  syntax Int ::= inv(Int) [function, symbol(inv)]
  rule [inv]: inv(N) => #if N =/=Int 0 #then 100 /Int N #else 0 #fi
  syntax Bool ::= p(Int) [function, symbol(p)]
  rule [p]: p(1) => true
  syntax Int ::= dbl(Int) [function, total, symbol(dbl)]
  rule [dbl]: dbl(N) => N +Int N
  syntax KItem ::= res(Int) [symbol(res)] | resB(Bool) [symbol(resB)]
  rule [t1]: <k> t1 => res(inv(0)) </k>
  rule [t2]: <k> t2 => res(inv(4)) </k>
  rule [t3]: <k> t3 => resB(false andBool p(0)) </k>
  rule [t4]: <k> t4 => res(#if true #then 5 #else 6 #fi) </k>
  rule [t5]: <k> t5 => res(#if false #then dbl(1) #else dbl(2) #fi) </k>
endmodule
