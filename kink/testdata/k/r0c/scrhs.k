// Re-pin R0c-fix-1 deliverable 4 (R0c review 1 minor, decision 1): right-hand sides that apply a
// short-circuit operator over an operand that may be undefined (10 /Int 0). k-rust evaluates
// every operand, so each of go, fn, at, oe, cond and imp on 0 is an undefined step (a Trivial
// leaf naming the rule) where a short-circuiting backend gives a value. rqa's condition is a
// top-level conjunction and gd's calls a conjunctive guard (the shape of tb02bytes.k's
// byteGuard): each applies in the same cases in both readings. ctl's operands are total.
module SCRHS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | rqa(Int) [symbol(rqa)] | fn(Int) [symbol(fn)]
                | at(Int) [symbol(at)] | oe(Int) [symbol(oe)] | cond(Int) [symbol(cond)]
                | imp(Int) [symbol(imp)] | ctl(Int) [symbol(ctl)] | gd(Int) [symbol(gd)]
                | res(Bool) [symbol(res)]
  syntax Bool ::= f(Int) [function, symbol(f)] | guard(Int) [function, symbol(guard)]
endmodule
module SCRHS
  imports SCRHS-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Prog </k>
  rule f(I) => false andBool 10 /Int I >Int 0
  rule [go]: <k> go(I) => res(false andBool 10 /Int I >Int 0) </k>
  rule [rqa]: <k> rqa(I) => res(true) </k> requires false andBool 10 /Int I >Int 0
  rule [fn]: <k> fn(I) => res(f(I)) </k>
  rule [at]: <k> at(I) => res(false andThenBool 10 /Int I >Int 0) </k>
  rule [oe]: <k> oe(I) => res(true orElseBool 10 /Int I >Int 0) </k>
  rule [cond]: <k> cond(I) => res(#if true #then true #else 10 /Int I >Int 0 #fi) </k>
  rule [imp]: <k> imp(I) => res(false impliesBool 10 /Int I >Int 0) </k>
  rule [ctl]: <k> ctl(I) => res(false andBool I >Int 0) </k>
  rule guard(I) => I =/=Int 0 andBool 10 /Int I >Int 0
  rule [gd]: <k> gd(I) => res(true) </k> requires guard(I)
endmodule
