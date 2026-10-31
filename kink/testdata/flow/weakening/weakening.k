module WEAK-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Val ::= v(Int) [symbol(v)]
  syntax Prog ::= runf(Int) [symbol(runf)] | rung(Int) [symbol(rung)] | runh(Int) [symbol(runh)] | runs(Int) [symbol(runs)] | out(Int) [symbol(out)]
                | runfz(Int) [symbol(runfz)] | pair(Val, Val) [symbol(pair)] | done(Int) [symbol(done)]
  syntax Val ::= f(Int) [function, total, symbol(f)]
               | g(Int) [function, symbol(g)]
               | h(Int) [function, symbol(h)]
               | s(Int) [function, total, symbol(s)]
               | z(Int) [function, total, symbol(z)]
  syntax Int ::= w(Int) [function, total, symbol(w)]
  // Hooked BOOL.and, but a macro: its rule makes `A &&& B` mean `notBool A`, not a conjunction.
  syntax Bool ::= Bool "&&&" Bool [function, hook(BOOL.and), macro, symbol(andand)]
endmodule

module WEAK
  imports WEAK-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [runf]: <k> runf(I) => f(I) </k>
  rule [rung]: <k> rung(I) => g(I) </k>
  rule [runh]: <k> runh(I) => h(I) </k>
  rule [runs]: <k> runs(I) => s(I) </k>
  rule [out]: <k> v(I) => out(I) </k>
  // runfz(1) holds z(5), which no equation reduces in the baseline either, before f(1).
  rule [runfz]: <k> runfz(I) => pair(z(5), f(I)) </k>
  rule [pair]: <k> pair(_, v(I)) => done(I) </k>
  rule [f-zero]: f(0) => v(1)
  rule [f-pos]: f(I) => v(I) requires I >Int 0
  rule [f-neg]: f(I) => v(0 -Int I) requires I <Int 0
  rule [g-zero]: g(0) => v(7)
  rule [g-else]: g(_) => v(3) [owise]
  rule [h-one]: h(1) => v(2)
  rule [h-pos]: h(I) => v(I) requires I >Int 1
  rule [h-low]: h(_) => v(5) [priority(60)]
  rule [w-def]: w(I) => I +Int 1
  rule [z-zero]: z(0) => v(0)
  rule [w-lemma]: w(I) +Int 0 => w(I) [simplification]
  rule [and-macro]: A &&& _ => notBool A
  rule [s-big]: s(I) => v(I) requires I >Int 10
  rule [s-small]: s(I) => v(I +Int 1) requires I <=Int 10
endmodule
