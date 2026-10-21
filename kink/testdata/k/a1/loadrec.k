// Re-pin adoption A-1 (ADOPTION.md section 2.2, decision D-6): a contradicted claim the load of
// the definition observes. The two `anywhere` equations of `g` overlap, and k-rust's load-time
// critical-pair check simplifies the first one's condition through `td(0)`, which is undefined
// although `td` is declared total (k-rust tests/contradicted_claims.rs, `LOAD`). The record is a
// fact about the definition, with `observedIn: load`, on every run's list and on no leaf.
module LOADREC-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
  syntax Foo ::= g(Int) [symbol(g)]
               | "fa" [symbol(fa)]
               | "fb" [symbol(fb)]
endmodule
module LOADREC
  imports LOADREC-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int I
  rule [ga]: g(_X) => fa requires td(0) ==Int 1 [anywhere]
  rule [gb]: g(_X) => fb [anywhere]
  rule [go]: <k> go(I) => val(I +Int 1) </k>
endmodule
