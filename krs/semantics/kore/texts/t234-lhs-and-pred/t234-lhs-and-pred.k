// #And on a rule's left side: a term with a predicate (#Ceil, #Equals), a variable with a term, and two terms.
module T234-LHS-AND-PRED
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | go2(Int) [symbol(go2)] | "done" [symbol(done)]
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)] | e(Exp) [symbol(e)]
  rule <k> go(X) #And #Ceil(go(X)) => done ... </k>
  rule <k> go2(X) #And {X #Equals 1} => done ... </k>
  rule <k> c(X #And d(_, b())) => X ... </k>
  rule <k> e(d(X, _) #And d(_, b())) => X ... </k>
endmodule
