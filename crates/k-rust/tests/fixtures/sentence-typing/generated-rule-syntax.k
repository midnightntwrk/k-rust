module TYPER-PROBE
  imports DOMAINS
  syntax KResult ::= Int
  syntax KItem ::= a(K) | b(Int) | c(Int) | d(Int) | e(Int) | g(Int) | h(K) | m(K)
  syntax Pair ::= pair(fst: Int, snd: Int) [symbol(pair)]
  rule [pred-int]: a(X) => b(1) requires isInt(X)
  rule [pred-kresult]: a(X) => d(1) requires isKResult(X)
  rule [pred-in-rhs]: h(X) => m(isInt(X))
  rule [let]: b(X) => c(#let Y = X #in Y +Int 1)
  rule [fun]: c(X) => d(#fun(Y => Y +Int 1)(X))
  rule [fun-cast]: d(X) => e(#fun(Y:Int => Y +Int 1)(X))
  rule [match]: e(X) => g(0) requires X :=K 0
  rule [nomatch]: e(X) => g(1) requires X :/=K 0
  rule [proj]: h(X) => g({X}:>Int)
  rule [field]: g(X) => b(fst(pair(X, X)))
  rule [ite]: m(X) => g(#if isInt(X) #then 1 #else 2 #fi)
  syntax Int ::= fz(Int) [function, total]
  rule [fz]: fz(X) => X
  rule [ml]: fz(X) => X requires #Ceil(X /Int 2) [simplification]
endmodule
