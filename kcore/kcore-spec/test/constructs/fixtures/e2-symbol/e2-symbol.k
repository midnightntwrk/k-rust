module E2-SYMBOL
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | "(" Exp ")"                         [bracket]
               | k1(Exp)                             [klabel(k1), symbol]
  syntax Int ::= fn(Int)                             [function, symbol(fn)]
               | fnt(Int)                            [function, total, symbol(fnt)]
               | fnf(Int)                            [function, functional, symbol(fnf)]
               | fm(Int)                             [function, memo, symbol(fm)]
               | fi(Int)                             [function, impure, symbol(fi)]
               | fd(Int)                             [function, deprecated, symbol(fd)]
               | fne(Int)                            [function, no-evaluators, symbol(fne)]
               | fs(Int)                             [function, smtlib(fsmt), symbol(fs)]
               | fh(Int)                             [function, smt-hook(+), symbol(fh)]
               | fg(Int)                             [function, total, freshGenerator, symbol(fg)]
               | ff(Int)                             [function, format(%1%2%3%4), symbol(ff)]
               | fc(Int)                             [function, color(red), symbol(fc)]
               | fl(Int)                             [function, label(flabel), symbol(fl)]
               | fp(Int)                             [function, priority(30), symbol(fp)]
               | fhk(Int, Int)                       [function, hook(INT.add), symbol(fhk)]
  syntax Exp ::= ctor(Int)                           [constructor, symbol(ctor)]
               | inj1(Int)                           [injective, symbol(inj1)]
  rule fn(X) => X
  rule fnt(X) => X
  rule fnf(X) => X
  rule fm(X) => X
  rule fi(X) => X
  rule fd(X) => X
  rule fs(X) => X
  rule fh(X) => X
  rule fg(X) => X
  rule ff(X) => X
  rule fc(X) => X
  rule fl(X) => X
  rule fp(X) => X
endmodule
