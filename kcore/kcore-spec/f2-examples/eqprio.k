module E2-EQUATION
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)] | gc(Int) [function, symbol(gc)] | gs(Int) [function, symbol(gs)]
               | h(Int) [function, symbol(h)] | p(Int, Int) [function, symbol(p)]
               | sl(Int) [function, smtlib(sl), symbol(sl)]
  rule [eq-label]: f(0) => 0
  rule f(1) => 1 [priority(10)]
  rule f(2) => 2 [priority(50)]
  rule f(3) => 3 [priority(60)]
  rule f(_) => 9 [owise]
  rule gc(X) => X [concrete]
  rule gs(X) => X [symbolic]
  rule h(X) => X [preserves-definedness]
  rule h(X) => X +Int 1 [non-executable, priority(60)]
  rule sl(X) => X
endmodule
