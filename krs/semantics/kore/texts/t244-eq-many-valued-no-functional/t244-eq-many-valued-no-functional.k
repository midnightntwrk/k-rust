module T244-EQ-MANY-VALUED-NO-FUNCTIONAL
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)] | s(Int) [function, symbol(s)]
  syntax Bool ::= p(Bool) [function, symbol(p)] | px(Bool) [function, symbol(px)]
  rule f(X) => X
  rule g(X) => 0 -Int X
  rule h(X) => f(X) #Or g(X)
  rule p(X) => X #Or (#Exists B:Bool. (B #And {B #Equals notBool X}))
  rule px(X) => X #Or (#Exists B:Bool. (B #And {B #Equals X}))
  rule s(X) => X #Or (#Exists B:Int. (B #And {B #Equals X +Int 1}))
endmodule
