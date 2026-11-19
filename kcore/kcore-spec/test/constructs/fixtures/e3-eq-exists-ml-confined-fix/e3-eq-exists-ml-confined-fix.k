// An equation's right side whose binder Z (of Int, which the text leaves unconfined) is fixed by
// terms over a binder B of Bool (confined): f(X) => #Exists B:Bool. #Exists Z:Int.
// (Z #And g(B) #And h(B) #And {B #Equals X}), g and h total.
module E3-EQ-EXISTS-ML-CONFINED-FIX
  imports INT
  imports BOOL
  syntax Int ::= f(Bool) [function, symbol(f)]
               | g(Bool) [function, total, symbol(g)]
               | h(Bool) [function, total, symbol(h)]
  rule g(B) => 1 requires B
  rule g(B) => 1 requires notBool B
  rule h(_) => 1
  rule f(X) => #Exists B:Bool. #Exists Z:Int. (Z #And g(B) #And h(B) #And {B #Equals X})
endmodule
