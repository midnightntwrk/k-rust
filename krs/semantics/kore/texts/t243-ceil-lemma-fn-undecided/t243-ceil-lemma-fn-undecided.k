// A function d with one equation, which applies where its second argument is not 0, and a
// [simplification] sentence over element variables stating that d(A, B) has a value exactly where
// B is not 0. No equation of d speaks of d(A, 0); the sentence does.
module T243-CEIL-LEMMA-FN-UNDECIDED
  imports INT
  imports BOOL
  imports ML-SYNTAX
  syntax Int ::= d(Int, Int) [function]
  rule d(A:Int, B:Int) => A requires B =/=Int 0
  rule #Ceil(d(_A:Int, B:Int)) => {(B =/=Int 0) #Equals true} [simplification]
endmodule
