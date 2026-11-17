// A definition importing INT, BOOL and MAP-SYMBOLIC. Its kompiled text holds the library's
// [simplification] sentences over set variables, among them those of domains.md
// 1393 (#Ceil(@I1 %Int @I2)), 1177 ({notBool @B #Equals true}) and
// 449 ({false #Equals @Key in_keys(.Map)}).
module T91-SET-VARIABLE-LEMMAS
  imports INT
  imports BOOL
  imports MAP-SYMBOLIC

  syntax KItem ::= go(Int)
  rule go(I) => I %Int 2
endmodule
