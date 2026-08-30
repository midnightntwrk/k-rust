module OVERLOAD-CONSTRUCTORS
  syntax Digit
  syntax Small ::= Digit
  syntax Medium ::= Small
  syntax Large ::= Medium
  syntax K ::= Large

  syntax Small ::= "narrow(" Small ")" [overload(project), symbol(narrow)]
  syntax Medium ::= "wide(" Medium ")" [overload(project), symbol(wide)]
  syntax Large ::= "widest(" Large ")" [overload(project), symbol(widest)]

  syntax Large ::= "asSmall(" Small ")" [overload(view), symbol(asSmall)]
  syntax Large ::= "asMedium(" Medium ")" [overload(view), symbol(asMedium)]

  syntax Small ::= "fromSmall(" Small ")" [overload(promote), symbol(fromSmall)]
  syntax Medium ::= "fromMedium(" Small ")" [overload(promote), symbol(fromMedium)]
endmodule
