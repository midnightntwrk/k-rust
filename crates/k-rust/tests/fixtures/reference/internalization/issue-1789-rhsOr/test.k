module TEST
  imports INT
  syntax Int ::= split(Int) [function]
  rule split(V) => ({true #Equals V >=Int 0} #And V) #Or ({false #Equals V >=Int 0} #And (V +Int 1)) [label(xyzzy)]
endmodule
