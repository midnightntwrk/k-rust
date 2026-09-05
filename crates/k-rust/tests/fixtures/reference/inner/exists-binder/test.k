module TEST
  imports INT
  syntax Exp ::= foo(Int)
  rule foo(_X) => #Exists Y . { ?_I #Equals Y }
endmodule
