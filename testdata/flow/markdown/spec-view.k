                               

                                                                               
                                                                               
                                                                              
                                                                  

    
module LIT-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "inc" Exp   [strict, symbol(inc)]
               | "dec" Exp   [strict, symbol(dec)]
               | "twice" Exp [strict, symbol(twice)]
               > left:
                 Exp "+" Exp [strict, symbol(add)]
endmodule
   

                                                                         
                                                           

    
module LIT
  imports LIT-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule [inc]: inc I:Int => I +Int 1
  rule I1:Int + I2:Int => I1 +Int I2
   

                                                                            
                                    

        
                              
   

                                                                            
                                           

    
  rule dec I:Int => I -Int 1 [label(dec)]
  rule [twice]: twice I:Int => I +Int 1 +Int 1
endmodule
   

                                                                        
