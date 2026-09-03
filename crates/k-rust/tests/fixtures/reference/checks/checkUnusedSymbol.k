// reference: k/result/bin/kompile -w2e -w all --backend haskell checkUnusedSymbol.k
// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKUNUSEDSYMBOL-SYNTAX

endmodule

module CHECKUNUSEDSYMBOL
  imports CHECKUNUSEDSYMBOL-SYNTAX
  imports INT

  syntax Foo ::= foo(Int)

  syntax Bar ::= bar(Int) [unused]
endmodule
