// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"
// https://github.com/runtimeverification/k/issues/2587

module A4-SPEC
  imports TEST
  imports ML-SYNTAX

  claim <k> c => 2 #And {3 #Equals n} </k>
  rule {n #Equals 3} => #Top [simplification, comm]
endmodule
