// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"
// https://github.com/runtimeverification/k/issues/2587

module A5-SPEC
  imports TEST
  imports ML-SYNTAX

  claim <k> c => 2 #And n +Int n </k>
  rule n +Int n => #Top [simplification]
endmodule
