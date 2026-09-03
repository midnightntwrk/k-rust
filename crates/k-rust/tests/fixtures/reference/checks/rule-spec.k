// reference: k/result/bin/kprove --definition errorClaim-kompiled rule-spec.k
// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module RULE-SPEC
    imports ERRORCLAIM

    rule <k> doIt(foo) => doIt(0) ... </k>
endmodule
