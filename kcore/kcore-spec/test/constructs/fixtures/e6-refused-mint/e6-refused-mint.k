// Each of the 38 sort-parametric hooked functions of MINT (domains.md) applied once, each in a rule
// of its own labelled with the hook's name, at the instance MInt{8} (MInt{16} for the result of
// roundMInt and signExtendMInt), and a literal of MInt{8} (rule mint-literal).
module E6-REFUSED-MINT
  imports MINT
  imports INT
  imports BOOL
  imports BYTES
  syntax MInt{8}
  syntax MInt{16}
  syntax KItem ::= go(Int) [symbol(go)]
  rule [mint-not]:        <k> go(1)  ~> X:MInt{8} => ~MInt X ... </k>
  rule [mint-neg]:        <k> go(2)  ~> X:MInt{8} => --MInt X ... </k>
  rule [mint-pow]:        <k> go(3)  ~> X:MInt{8} ~> Y:MInt{8} => X ^MInt Y ... </k>
  rule [mint-mul]:        <k> go(4)  ~> X:MInt{8} ~> Y:MInt{8} => X *MInt Y ... </k>
  rule [mint-sdiv]:       <k> go(5)  ~> X:MInt{8} ~> Y:MInt{8} => X /sMInt Y ... </k>
  rule [mint-srem]:       <k> go(6)  ~> X:MInt{8} ~> Y:MInt{8} => X %sMInt Y ... </k>
  rule [mint-udiv]:       <k> go(7)  ~> X:MInt{8} ~> Y:MInt{8} => X /uMInt Y ... </k>
  rule [mint-urem]:       <k> go(8)  ~> X:MInt{8} ~> Y:MInt{8} => X %uMInt Y ... </k>
  rule [mint-add]:        <k> go(9)  ~> X:MInt{8} ~> Y:MInt{8} => X +MInt Y ... </k>
  rule [mint-sub]:        <k> go(10) ~> X:MInt{8} ~> Y:MInt{8} => X -MInt Y ... </k>
  rule [mint-shl]:        <k> go(11) ~> X:MInt{8} ~> Y:MInt{8} => X <<MInt Y ... </k>
  rule [mint-ashr]:       <k> go(12) ~> X:MInt{8} ~> Y:MInt{8} => X >>aMInt Y ... </k>
  rule [mint-lshr]:       <k> go(13) ~> X:MInt{8} ~> Y:MInt{8} => X >>lMInt Y ... </k>
  rule [mint-and]:        <k> go(14) ~> X:MInt{8} ~> Y:MInt{8} => X &MInt Y ... </k>
  rule [mint-xor]:        <k> go(15) ~> X:MInt{8} ~> Y:MInt{8} => X xorMInt Y ... </k>
  rule [mint-or]:         <k> go(16) ~> X:MInt{8} ~> Y:MInt{8} => X |MInt Y ... </k>
  rule [mint-slt]:        <k> go(17) ~> X:MInt{8} ~> Y:MInt{8} => X <sMInt Y ... </k>
  rule [mint-ult]:        <k> go(18) ~> X:MInt{8} ~> Y:MInt{8} => X <uMInt Y ... </k>
  rule [mint-sle]:        <k> go(19) ~> X:MInt{8} ~> Y:MInt{8} => X <=sMInt Y ... </k>
  rule [mint-ule]:        <k> go(20) ~> X:MInt{8} ~> Y:MInt{8} => X <=uMInt Y ... </k>
  rule [mint-sgt]:        <k> go(21) ~> X:MInt{8} ~> Y:MInt{8} => X >sMInt Y ... </k>
  rule [mint-ugt]:        <k> go(22) ~> X:MInt{8} ~> Y:MInt{8} => X >uMInt Y ... </k>
  rule [mint-sge]:        <k> go(23) ~> X:MInt{8} ~> Y:MInt{8} => X >=sMInt Y ... </k>
  rule [mint-uge]:        <k> go(24) ~> X:MInt{8} ~> Y:MInt{8} => X >=uMInt Y ... </k>
  rule [mint-eq]:         <k> go(25) ~> X:MInt{8} ~> Y:MInt{8} => X ==MInt Y ... </k>
  rule [mint-ne]:         <k> go(26) ~> X:MInt{8} ~> Y:MInt{8} => X =/=MInt Y ... </k>
  rule [mint-smax]:       <k> go(27) ~> X:MInt{8} ~> Y:MInt{8} => sMaxMInt(X, Y) ... </k>
  rule [mint-smin]:       <k> go(28) ~> X:MInt{8} ~> Y:MInt{8} => sMinMInt(X, Y) ... </k>
  rule [mint-umax]:       <k> go(29) ~> X:MInt{8} ~> Y:MInt{8} => uMaxMInt(X, Y) ... </k>
  rule [mint-umin]:       <k> go(30) ~> X:MInt{8} ~> Y:MInt{8} => uMinMInt(X, Y) ... </k>
  rule [mint-round]:      <k> go(31) ~> X:MInt{8} => roundMInt(X)::MInt{16} ... </k>
  rule [mint-sext]:       <k> go(32) ~> X:MInt{8} => signExtendMInt(X)::MInt{16} ... </k>
  rule [mint-bitwidth]:   <k> go(33) ~> X:MInt{8} => bitwidthMInt(X) ... </k>
  rule [mint-svalue]:     <k> go(34) ~> X:MInt{8} => MInt2Signed(X) ... </k>
  rule [mint-uvalue]:     <k> go(35) ~> X:MInt{8} => MInt2Unsigned(X) ... </k>
  rule [mint-integer]:    <k> go(36) ~> I:Int => Int2MInt(I)::MInt{8} ... </k>
  rule [mint-MInt2bytes]: <k> go(37) ~> X:MInt{8} => MInt2Bytes(X) ... </k>
  rule [mint-bytes2MInt]: <k> go(38) ~> B:Bytes => Bytes2MInt(B)::MInt{8} ... </k>
  rule [mint-literal]:    <k> go(39) => 3p8 ... </k>
endmodule
