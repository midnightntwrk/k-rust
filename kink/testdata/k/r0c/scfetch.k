// The shape by which SM83's decode excluded the definition, at a state that still depends on the
// short-circuit reading: the rules fetch and fetch-halt-bug apply decode, a total function with
// an owise equation, and decode's condition skips a bitRangeInt operand below andThenBool. Here
// that andThenBool stands under notBool, where the readings can differ as true versus \bottom,
// and the operand reads the opcode at the offset of a cell, so bitRangeInt(Op, Off, 2) owes
// Off >=Int 0 under the ceil theory and no other operand evaluates it. The cause chain of each
// fetch rule names decode, the equation (decode-unknown's owise guard once decode-inc is
// dropped), andThenBool and the bitRangeInt operand.
module SCFETCH-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax MicroOp ::= "#" "fetch" [symbol(microFetch)]
  syntax Instr ::= decode(Int, Int) [function, total, symbol(decode)]
                 | inc(Int) [symbol(inc)] | unknown(Int) [symbol(unknown)]
endmodule
module SCFETCH
  imports SCFETCH-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  configuration <k> $PGM:MicroOp </k> <memory> .Map </memory> <pc> 0 </pc> <offset> 0 </offset>
                <haltBug> false </haltBug>
  rule [fetch]:
    <k> # fetch => decode(Opcode:Int, Off:Int) ... </k>
    <memory> Pc:Int |-> Opcode:Int ... </memory>
    <pc> Pc:Int => Pc:Int +Int 1 </pc>
    <offset> Off:Int </offset>
    <haltBug> Bug:Bool </haltBug>
    requires notBool Bug:Bool
  rule [fetch-halt-bug]:
    <k> # fetch => decode(Opcode:Int, Off:Int) ... </k>
    <memory> Pc:Int |-> Opcode:Int ... </memory>
    <pc> Pc:Int </pc>
    <offset> Off:Int </offset>
    <haltBug> Bug:Bool => false </haltBug>
    requires Bug:Bool
  rule [decode-inc]: decode(Op, Off) => inc(bitRangeInt(Op, 3, 3))
    requires (Op >=Int 0 andThenBool Op <Int 256)
             andThenBool notBool (Op >=Int 128 andThenBool bitRangeInt(Op, Off, 2) ==Int 0)
  rule [decode-unknown]: decode(Op, _) => unknown(Op) [owise]
endmodule
