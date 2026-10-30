module PRIO-SYNTAX
  imports INT-SYNTAX
  syntax Reg ::= "ra" | "rb" | "rc" | "rd"
  syntax Instr ::= mv(Reg, Reg) | "stop" | "bad"
  syntax Pgm ::= Int | decode(Int) | expect(Int)
endmodule

module PRIO
  imports PRIO-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>

  // A table whose last row has a later priority, as KRS writes a default row: it gives the value
  // only where no earlier row applies.
  syntax Int ::= table(Int) [function, total]
  rule table(0) => 10
  rule table(1) => 11
  rule table(_) => 12 [priority(200)]

  // Two rows of distinct priorities over one argument.
  syntax Int ::= ranked(Int) [function, total]
  rule ranked(0) => 111 [priority(40)]
  rule ranked(_) => 222 [priority(80)]

  // Rows of one priority told apart by bit patterns and a literal, then a default row.
  syntax Int ::= field(Int) [function]
  rule field(X) => 1 requires X >=Int 0 andBool X <Int 256 andBool bitRangeInt(X, 6, 2) ==Int 1
  rule field(226) => 3
  rule field(X) => 2 requires X >=Int 0 andBool X <Int 256 andBool bitRangeInt(X, 6, 2) ==Int 3
    andBool bitRangeInt(X, 0, 3) ==Int 1
  rule field(_) => 0 [priority(200)]

  // A decoder, as a CPU's: a family of opcodes by a bit pattern whose operands are fields read
  // through a table of registers that has no default, a literal opcode inside the family with
  // another result, and a default row.
  syntax Reg ::= reg(Int) [function, total]
  rule reg(0) => ra
  rule reg(1) => rb
  rule reg(2) => rc
  rule reg(3) => rd

  syntax Instr ::= dec(Int) [function, total]
  rule dec(X) => mv(reg(bitRangeInt(X, 2, 2)), reg(bitRangeInt(X, 0, 2)))
    requires X >=Int 0 andBool X <Int 64 andBool bitRangeInt(X, 4, 2) ==Int 1 andBool X =/=Int 21
  rule dec(21) => stop
  rule dec(_) => bad [priority(200)]

  // The registers written independently (another order, a default row), for the claims of
  // `demos/claims/specs/prio-spec.k` to compare with the decoder's.
  syntax Reg ::= expected(Int) [function, total]
  rule expected(1) => rb
  rule expected(3) => rd
  rule expected(0) => ra
  rule expected(2) => rc
  rule expected(_) => ra [priority(200)]

  rule <k> X:Int => table(X) +Int ranked(X) +Int field(X) </k> requires X <Int 1000
  rule <k> decode(X) => dec(X) </k>
  rule <k> expect(X) => mv(expected((X /Int 4) %Int 4), expected(X %Int 4)) </k>
endmodule
