// A definition with user record sorts declared in the semantic module, outside the closure of
// the program sort: `Tx` (a transfer of an amount with a fee, or `noop`) and `Account`. The
// transaction is the configuration variable `$TX`, a data hole addressed by name; the program
// itself is the single command `settle`.

module LEDGER-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "settle"  [symbol(settle)]
endmodule

module LEDGER
  imports LEDGER-SYNTAX
  imports INT
  imports BOOL

  syntax Account ::= account(Int, Int)       [symbol(account)]
  syntax Tx      ::= transfer(Int, Int)      [symbol(transfer)]
                   | "noop"                  [symbol(noop)]
  syntax Status  ::= "pending"               [symbol(pending)]
                   | "applied"               [symbol(applied)]
                   | "refused"               [symbol(refused)]

  configuration <k> $PGM:Pgm </k>
                <tx> $TX:Tx </tx>
                <account> account(1, 100) </account>
                <status> pending </status>

  rule [settle]: <k> settle => .K ... </k>
                 <tx> transfer(Amount, Fee) </tx>
                 <account> account(_Id, Balance => Balance -Int Amount -Int Fee) </account>
                 <status> _ => applied </status>
    requires Amount >=Int 0 andBool Fee >=Int 0 andBool Amount +Int Fee <=Int Balance
  rule [refuse]: <k> settle => .K ... </k>
                 <status> _ => refused </status>
    [owise]
endmodule
