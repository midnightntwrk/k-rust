// A sort of the definition below a library sort whose values are constructor terms: `Acct < JSON`,
// as KEVM's `Account < JSON`, and `Int < JSONKey` between two library sorts, as KEVM's. The rule
// matches an account injected into JSON and builds the JSON entry `N : acct(N)`, whose key is an
// Int injected into JSONKey and whose value an account injected into JSON.
requires "json.md"

module LIBSUB-SYNTAX
  imports INT-SYNTAX
  imports JSON-SYNTAX
  syntax Acct ::= acct(Int) [symbol(acct)]
  syntax JSON ::= Acct
  syntax JSONKey ::= Int
  syntax Cmd ::= wrap(JSON) [symbol(wrap)] | done(JSON) [symbol(done)]
endmodule

module LIBSUB
  imports LIBSUB-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>
  rule [entry]: <k> wrap(acct(N)) => done(N : acct(N)) </k>
endmodule
