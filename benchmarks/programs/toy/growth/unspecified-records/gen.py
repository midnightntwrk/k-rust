# Usage: gen.py T
# Prints the RING definition: substrString with two recurring equations whose two-conjunct
# requires leave records unspecified, started from substrString("abc", n(T), n(0)).
# Equation attempts grow about threefold per level of T.
import sys
t = int(sys.argv[1])
print('''module RING-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= "a"
endmodule
module RING
  imports RING-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= r(K)
  syntax Int ::= n(Int) [function]
  rule n(I) => I
  syntax String ::= w(String) [function]
  rule w(S) => "a" +String S requires lengthString(S) >Int 100 andBool lengthString(S) >Int -1
  rule substrString(S, I, J) => w(substrString(S, I -Int 1, J)) requires J <Int I -Int 1 andBool 1 >Int 0
  rule substrString(S, I, J) => w(substrString(S, I -Int 1, J)) requires J <Int I -Int 1 andBool 2 >Int 0
  rule substrString(S, I, J) => substrString(S, %d, J) requires J ==Int I -Int 1
  rule <k> a => r(substrString("abc", n(%d), n(0))) </k>
endmodule''' % (t, t))
