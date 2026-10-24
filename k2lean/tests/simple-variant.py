#!/usr/bin/env python3
"""Write a variant of SIMPLE (K's tutorial `simple-untyped.md`) for `k2lean relate`.

usage: simple-variant.py IN/simple-untyped.md OUT/simple-variant.md

The variant is the same language written differently, the way a refactoring or a second author
would write it:

- three constructors get other KORE symbols (`symbol(...)`): the `while` statement, the
  function value `lambda(_,_)` and the environment-recovery item `setEnv(_)`; their concrete
  syntax is unchanged, so `relate` matches them by syntax;
- the arithmetic rules move from the middle of the module `SIMPLE-UNTYPED` to its end, and the
  two rules of `&&` change places, so the rules come in another order (another `Step`
  constructor order and another execution order).

The new symbols are chosen so that each constructor keeps its position among its sort's
constructors (the generated libraries order constructors by symbol): the translation then
preserves the order of every term, which `relate` needs for the canonical maps of SIMPLE's
configuration (`docs/design.md`, section 3.2). The script fails if the source does not contain
exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()


def replace_once(text, old, new):
    if text.count(old) != 1:
        sys.exit(f"simple-variant.py: expected exactly one occurrence of {old!r}")
    return text.replace(old, new)


text = replace_once(text, '| "while" "(" Exp ")" Block\n',
                    '| "while" "(" Exp ")" Block [symbol(whileLoop)]\n')
text = replace_once(text, "| lambda(Ids,Stmt)\n", "| lambda(Ids,Stmt) [symbol(closure)]\n")
text = replace_once(text, "syntax KItem ::= setEnv(Map)\n",
                    "syntax KItem ::= setEnv(Map) [symbol(restoreEnv)]\n")
arith = """  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 requires I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 requires I2 =/=K 0
  rule - I => 0 -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
"""
text = replace_once(text, arith, "")
text = replace_once(text, "```k\nendmodule\n```", "```k\n" + arith + "endmodule\n```")
text = replace_once(text, "  rule true  && E => E\n  rule false && _ => false\n",
                    "  rule false && _ => false\n  rule true  && E => E\n")
open(dst, "w").write(text)
