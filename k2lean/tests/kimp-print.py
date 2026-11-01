#!/usr/bin/env python3
"""Write kimp with output to K's stdout stream, for `k2lean refine` with priority ranks.

usage: kimp-print.py KIMP_DIR OUT_DIR

Copies kimp's `expr.k` and `imp.k` and writes its `calc.k` with an `<output stream="stdout">`
cell and the statement `print ( E ) ;` (strict), which appends an integer to it. The stream
attribute brings K's stdout stream rules, at priorities 25 and 30, before the default 50: a
configuration whose output buffer has an element flushes it before any other rule steps. With
tests/kimp-unroll.py applied to the written `imp.k`, the two sides of `demos/ImpPrintRefine`
(`docs/design.md`, section 3.5). The script fails if `calc.k` does not contain exactly the text
it rewrites.
"""
import os
import shutil
import sys

src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)
for f in ("expr.k", "imp.k"):
    shutil.copy(os.path.join(src, f), os.path.join(dst, f))
text = open(os.path.join(src, "calc.k")).read()
edits = [
    ("""  imports CALC-SYNTAX
  imports EXPR-RULES
""", """  imports CALC-SYNTAX
  imports EXPR-RULES
  imports LIST
"""),
    ('''  syntax Stmt ::= Id "=" Expr ";" [group(stmt), strict(2), format(%1 %2 %3%4)]
''', '''  syntax Stmt ::= Id "=" Expr ";" [group(stmt), strict(2), format(%1 %2 %3%4)]
                | "print" "(" Expr ")" ";" [group(stmt), strict, format(%1%2%3%4%5)]
'''),
    ('''    <env color="yellow"> $ENV:Map  </env>
''', '''    <env color="yellow"> $ENV:Map  </env>
    <output stream="stdout"> .List </output>
'''),
    ('''  rule [assign]:''', '''  rule [print]:
    <k> print ( I:Int ) ; => .K ... </k>
    <output> ... .List => ListItem(I) </output>

  rule [assign]:'''),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"kimp-print.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(os.path.join(dst, "calc.k"), "w").write(text)
