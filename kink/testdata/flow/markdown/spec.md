# Lit: a literate tiny language

Flow fixture (F-10): a Markdown specification. Its K text is the content of the
fences the selector `k` selects; everything else is prose, which k-rust reduces
to whitespace. The prose quotes K-looking text on purpose: this rule is not K,
rule [inc]: inc I:Int => I1 -Int I2, and neither is I +Int 1 here.

```k
module LIT-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "inc" Exp   [strict, symbol(inc)]
               | "dec" Exp   [strict, symbol(dec)]
               | "twice" Exp [strict, symbol(twice)]
               > left:
                 Exp "+" Exp [strict, symbol(add)]
endmodule
```

Between the fences: the module `LIT` starts in the next fence, and a rule
written here, rule I1:Int + I2:Int => I1 -Int I2, is prose.

```k
module LIT
  imports LIT-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule [inc]: inc I:Int => I +Int 1
  rule I1:Int + I2:Int => I1 +Int I2
```

The next fence is tagged `ghost`, which the selector does not select, so the
rule inside it is not part of `LIT`:

```ghost
  rule [ghost]: dec I:Int => I
```

The module ends in this fence. `dec` carries its label in the `[label(dec)]`
form, and `+Int 1` occurs twice in `twice`.

```k
  rule dec I:Int => I -Int 1 [label(dec)]
  rule [twice]: twice I:Int => I +Int 1 +Int 1
endmodule
```

Closing prose: rule [twice] adds two, and I +Int 1 is not K here either.
