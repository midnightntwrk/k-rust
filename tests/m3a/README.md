# M3A independent expression oracle

This tree freezes the external acceptance contract for the first executable
IMP slice. It does not import KRS production crates and the handwritten K
definition is not generated from KRS output.

`fixtures/expr.k` is a deliberately small transcription of the upstream IMP
`expr.k`. It retains the relevant semantic surface:

- `Int` and `Bool` values and their injection through `Value` into `Expr`;
- the parentheses bracket production;
- unary `-` and `!`;
- arithmetic, comparison, equality, `&&`, and `||` productions;
- all six precedence boundaries and their left-associativity declarations;
- unary `strict`, binary `seqstrict`, and short-circuit `strict(1)`;
- all 18 expression rewrite rules and the `$PGM:Expr` computation cell.

The exact upstream and handwritten source hashes are in `pins.json`. The
reference frontend is K 7.1.337 at commit
`4a46d1231473b599c699160132fd6e76a5c46406`; the native frontend is k-rust
0.3.0 at commit `58f33885b736148dae189623d1aac989ce9be475`.

## Corpus contract

The nine accepted inputs make precedence and associativity observable in the
full KAST v4 trees. They distinguish multiplication from addition,
parenthesized grouping, left-associative subtraction and division, unary
binding, comparison before equality, and `&&` before `||`. The last case also
places division by zero in the skipped right operand, so a successful `true`
normal form is direct evidence for `strict(1)` short-circuiting.

Every accepted input is checked through both `kast` and `kparse`, executed with
the LLVM backend, and passed through the reference `program` unparser. The
normalizer retains every KAST node and key and fails on unknown node or label
shapes. Eight terms survive parse/unparse/parse exactly. K 7.1.337 unparses the
authored unary term `- 1 + 2` as `-1 + 2`; reparsing changes the unary
application into one signed `Int` token. This is recorded as an exact expected
frontend mismatch, not normalized away.

The rejected corpus separates two different failure classes:

- `rejected/syntax` must fail parsing. Both EOF diagnostics select authored
  line 2, column 1 exactly.
- `rejected/semantic-type` must parse as `Expr`, because IMP deliberately uses
  one syntactic expression sort, but must remain stuck rather than reach a
  `Value` normal form. The cases are `true + 1` and `! 0`.

The induced definition error independently checks that K selects the authored
`@` at `fixtures/induced-definition-error.k:3:17-3:18`.

## Strictness and source-structure evidence

The compiled reference artifacts must contain exactly 24 generated contexts:
20 from the ten `seqstrict` binary productions and four from the two unary and
two short-circuit productions. The main compiled module must contain exactly
24 heat and 24 cool rules.

The native probe uses only public pinned k-rust APIs. Its outer parser/lowerer
matches all 19 project grammar productions plus the priority and associativity
groups after three explicit normalizations: enumerated compiler metadata,
unordered members within an associativity/priority group, and k-rust's string
versus Java's zero-parameter `KLabel` spelling for `bracketLabel`. Unknown
sentences, attributes, and nodes are retained.

Two native differences remain visible:

- outer lowering retains the 18 rules and configuration as unresolved bubbles,
  whereas Java `parsed.json` contains resolved rules and generated cell syntax;
- full public k-rust loading reaches the pinned `domains.md`, then stops in
  `ARRAY-IN-K` because that ambiguous rule requires native Z3 sort inference.

Consequently this oracle proves the source grammar agreement but does not
claim native expression-program parsing or execution.

## Verification

Run exactly:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/m3a/verify.py
```

The frozen verifier SHA-256 is
`8cf21899e30a9a6f41e13b4310989ee535314907954e50df9c9f325bee6348f9`.
Its native evidence is the exact public-loader diagnostic fragment
`module "ARRAY-IN-K" ... requires native Z3 sort inference`; a different
failure does not satisfy the expected-mismatch check.

The command fails closed on a source/hash drift, wrong tool pin, changed parse
tree, precedence or associativity change, missing strictness expansion,
execution mismatch, diagnostic relocation, unexpected native result, or a
normalizer shape it does not understand. Installed pyk is reported for
capability visibility but is never imported by the verifier.
