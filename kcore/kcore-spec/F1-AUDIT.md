# Theory audit of F1's fixed texts

Date: 2026-11-07. Subject: the axioms that F1's three fixed texts (`prelude/f1-{none,bool,int}.kore`, Prelude.lean) put into Γ_D.
Danger looked for: an axiom false in the intended standard model. Γ_D with a false axiom has no standard model, and `StdModelOK`, so soundness and completeness, would fail or hold vacuously.
The standard model is the one Hooks.lean defines (Q7): Bool the two Booleans, Int ℤ with truncating `/Int` and `%Int` and Euclidean `divInt` and `modInt` (all undefined at divisor 0), `==K` equality of values, a Map a finite function. Symbols F1 does not interpret (`>>Int`, `^Int`, `log2Int`, …) are interpreted by any functions consistent with their axioms; where a function symbol is defined by an equation, that equation is its interpretation.
Γ_D reads every axiom but those marked `[simplification]` (Curate.lean, decision D2), so simplification lemmas are not in Γ_D and are not audited here; whether they are true is `G-theory-audit`'s wider question.

## The texts and what each adds

Counted by `probe/extract_fixed.py` (sentences of the user module) [V]:

| text | sentences | over the previous text | of which axioms in Γ_D |
|---|---:|---|---:|
| none (peano) | 162 | F0's fixed text (`kcore-spec/prelude/f0-prelude.kore`, audited at M1.3, STATEMENTS.md §5), plus `import K` and the three `⊤ ∨ ⊥` no-junk axioms of Bool, Int and KConfigVar that F0's `emit` wrote | 0 new |
| bool | 214 | 9 hooked symbols, 19 simplification lemmas, 9 functional axioms, 15 equations | 24 |
| int | 328 | 34 symbols, 76 simplification lemmas, 20 functional axioms, 11 equations (over bool) | 31 |

`imports MAP` adds nothing: the K prelude already declares Map, and the texts of a definition with and without it are equal [V: probe `mapa` against `inta`].

## BOOL (24 axioms)

Functional (`∃v. v = f(x̄)`), 9: `notBool`, `andBool`, `andThenBool`, `orBool`, `orElseBool`, `xorBool`, `impliesBool`, `==Bool`, `=/=Bool`. All total on the Booleans: true.

Equations, 15 (premise: the arguments match the patterns; `_` is a variable):
- `notBool true = false`, `notBool false = true`;
- `true andBool B = B`, `false andBool _ = false`; the same two for `andThenBool`;
- `false xorBool B = B`, `B xorBool B = false`;
- `true orBool _ = true`, `false orBool B = B`; the same two for `orElseBool`;
- `true impliesBool B = B`, `false impliesBool _ = true`;
- `B1 =/=Bool B2 = notBool (B1 ==Bool B2)`.

Each holds in the two-element Boolean algebra, and Hooks.lean computes the same function (`andThenBool` and `orElseBool` strict, Q10, which these equations do not contradict: in a model every argument is an element). Result: **no false axiom; nothing curated.**

## INT (31 axioms)

Functional, 20: `~Int`, `*Int`, `+Int`, `-Int`, `&Int`, `xorInt`, `|Int`, `minInt`, `maxInt`, `absInt`, `<=Int`, `<Int`, `>=Int`, `>Int`, `==Int`, `=/=Int`, `==K`, `=/=K`, `#if_#then_#else_#fi`, `freshInt`.
All total in the standard model (the bitwise ones on ℤ in two's complement). None of the partial symbols (`/Int`, `%Int`, `divInt`, `modInt`, `>>Int`, `<<Int`, `^Int`, `log2Int`, `Map:lookup`, `_Map_`) has a functional axiom [V: the list above is every functional axiom the text adds]. True.

Equations, 11:
- `K1 =/=K K2 = notBool (K1 ==K K2)`: true (`==K` is equality of values).
- `#if C #then B1 #else B2 #fi = B1` requires `C`; `= B2` requires `notBool C`: true.
- `I1 =/=Int I2 = notBool (I1 ==Int I2)`: true.
- `minInt(I1, I2) = I1` requires `I1 <Int I2`; `= I2` requires `I1 >=Int I2`: true, and Hooks' `min` agrees.
- `freshInt(I) = I`: true, and Hooks agrees.
- `I1 divInt I2 = (I1 -Int (I1 modInt I2)) /Int I2` requires `I2 =/=Int 0`: with Euclidean `modInt` (0 ≤ r < |I2|), `I1 - r` is a multiple of `I2`, so the truncating quotient is exact and equals the Euclidean quotient. True; Hooks uses Lean's `Int.ediv`, `Int.emod` and `Int.tdiv`, which satisfy it.
- `I1 dividesInt I2 = (I2 %Int I1) ==Int 0`: defines `dividesInt`; at `I1 = 0` the right side is undefined, so `dividesInt(0, _)` is undefined in every model. No axiom says `dividesInt` is total, so this is consistent.
- `bitRangeInt(I, IDX, LEN) = (I >>Int IDX) modInt (1 <<Int LEN)` and `signExtendBitRangeInt(…) = …`: definitions of two non-interpreted functions in terms of others; partial where the shifts are; no functional axiom for either. Consistent.

Result: **no false axiom; nothing curated.**

## What this does not cover

- The 95 simplification lemmas of the BOOL and INT texts (not in Γ_D).
- A proof that the standard model satisfies these axioms: argued here, axiom by axiom; the Lean statement is `StdModelOK` (root track).
- Fixed texts for other imports (STRING, LIST, SET, BYTES, …): not in F1.
