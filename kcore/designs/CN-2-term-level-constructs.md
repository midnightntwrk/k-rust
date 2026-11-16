# CN-2: the term- and carrier-level constructs triage refused as R-c: RANGEMAP, `assoc`/`comm` on a constructor production, matching-logic connectives and set variables in a read sentence, a user sort hooked to a builtin carrier

Owner direction 2026-11-15: support each of these before R2 unless a first-principles reason shows the construct has no meaning KCore can state.
Lean tree read: `kcore-spec` at `1e306534` (`jj file show`). Nothing here was elaborated or run: every Lean block is **to run**.
"Shown" means shown by reading the quoted definition or text; "suspected" means argued, not checked.
Cost scale for a unit: S (one short session, under 300 lines of Lean), M (300 to 900), L (900 to 2500), XL (more).

## 0. Result

| Group | Verdict | Cone declarations that change | Headline texts | Cost |
|---|---|---|---|---|
| S. user sort hooked to `INT.Int` (or Bool, Float, String, Bytes) | support | `Lib` (one field), `dvOK`, `paramVal`, `distinctSorts` | kept | S |
| (c) RANGEMAP in term positions (sort, constructor, 15 hooks interpreted, 3 hooks parameters) | support | `CollKind`, `sortOf`, `builtinColls`, `collNoJunk`, `collAxioms`, `hookTable`, `hookSigs`, `silentTable`, the registry | kept | M + M |
| (c) a RANGEMAP symbol binding a variable in a left side | support needs a `ΓColls` family for range maps (unit c3); until then refused by name | `collAxioms`, `isCollPat` | kept | L |
| (d) `comm`, `assoc` on a constructor production | support as an **open generator**: a parameter symbol whose raw application is a value where the interpretation keeps it | `ParamSig`, `sortOf`, `paramVal`, `gens`, `consItemsK`, `enumerable` | kept; the `assoc` law is a guard on H, not an axiom of Γ | XL |
| (e) connectives as conditions, splits and fresh variables | support: `Term` gains nothing; a new `Cond`, read by `Rule` and `Clause` | `Cond` (new), `Rule`, `Clause`, `Step`, `NotApplies`, `RuleApplies`, `StepDecided`, `Eval`'s block, `applies`, `prioRuleK`, the clause equations | kept | M (reader) + L (rules) + L to XL (clauses) |
| (e) a set-valued right side of a rule (`#Or`, `#Top`, `#Exists`, `#Not(t)`) | is `?X` with a condition: owned by the existential-variable design | that design's (`Rule`, `Step`) | that design's | there |
| (e) three shapes kept refused, each with a first-principles reason | a quantifier or complement over a sort whose extent the text does not state; a function equation whose right side has two values; `@S` in the argument-abstracted form | none | | |

Three facts decide most of what follows.

F-A (shown). `KoreAML.tr` translates every connective and set variable (`Translate.lean:125-158`): Γ can state any written sentence. What lacks a notion is the kernel's side: `EvalTerm c σ t r` gives a term at most one value (`r : Option GroundTerm`), and `Step` relates values.

F-B (shown from `ΓDomains`, `Faithful.lean`, and TIE-0 F1). Γ states hooked and parameter symbols by their graphs **on values**, and a model of Γ may hold elements of Int, Bool, a token sort, and so of KItem and K, that are no value's. The text does not exclude them either: the no-junk axiom kompile writes for a domain-value sort is `\or(\top, \bottom)` (TRIAGE-B finding 8). So a sentence whose truth at given values depends on *which elements a sort has* (an unguarded quantifier, a complement, an application of a non-injective symbol to unknown arguments) is true in some models of the text and false in others. `sound_at` and `complete_at` quantify over all models of Γ, so no `Step` on values is sound and complete for such a sentence. This is the only reason used below to keep something refused, and it is used three times: (c) left sides without a `ΓColls` family, (d) left sides, (e) unguarded quantifiers.

F-C (shown). The kernel already has the mechanism for "the text leaves it open": a parameter symbol, interpreted by `c.hooks`, with Γ stating H's graph and every theorem for every H (`ParamSig`, `paramVal`, `ΓDomains` second disjunct). (d) is an instance of it.

## 1. Sub-case S: a user sort hooked to a builtin carrier under its own name

### 1.1 What the text states

`syntax MyInt [hook(INT.Int)]` is expected to give `hooked-sort SortMyInt{} [hook{}("INT.Int"), …]`, literals `\dv{SortMyInt{}}("5")`, and whatever hooked symbols the author declares over it (`syntax MyInt ::= MyInt "+My" MyInt [function, hook(INT.add)]`). Suspected: no fixture exists (TRIAGE-C finding 2 asks for one).
The text states a sort and symbols over it. The hook names say, by the builtin prose (trusted base 4), that the sort's values are the integers and `+My` is addition. No sentence relates `MyInt` to `Int`: no subsort, and the library's `+Int` is declared over `SortInt` only. So the meaning is a second copy of ℤ, apart from Int.

### 1.2 The Lean change (to run)

```lean
-- FixedSignature.lean, structure Lib: one field, at the end
  /-- the sorts hooked under their own name to a library sort with domain values (`(s, b)`: the
  values of `s` are the literals of `b`, one of Int, Bool, Float, String, Bytes) -/
  carriers : List (Srt × Srt) := []

def Lib.carrier (l : Lib) (s : Srt) : Srt := ((l.carriers.find? (·.1 == s)).map (·.2)).getD s

-- Value.lean
def dvOK (l : Lib) (s : Srt) : Lit → Bool
  | .int _ => l.carrier s == Srt.int
  | .bool _ => l.carrier s == Srt.bool
  | .tok t => s == Srt.kconfigVar || l.carrier s == Srt.string || l.tokenSorts.contains s ||
    ((l.carrier s == Srt.bytes || l.byteSorts.contains s) && t.toList.all (·.toNat < 256))
  | .float p e b => l.carrier s == Srt.float && KFloat.ok p e b

/-- A literal of a carrier sort as the library sort's literal, any other value unchanged. -/
def GroundTerm.toLib (l : Lib) : GroundTerm → GroundTerm
  | .dv s lit => .dv (l.carrier s) lit
  | v => v
/-- A library literal as a literal of `s` when `s` has that carrier; a collection as `withSort`. -/
def GroundTerm.asSort (l : Lib) (s : Srt) : GroundTerm → GroundTerm
  | .dv b lit => if l.carrier s == b then .dv s lit else .dv b lit
  | v => v.withSort s

-- Evaluation.lean, paramVal: the registry hook reads its arguments as the library's literals
      | some g => (c.hookRes g (vs.map (GroundTerm.toLib c.lib))).join.map (GroundTerm.asSort c.lib k.sig.result)

-- FaithOK.lean, distinctSorts: at the end
    ++ c.lib.carriers.map (·.1)
```

`hookTable`, `asInt` and every `xHooks` list keep their text: the hook still computes at `Srt.int`.
Reader: `scanCarrier` for a user `hooked-sort` whose hook is one of the five namespaces' sort hooks and whose name is not the library's (today no scanner takes it: TRIAGE-C finding 2); a user hooked symbol over it is a `ParamSig` with `impl := regHookOf hook`, which the reader already builds for cell collections.

### 1.3 Headline statements

All five keep their text. Proof changes: `paramVal_sorted` (the result's sort) needs `asSort`'s sort lemma; the value model needs that a literal of a carrier sort is one element and distinct literals are distinct, which `dvArityAll` and the distinctness disjunct of `ΓDomains` give by the same proof as for Int once the sort is in `distinctSorts`. `ΓFallback`'s first disjunct is stated over `hookSigs` at library sorts and is untouched; a silent point reached through a parameter is covered by `paramVal` reading `hookRes`.

### 1.4 Tie and FD-C

Declarations: row 19 (E). A user hooked symbol: the parameter family of `ΓDomains` (M); its `functional` axiom Ev. FD-C: not concerned.

### 1.5 Reading and reversal

S-1. The sort is a copy of the carrier, apart from the library sort. Reason: the text states no sentence relating the two. Reverse when the fixture's text holds a subsort or an equation between them; then that sentence is read as written.
S-2. If kompile rejects the declaration, the row is `refused` R-b with `kompile.txt` as evidence and nothing here is built.

## 2. Group (c): RANGEMAP

### 2.1 What the text states

The kompiled text (TRIAGE-C, all-builtins `definition.kore`; I did not open that file) holds `hooked-sort SortRangeMap{} [concat, element, hook{}("RANGEMAP.RangeMap"), unit]`, the constructor `RangeMap:Range : KItem × KItem → Range`, and 18 hooked function symbols. No equation defines them. Their meaning is domains.md's prose (lines 468-696 of the K 7.1.337 file; trusted base 4):

- 498-500: "a map whose keys are stored as ranges, bounded inclusively below and exclusively above. Contiguous or overlapping ranges that map to the same value are merged into a single range."
- 471-477: "range maps from `Int` to `KItem`"; "only supports `Int` keys".
- 600-602: concatenation is "a partial function only defined on range maps with non overlapping ranges".

So a value is a partial function from ℤ to KItem values that is constant on each of finitely many intervals, and the stated representation is the list of its **maximal** intervals. `elem([a, b), v)` is the function `v` on `a ≤ k < b`; concatenation is the union of two functions with disjoint domains and nothing otherwise. Merging is then not an operation: it is that two descriptions of one function are one value.

The construct has a meaning KCore can state. The triage's reason ("no constructor has it as result sort … RangeMap has no value in the kernel") is a missing carrier, not a missing meaning.

### 2.2 Carrier: no new `GroundTerm` constructor

Reading RM-1 (decided). A range map is `GroundTerm.map s es` of a collection sort of a fourth kind, its keys the `Range` constructor terms of its maximal intervals.
Reason: `GroundTerm.kore` then writes it as `_RangeMap_(_r|->_([a,b), v), …)` by the existing `koreEntries` with the sort's own unit, element and concatenation, `cmp` and the distinctness disjunct apply unchanged, and no recursion over `GroundTerm` gains a case.
Reverse when a proof needs the key order to be the numeric order of lower bounds and `cmp` does not give it; then the canonical form sorts by `cmp` instead of by bound (uniqueness needs only a strict total order).

```lean
-- Core.lean
inductive CollKind where
  | map | set | list
  /-- a range map: a `GroundTerm.map` whose keys are `Range` terms of its maximal intervals -/
  | rangeMap

def builtinColls : List CollSig :=
  [⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩,
   ⟨Srt.set, .set, Srt.kitem, none, setUnit, setElem, setConcat⟩,
   ⟨Srt.list, .list, Srt.kitem, none, listUnit, listElem, listConcat⟩,
   ⟨Srt.rangeMap, .rangeMap, Srt.range, some Srt.kitem, rmUnit, rmElem, rmConcat⟩]

-- Hooks.lean (before the hooks)
/-- A KItem that is an Int. -/
def asKInt : GroundTerm → Option Int
  | .inj a b v => if a == Srt.int && b == Srt.kitem then asInt v else none
  | _ => none
/-- `[a, b)` with Int bounds, `a < b`. -/
def asRange : GroundTerm → Option (Int × Int)
  | .ctor f [x, y] => if f == rangeCtor then
      (asKInt x).bind fun a => (asKInt y).bind fun b => if a < b then some (a, b) else none else none
  | _ => none
/-- Maximal intervals in order: each key a proper range, each ending at or before the next begins,
and two that touch carry different values. -/
def rangesOK : Entries → Bool
  | [] => true
  | [(k, _)] => (asRange k).isSome
  | (k, v) :: (k', v') :: es => (match asRange k, asRange k' with
      | some (_, b), some (a', _) => decide (b ≤ a') && !(b == a' && GroundTerm.cmp v v' == .eq)
      | _, _ => false) && rangesOK ((k', v') :: es)

-- Value.lean, sortOf, the `.map` case
    | .map s es => match c.collOf s with
      | some k => match k.val with
        | some vs => if (k.kind == .map && keysSorted es || k.kind == .rangeMap && rangesOK es) &&
                        entriesOK k.key vs es then some s else none
        | none => none
      | none => none
```

`rangesOK` must sit before `sortOf` (Value.lean) or `sortOf` must take it from a file both import: the implementer places it; the text above is the definition.

### 2.3 The hooks

Fifteen are interpreted, three are parameters. Each is a function of the denoted partial function, computed on the canonical list through three helpers:

```lean
/-- The entries as triples. -/
def rmTriples (m : Entries) : Option (List (Int × Int × GroundTerm))
/-- Canonical entries of a list of pairwise disjoint proper intervals: sorted by lower bound,
touching intervals of one value merged. -/
def rmCanon (ts : List (Int × Int × GroundTerm)) : Entries
/-- The intervals of `ts` less `[a, b)`. -/
def rmCut (a b : Int) (ts : List (Int × Int × GroundTerm)) : List (Int × Int × GroundTerm)
/-- The value at `k`, and the interval holding it. -/
def rmFind (k : Int) (ts : List (Int × Int × GroundTerm)) : Option (Int × Int × GroundTerm)

def rangeMapHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(rmUnit,      fun vs => match vs with | [] => some (.map Srt.rangeMap []) | _ => none),
   (rmElem,      -- [r, v]: the one interval, for a proper Int range
    fun vs => match vs with | [r, v] => (asRange r).map fun _ => .map Srt.rangeMap [(r, v)] | _ => none),
   (rmConcat,    -- defined where no interval of one meets an interval of the other
    …),
   (rmLookup,    -- [m, k]: rmFind's value
    …),
   (rmLookupOrDefault, -- [m, k, d]: rmFind's value, d where there is none or k is no Int
    …),
   (rmFindRange, -- [m, k]: rmFind's interval as a Range term
    …),
   (rmUpdate,    -- [m, r, v]: rmCanon (rmCut a b m ++ [(a, b, v)])
    …),
   (rmRemove,    -- [m, r]: rmCanon (rmCut a b m)
    …),
   (rmDifference, -- [m, n]: m less each interval of n cut to where m has n's value
    …),
   (rmUpdateAll, -- [m, n]: the intervals of n written over m in turn
    …),
   (rmRemoveAll, -- [m, S]: every member of S a proper range, each cut from m
    …),
   (rmKeys,      -- [m]: the Set of its Range terms, injected into KItem
    …),
   (rmInKeys,    -- [k, m]: (rmFind k m).isSome, false for a k that is no Int
    …),
   (rmSize,      -- [m]: the number of entries
    …),
   (rmInclusion, -- [m, n]: every k of m has m's value in n
    …)]

def hookTable := boolHooks ++ … ++ bytesHooks ++ iteHooks ++ rangeMapHooks
```

`silentTable` gains, with the prose line for each:

| Key | Silent where | Prose |
|---|---|---|
| `rmElem` | the range is not a proper Int range (`asRange` fails) | 476-477 name Int keys only; an empty or inverted range is not described |
| `rmLookup`, `rmFindRange` | the key is in no interval | 534-535, 555-556: "an exception during concrete execution", of a run (the reading `silentTable` already takes for `memsetBytes`) |
| `rmUpdate`, `rmRemove`, `rmRemoveAll` | a range argument is not proper | as `rmElem` |
| `rmInclusion` | the two maps are equal | 665: "a strict subset" against the name `<=RangeMap` (as `<=Set`) |

`rmConcat` on overlapping maps is **not** silent: 600-602 say it is not defined there, and Γ states ⊥.
Parameters (no interpretation, `Builtins.lean` module `RANGEMAP`): `RangeMap:choice` ("an arbitrarily chosen key", 676-679), `keys_list` and `values` (a List "of all" ranges or values, 630, 648: no order is stated).

Readings.
RM-2. `size`, `keys` and `find_range` read the maximal intervals. Reason: line 499-500 states the merge. Reverse when a K text's own equation over RangeMap counts unmerged pairs.
RM-3. `lookup` and `find_range` off the keys are silent, not ⊥. Reason: the prose speaks of a run's exception and writes no `#Bottom`. Both readings pass: with ⊥, `Γ ⊧ ¬⌈m[k]⌉` is provable off the keys and a rule whose right side looks up a missing key provably gives no step; with silent, neither that nor a value is provable over all H. Left to the orchestrator; the table above takes silent because it asserts less.
RM-4. `keys_list` and `values` are parameters everywhere, also at maps of at most one interval, where the prose fixes the value. Reason: three table entries and their silent predicates for points no definition is known to use; the reading asserts less than the prose, nothing false. Reverse when a row needs the value at a one-interval map.

### 2.4 Left sides

`_RangeMap_`, `_r|->_` and `.RangeMap` carry the collection attributes, so a K author may write `([A, B) r|-> V) Rest` in a left side.
Its meaning is statable: `PatVal.coll` reads "the value the operation builds from the parts' values" for any collection pattern symbol.
What is missing is on Γ's side (F-B): `ΓDomains` gives the three graphs on values only, and under a negation or in `complete_at` a model may match the pattern with a non-value part. For maps, sets and lists `ΓColls` closes this with axioms true of the intended model. A range map needs its own: an entry is not atomic (`[0,10) r|-> v` is `[0,3) r|-> v` with `[3,10) r|-> v`), so `mapElemAtomAx` and `mapDecompAx` are false of it.

Decided for the freeze: in a left side a RANGEMAP symbol all of whose variables are bound elsewhere is cut to a fresh variable with `V ==K t` in the `requires` (the reader's `keyCut` reading, TRIAGE-C row B51). One that binds a variable is refused `rangeMapPattern` until unit c3. The reason is F-B, not a missing notion in `Term`.

Unit c3's family (to run; each is true of partial functions that are constant on finitely many intervals):

```lean
def rangeMapCollAxioms : List KoreAML.P :=
  [ -- ⌈unit ∧ concat(m₁, m₂)⌉ → m₁ = unit ∧ m₂ = unit                       (as mapUnitSplitAx)
    rmUnitSplitAx c k,
    -- ¬⌈unit ∧ elem(r, b)⌉                                                    (as mapElemNotUnitAx)
    rmElemNotUnitAx c k,
    -- refinement: ⌈concat(m₁, m₂) ∧ concat(n₁, n₂)⌉ →
    --   ∃ p q r s. m₁ = concat(p, q) ∧ m₂ = concat(r, s) ∧ n₁ = concat(p, r) ∧ n₂ = concat(q, s)
    rmRefineAx c k,
    -- a part of an entry is an entry of a sub-range with the same value, or the unit:
    --   ⌈elem(r, b) ∧ concat(m₁, m₂)⌉ → m₁ = unit ∨ m₂ = unit ∨ ∃ r₁ r₂. … (two adjacent sub-ranges)
    rmElemSplitAx c k ]
```

Whether these four decide every match of a range-map pattern against a value (what `FaithfulCollPat` proves for maps) is **not known**: `rmElemSplitAx` as sketched covers a split in two, and a part of an interval may be a union of several sub-intervals. This is the unit's risk; it is why c3 is L and last.

### 2.5 Headline statements

All five keep their text. Proof changes, units c1 and c2 only:
- `Model.ModelColls`: a range-map value denotes one element; `collNoJunk` for the fourth collection (a canonical list is its first entry concatenated with its canonical rest, by `rmConcat`'s definition); `collNoJunk`'s `el` treats `.rangeMap` as `.map` (an entry has a value sort).
- `collAxioms` gains `| .rangeMap => []` (c3 replaces `[]`).
- Every `decide` or case split over `builtinColls` and `CollKind` gains a case (`builtinColl`, `collSig`, `valSort`, the three-element lemmas of `FaithOK.lean`). Count unknown: I did not read them.
- `hookTable_keys` (`decide +kernel`) re-runs with 15 more keys.
- The registry: `Srt.range`, `Srt.rangeMap`, `rangeCtor` and 18 symbols are new numbers. `BuiltinNames.nNewSorts` and `nNewSyms` grow, so `nRegSorts` and `nRegSyms` grow and **every package's own sorts and symbols renumber**: all generated packages are regenerated by the integration lane. This is the item most likely to break elsewhere.

### 2.6 Tie and FD-C

- Declarations: row 19 (E for G-sort and G-arity).
- `functional` axioms of the hooks declared `total`: row 9, Ev. At a silent point where H gives no value the Ev statement needs the guard that H gives one (as `<=Set` today).
- The associativity and unit axioms kompile writes for a hooked concatenation with those attributes (expected for `_RangeMap_`; not seen): row 15, `inert collectionLaw`, direction Ev under FD-1. FD-C's table gains a column: associativity and both units hold of `rmConcat` at values (union of functions with disjoint domains; suspected, same argument as Map). No idempotence axiom is expected. The reader's `isCollectionLaw` must take `_RangeMap_` as a concatenation of a collection sort (TRIAGE-B finding 4's repair covers it once the sort is in `allColls`).
- M: the graphs (`ΓDomains` first disjunct), `collNoJunk` of the fourth collection, `ΓFallback` at the silent keys. All existing families.

## 3. Group (d): `assoc` and `comm` on a constructor production

### 3.1 What the text states

Fixture `e2-comm-ctor` (`syntax Exp ::= "x" | Exp "&" Exp [symbol(and), comm] | Exp "|" Exp [symbol(or), assoc]`), `kore.txt`, shown:
- `symbol Lbland{}(SortExp{}, SortExp{}) : SortExp{} [functional{}(), …]`, likewise `Lblor`: neither `constructor` nor `injective` nor `function`.
- sentence 151, 173: `\exists(Val, \equals(Val, Lbland(K0, K1)))`, same for `Lblor`: each is total and single-valued.
- sentence 172: `Lblor(Lblor(K1,K2),K3) = Lblor(K1,Lblor(K2,K3))`.
- sentence 182: `\or(∃ Lbland(X0,X1), ∃ Lblor(X0,X1), Lblx(), \bottom)`: every element of Exp is `x` or an application of one of the two.
- no no-confusion axiom names `and` or `or`; no axiom carries `comm`.

So the text states: two total binary operations on Exp, one associative, and Exp generated by `x` and the two. It states **nothing** about which applications are equal. Its models that satisfy the least-fixed-point form of no-junk are exactly the quotients of the free term algebra by a congruence that contains associativity of `or`: the free one, the commutative one, the one-point one, and every one between.

"Support" is therefore reading exactly what is written: the operations are generators whose identifications are open. The three other readings each assert something the text does not:
- as constructors: injectivity and distinctness (for `or` these contradict sentence 172);
- as functions without clauses (today's reading): `consItemsK`'s no-junk over the remaining constructors, that is `∀ v : Exp, v = x` (TRIAGE-B's "to run", suspected);
- as free modulo the written law (a normal form in the kernel): for `comm` nothing is written, so this is the constructor reading; for `assoc` it adds "no other identification".

An open identification is what a parameter is for (F-C). The one thing a plain parameter lacks is values: `and(x, x)` must be able to be a value that is not `x`.

### 3.2 The Lean change (to run)

```lean
-- Core.lean
structure ParamSig where
  sig : CtorSig
  impl : Option Sym := none
  /-- an **open generator**: a symbol the text declares total, lists among its result sort's
  generators and says nothing else of. Its application to values is the interpretation's value,
  and where the interpretation gives none or gives the raw application back, the raw application
  `.ctor f vs`, which is then a value. -/
  raw : Bool := false

-- Value.lean
/-- The open generator `f`, if it is one. -/
def Semantics.lookupOpen (c : Semantics) (f : Sym) : Option ParamSig :=
  c.params.find? fun k => k.raw && k.sig.name == f
/-- The interpretation leaves `f(vs)` raw. -/
def Semantics.keepsRaw (c : Semantics) (f : Sym) (vs : List GroundTerm) : Bool :=
  match c.hooks.app f vs with
  | none => true
  | some w => GroundTerm.cmp w (.ctor f vs) == .eq

-- sortOf, the `.ctor` case, after the overloading symbols
        | none => match c.lookupOpen f with
          | some k => if sortsOf ts == some k.sig.args && c.keepsRaw f ts then some k.sig.result else none
          | none => none

-- Evaluation.lean, paramVal, the `impl = none` branch
      | none => if k.raw then some ((c.hooks.app f vs).getD (.ctor f vs)) else c.hooks.app f vs
      -- then, as today: .filter fun v => c.sortOf v == some k.sig.result

-- DefinitionWf.lean
def gens (N : Srt) : List Gen :=
  (c.ctorSigs.filter (·.result == N)).map .ctor ++
  (c.ovlSigs.filter (·.result == N)).map .ctor ++
  (((c.params.filter (·.raw)).map (·.sig)).filter (·.result == N)).map .ctor ++
  (sortBy id ((c.subsorts.filter (·.2 == N)).map (·.1))).map .inj
def Semantics.isOpenGen (c : Semantics) : Gen → Bool
  | .ctor k => (c.lookupOpen k.name).isSome
  | .inj _ => false
-- enumerable gains the conjunct  !c.params.any (·.raw)

-- Faithful.lean, consItemsK, perSort: functionality, injectivity and distinctness over the
-- generators that are not open; no-junk over all of them
    let gs := c.gens N
    let fr := gs.filter (!c.isOpenGen ·)
    (fr.map (Gen.toK c)).map (KoreAML.Cons.funItem (n N)) ++
    ((fr.map (Gen.toK c)).filter (!·.argSorts.isEmpty)).map (KoreAML.Cons.injItem (n N)) ++
    (pairs fr).flatMap (…as today…) ++
    [KoreAML.Cons.noJunkItem (n N) (gs.map (Gen.toK c))]
```

With `HookParams.none` every raw application is a value: the default interpretation is the free model.
`sortOf` no longer recurses into the interpretation's answer: whether `.ctor f vs` is a value is read off `c.hooks.app f vs` at that one point, and `paramVal`'s existing filter makes an answer that is no value read as undefined (the reading `paramVal` already takes for an ill-sorted answer).
What Γ states of an open generator is then only what existing families state: its arity (`ΓSig`), H's graph on values (`ΓDomains`, parameter disjunct), that each value is one element, that distinct values of a sort below KItem are distinct (the graph of `_==K_`, `apartSort`), and no-junk with it among the generators.
No law is in Γ.

Reader (unit d2): a `symbol` (not hooked) with `functional`, without `constructor` and without `function`, that its result sort's no-junk axiom lists, is a `ParamSig` with `raw := true` (today `symProdBody` makes it a function with no clause, TRIAGE-B finding 3). Its `[assoc]` axiom is classified `openLaw (assoc)`, not `collectionLaw` (finding 4). The no-junk axiom then matches `consItemsK`'s and is no `inertMismatch`.

### 3.3 The law: a guard on H, not an axiom

Reading OG-1 (decided). The written associativity axiom is not put in Γ. It is tied in direction Ev under the guard

```lean
def OpenAssoc (c : Semantics) (f : Sym) : Prop :=
  ∀ a b d, c.paramVal f [a, b] ≠ none → c.paramVal f [b, d] ≠ none →
    (c.paramVal f [a, b]).bind (fun ab => c.paramVal f [ab, d]) =
    (c.paramVal f [b, d]).bind (fun bd => c.paramVal f [a, bd])
def OpenTotal (c : Semantics) (f : Sym) : Prop :=
  ∀ k vs, c.lookupOpen f = some k → c.sortsOf vs = some k.sig.args → c.paramVal f vs ≠ none
```

and the library gives the interpretation that meets it (`assocH f`: `H.app f [a, b]` is the right-nested application of the flattened arguments).
Reason: with the axiom in Γ, `Γ (c.withHooks H)` has no model at an H that is not associative, so `sound_hyp`'s consistency conjunct is false there and `FnHyp` would have to gain a hypothesis on H: a headline weakened. Without it every headline holds for every H, and the H that are models of the text are those the guard selects. The same situation exists today for a `functional` axiom of a parameter symbol at a partial H.
Reverse when the owner accepts `FnSolves` (and so `FnHyp`) gaining "the interpretation satisfies the laws written for its open generators": then the law is a member of Γ, tied E by equality of patterns, and `consistent_of` needs it of H.
What each makes provable: with OG-1, a statement about a definition with an `assoc` generator is proved for every H and is about the text's models only where `OpenAssoc` is assumed in the statement; with the reversal, `Γ ⊧` the law at all elements, and `sound_hyp` says nothing at a non-associative H.

Note for the orchestrator: at `HookParams.none` an `assoc` generator is free, so `none` is not a model of sentence 172. C10's row is at `none`; it is unaffected only if `kore.k` has no such symbol (not checked here).

### 3.4 Left sides

An open generator in a left side meets F-B: Γ has its graph on values only and no injectivity, so whether `and(A, B)` matches a value is open at elements the text does not delimit when Exp's argument sorts reach a domain-value sort.
Decided: all variables bound elsewhere: cut with `==K` (reader, as B51). Binding a variable: refused `openGeneratorPattern`, reason F-B.
Reverse (unit d4, not costed in detail): for a sort all of whose elements are values in every model of Γ (`closedSort`: its generators' argument sorts are constructor sorts with no domain-value, token or collection sort reachable; `e2-comm-ctor`'s Exp is one), `PatVal` gains

```lean
    | open {f : Sym} {ps : List Term} {vs : List GroundTerm} {v : GroundTerm}
        (ho : (c.lookupOpen f).isSome = true) (hs : PatVals c σ ps vs)
        (hv : c.paramVal f vs = some v) : PatVal c σ (.app f ps) v
```

and soundness of a negated match is by no-junk induction. Whether a lemma "every element of a closed sort is a value's" exists at `1e306534` I did not find out.

### 3.5 Headline statements

All five keep their text. What changes underneath:
- `sortOf` reads `c.hooks`. Every lemma of the form `(c.withHooks H).sortOf = c.sortOf`, and every `rfl` proof that a decided condition is the same for all H, holds only where `c.params.all (!·.raw)`, or must be re-proved from the fact that no decided condition applies `sortOf` to a raw open application. `Config c` now depends on H for such a definition. This is the invasive part and the reason for XL. I did not count the lemmas (`Exec.lean`, `Determinism.lean`, `Definition.wf_withHooks` are named in `Core.lean`'s comment on `hooks`).
- Model construction (`ModelCons`, `ModelDomains`): the carrier is the values under H. An open generator is interpreted by `paramVal`. `noJunkItem` with the open generators holds because every value of the sort is a free generator's or an open generator's application to values, and `paramVal f vs` is a value or nothing. `funItem`, `injItem`, `distItem` are no longer asked of them. Distinctness of raw values from others is `cmp`, as for an overloading symbol's raw application.
- `genWf` ("a value of a constructor sort is a constructor or an injection applied to values") admits a raw open application, as it admits an overloading symbol's.
- `sound_at`, `complete_at`: `EvalTerm.param` already reads `paramVal`; no new `EvalTerm` case. The proofs that read a parameter's graph are unchanged; the proofs by cases on a value of a constructor sort gain the raw-open case.

### 3.6 Tie and FD-C

- declarations: row 19. `functional` (151, 173): Ev under `OpenTotal` (true at `none` and at `assocH`).
- sentence 172: Ev under `OpenAssoc`; a new row "law of an open generator" in TIE-0's table.
- sentence 182 (no junk): E, row 14: Γ's least fixed point entails the written disjunction.
- M: H's graph for the generator (the parameter family), and with it which raw applications are values.
- FD-C: the `[assoc]` axiom of a symbol that is no collection concatenation leaves the `collectionLaw` class; FD-C's verdict (collection laws at values) does not speak of it.

## 4. Group (e): connectives, `\forall`, `\floor`, set variables, `@S`

### 4.1 A ground term's denotation and a pattern's

A term under a substitution of values denotes at most one value (`EvalTerm`'s `Option GroundTerm`). A pattern denotes a set of elements. Every K-level connective in a term position is one of four things:

1. a **predicate** (`#Ceil`, `#Floor`, `#Equals`, `\in`, `#Top`/`#Bottom` used as such, and their combinations): everything or nothing, at any sort. It is a condition.
2. a term **with** a condition: `t #And P`, which is `t` where `P` holds and nothing otherwise; `t #And u`, which is `t` where both are defined and equal.
3. a **set of several values**: `t #Or u`, `#Top` at a term's sort, `#Exists Y. t`, `#Not(t)`.
4. a **set variable**.

Application is pointwise, so every pattern equals a comprehension `{z | C(z)}` whose condition's atoms are "`t` has the value `z`"; (3) differs from (2) only in that `C` holds of more than one `z`.

Reading E-1 (decided). `Term` gains no pattern form. Positions are read as conditions (a new `Cond`), as fresh variables bound by the match, as a split into several rules, or, on a rule's right side, as an existential variable with a condition.
Reason: a pattern form in `Term` makes `EvalTerm` set-valued, and with it `Eval`, `Step`, `StepDecided`, `FnDet` and the value model; every occurrence the text can state without F-B's obstruction is expressible by the four devices, which leave `EvalTerm` as it is.
Reverse when a text the project must read holds a function equation with a many-valued right side that is not a contradiction (4.4 row FR-3).

### 4.2 The Lean change (to run)

```lean
-- Core.lean
/-- A condition of a rule or a clause: a matching-logic predicate over terms. Each form is the
KORE connective of the same name at the sentence's sort, its arguments terms. -/
inductive Cond where
  | top | bot
  | not (p : Cond) | and (p q : Cond) | or (p q : Cond) | implies (p q : Cond)
  /-- `\ceil{s,_}(t)`: t has a value -/
  | ceil (s : Srt) (t : Term)
  /-- `\equals{s,_}(t, u)`: both undefined, or both defined with one value -/
  | equals (s : Srt) (t u : Term)
  /-- `\in{s,_}(t, u)`: both defined with one value -/
  | mem (s : Srt) (t u : Term)
  /-- `\exists ȳ. \in(t, p) ∧ body`: t's value matches the pattern p under some values of the
  variables `ys` (numbered after the sentence's own), and body holds there -/
  | exMatch (ys : List Srt) (s : Srt) (p t : Term) (body : Cond)
  deriving Repr, Inhabited

structure Rule where
  vars : List Srt
  lhs : Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat
  /-- a predicate of the left side: the rule applies where it holds -/
  pre : Cond := .top
  /-- a predicate of the right side: the rule gives its step where it holds -/
  post : Cond := .top
-- Clause gains the same two fields (unit e3).

-- Evaluation.lean: the truth value of a condition, as a result
inductive Holds (c : Semantics) : Subst → Cond → Bool → Prop where
  | top {σ} : Holds c σ .top true
  | bot {σ} : Holds c σ .bot false
  | not {σ p b} (h : Holds c σ p b) : Holds c σ (.not p) (!b)
  | and {σ p q b b'} (h : Holds c σ p b) (h' : Holds c σ q b') : Holds c σ (.and p q) (b && b')
  | or {σ p q b b'} (h : Holds c σ p b) (h' : Holds c σ q b') : Holds c σ (.or p q) (b || b')
  | implies {σ p q b b'} (h : Holds c σ p b) (h' : Holds c σ q b') : Holds c σ (.implies p q) (!b || b')
  | ceil {σ s t r} (h : EvalTerm c σ t r) : Holds c σ (.ceil s t) r.isSome
  | equals {σ s t u r r'} (h : EvalTerm c σ t r) (h' : EvalTerm c σ u r') :
      Holds c σ (.equals s t u) (sameResult r r')
  | mem {σ s t u r r'} (h : EvalTerm c σ t r) (h' : EvalTerm c σ u r') :
      Holds c σ (.mem s t u) (r.isSome && sameResult r r')
  /-- t undefined: no match -/
  | exNone {σ ys s p t body} (h : EvalTerm c σ t none) : Holds c σ (.exMatch ys s p t body) false
  /-- t = v: true iff the body holds at some extension of σ under which p denotes v. `g` gives
  the body's result at each such extension. -/
  | exSome {σ ys s p t body v b} (g : Subst → Bool) (h : EvalTerm c σ t (some v))
      (hb : ∀ σ', Extends c σ ys σ' → PatVal c σ' p v → Holds c σ' body (g σ'))
      (hr : b = true ↔ ∃ σ', Extends c σ ys σ' ∧ PatVal c σ' p v ∧ g σ' = true) :
      Holds c σ (.exMatch ys s p t body) b
-- sameResult r r' : Bool := match r, r' with | none, none => true | some v, some w => cmp v w == .eq | _, _ => false
-- Extends c σ ys σ' : σ' agrees with σ on the sentence's variables and is well sorted at ys.

-- Step.lean
inductive RuleReqFails (c : Semantics) (σ : Subst) (r : Rule) : Prop where
  | intro {t v} (ht : r.req = some t) (he : EvalTerm c σ t v) (hv : v ≠ some (bool true)) : RuleReqFails c σ r
  | pre (h : Holds c σ r.pre false) : RuleReqFails c σ r
-- Step.rule gains   (hpre : Holds c σ r.pre true)   and   (hpost : Holds c σ r.post true)
-- RuleApplies gains the conjunct   Holds c σ r.pre true
-- StepDecided gains: beside the `requires`' result,  ∃ b, Holds c σ r.pre b ; beside the
--   right side's and the `ensures`',  ∃ b, Holds c σ r.post b

-- Statements.lean / Faithful.lean
-- Cond.kore c vs S : Cond → Kore.Pattern, each form as its connective at the sort S
--   (exMatch ys s p t body ↦ \exists over ys of \and(\in{s,S}(t, p), body))
-- applies:    \and C [lhs, reqPat C req, Cond.kore … r.pre]
-- prioRuleK:  right := \and C [rhs, reqPat C ens, Cond.kore … r.post]
```

`Holds` is positive: a negation is a result `false`, never a `¬`. For rules alone it is defined after `Eval`'s block. For clauses (unit e3) it joins the block (`Eval`, `Fails`, `ReqFails`, `EvalTerm`), `ReqFails` gains the `pre` constructor and `Eval.clause` the two premises; `clauseEquation` and `competingEquation` write `pre` into the premise and `post` beside the right side as lane CE writes `ens`.

A rule or clause with `pre = post = .top` has `Holds.top` for both: `Step`, `StepDecided` and Γ are what they were (the Γ patterns gain a `\top` conjunct, or the two functions omit a `.top`; the implementer chooses the second so that existing ties stay equalities).

### 4.3 What stays refused, and why (F-B)

- **A quantifier whose variable is not bound by a match or an evaluation**: `#Forall Y. {f(Y) #Equals g(Y)}`, `#Exists Y. {f(Y) #Equals 0}`, `#Floor(t)` for a term (`∀z. z ∈ t`), and `#Not(p)` or `#Top` *inside a predicate's argument*. Reason F-B: the text does not state which elements Y's sort has (for Int, Bool, a token sort, KItem, K, and every sort with such an argument), so the sentence is true in some of its models and false in others at the same values; no `Step` on values is sound and complete for it. Refused `openExtent`. This is the admissible reason: no meaning KCore can state, because the text gives none that is determined.
  Reverse per sort when Γ gains a closure axiom the builtin prose supports (TIE-0's TR-2 reversal: `⟦Bool⟧ ⊆ true ∨ false`; `⟦Int⟧ ⊆ μX. 0 ∨ X +Int 1 ∨ X -Int 1`), or for a `closedSort`; then `Cond` gains `ex (s) (body)` and `all (s) (body)` over values.
  `exMatch` is not of this kind: its variables are determined by matching a value against a constructor or collection pattern, which Γ's injectivity, no-confusion and `ΓColls` axioms pin at any elements. It is the shape `applies` already has.
- **A function equation whose right side has more than one value** (`f(X) => a #Or b` with `a`, `b` apart; `=> #Top`; `=> #Not(t)`): the sentence says `f(X)` *is* that set (an equation between sets, not a choice). The symbol is declared `function`, which K's manual reads as a partial function, and `consistent_of` covers single-valued functions (`FnDet`). Refused `manyValuedRightSide` as a text whose equation contradicts its declaration; recorded as such, not R-c.
  Reverse when the owner decides a symbol declared `function` may be many-valued: then `Eval` is set-valued and the row is R-c on `Eval` and `FnDet`.
- **`@S` in the argument-abstracted form** (4.5).

### 4.4 Position by position

Whether kompile accepts each shape outside a `[simplification]`, and what it writes, is **not in the tree**: the fixtures hold connectives in simplification axioms only (`e3-ml`), `#Or` on a left side (`e7-guardors`), and three left sides kompile's own check rejects (`e3-ml-and-lhs`, `-exists-lhs`, `-floor-lhs`: "Unsupported LHS of equation"). Every row below is "if the text holds it"; unit e0 makes the fixtures. A shape kompile rejects is `refused` R-b with its `kompile.txt`.

L: a rule's left side, at any depth under constructors and collection pattern symbols. FL: an argument pattern of a function equation (`\in(Xi, p)` in the premise): as L, into the clause's `pre`.

| # | Shape | Reading | Device | Cone |
|---|---|---|---|---|
| L-1 | `p #Or q` | one rule per disjunct, same priority, requires, right side, ensures (TRIAGE-A `ml-or`); each disjunct must bind what the rest uses | split | none |
| L-2 | `#Top` | an anonymous variable | fresh variable | none |
| L-3 | `#Exists Y. p` | `Y` is a variable of the rule (`(∃y.φ) → •ψ` is `∀y.(φ → •ψ)`, `y` not in ψ) | variable | none |
| L-4 | `#Bottom` | the left side is empty: the sentence is a logical truth, `inert vacuousLeft` | none | none |
| L-5 | `p #And P`, P a predicate | `P` into `pre` | `Cond` | `Rule.pre` |
| L-6 | `p #And q`, both patterns | `p #as Z`, `pre := exMatch ȳ q Z top`, ȳ the variables only `q` holds. A variable of `q` used elsewhere and not bound by `p`: the unbound-variable construct, not this design's | `Cond` | `Rule.pre` |
| L-7 | `#Not(p)` | fresh `Z` at the position, `pre := not (exMatch ȳ p Z top)` | `Cond` | `Rule.pre` |
| L-8 | `p #Implies q` | `#Not(p) #Or q`: L-7 and L-1 | | |
| L-9 | a predicate at a term's sort (`#Ceil(t)` as an argument) | fresh `Z`, the predicate into `pre` | `Cond` | `Rule.pre` |
| L-10 | `#Forall Y. p` with `Y` in `p` | `{z | ∀y. z ∈ p(y)}`: refused `openExtent` | | |
| L-11 | the top of a function equation's left side is not an application | kompile rejects it (three fixtures): R-b | | |

R: a rule's right side. FR: a function equation's right side.

| # | Shape | Reading | Device | Cone |
|---|---|---|---|---|
| R-1, FR-1 | `t #And {B #Equals true}` | `rhs := t`, `ens := B` (an equation's: lane CE's `Clause.ens`) | reader | none |
| R-2, FR-2 | `t #And u`, both terms | `rhs := t`, `ens := t ==K u` (strict `==K` is true exactly where both are defined and equal) | reader | none |
| R-3, FR-3 | `#Bottom` | no step, no value, and the rule or clause still applies there (blocks larger priorities, no fall-through): `ens := false` | reader | none |
| R-4, FR-4 | `t #And P`, P another predicate | `P` into `post` | `Cond` | `Rule.post`, `Clause.post` |
| R-5 | `t #Or u`, `#Top`, `#Exists Y. t`, `#Not(t)`, a predicate at the configuration sort | `lhs → •S`: *some* successor lies in the set `S`. It is `rhs := ?Z` with `post` the membership (`or (mem Z t) (mem Z u)`, `top`, `exMatch`, `not (mem Z t)`): the existential-variable construct | that design | that design's |
| FR-5 | the same shapes in an equation | refused `manyValuedRightSide` (4.3), except where the reader shows one value: `t #Or #Bottom` is `t` | | none |
| R-6 | `#Forall Y. t` | refused `openExtent` | | |

C: a `requires` or `ensures`, written `\equals{SortBool, R}(B, \dv{SortBool}("true"))` with a connective inside `B` at sort Bool.

| # | Shape | Reading | Cone |
|---|---|---|---|
| C-1 | `B₁ #And B₂` | `B₁ andBool B₂`: the conjunction is `true` exactly where both evaluate to `true` | none |
| C-2 | a predicate as `B` (`requires #Ceil(f(X))` typed at Bool) | the predicate at sort Bool is every Bool or none, and neither is `{true}` since `true` and `false` are apart: the condition never holds. `req := false` literal | none |
| C-3 | `B₁ #Or B₂` | `{B₁} ∪ {B₂} = {true}`: `and (or (ceil B₁) (ceil B₂)) (and (implies (ceil B₁) (isTrue B₁)) (implies (ceil B₂) (isTrue B₂)))`, `isTrue B` being `mem Bool B true` | `pre`/`post` |
| C-4 | `#Not(B)`, `#Top` as `B` | the set holds every Bool element but one, or all: whether it is `{true}` depends on Bool's elements. Refused `openExtent` | |

P: the arguments of a predicate. Terms: the `Cond` form directly, and Γ's pattern is the written one. An argument with a connective is first rewritten by the laws `⌈φ ∨ ψ⌉ = ⌈φ⌉ ∨ ⌈ψ⌉`, `⌈φ ∧ P⌉ = ⌈φ⌉ ∧ P`, `⌈t ∧ u⌉ = t ∈ u`, `⌊P⌋ = ⌈P⌉ = P` for a predicate `P`, `∃y. y ∈ t ∧ B(y)` = `⌈t⌉ ∧ B(t)`; what remains with an unguarded quantifier, a complement or `⌊t⌋` is `openExtent`.
`\forall` and `\floor` (TRIAGE-C `forall-floor`) are the KORE forms of `#Forall` and `#Floor` and get these rows.

### 4.5 Set variables and `@S`

A free set variable in an axiom ranges over every subset of its sort. Instantiating it by a singleton is valid, so the sentence with an element variable in its place is always a consequence of the written one (direction W1). The two are equivalent when each `@S` occurs once on each side in positions application distributes over: `f(@S) => @S` says `f(x) = x` for every `x`, and no more (the image of a union is the union of images).
Reading SV-1 (decided). A set variable occurring once per side, under applications only, is read as an element variable with `ReadingNote.setVarAsElement`; reader only, tie by the two entailments on the fixture.
A non-linear occurrence (`g(@S, @S) => @S` also says `g(a, b) ∈ {a, b}` for `a ≠ b`) or one under a predicate or a negation says more than any clause states: refused `setVariable`, R-c on `Eval` (a constraint on a function that is no equation at a point).
The argument-abstracted form: if kompile writes a function rule with `@S` as it writes every function rule, `\implies(\in(X0, @S) ∧ …, \equals(f(X0), @S))`, the sentence says `f(x₀) = S` for **every** set `S` holding `x₀`: `{x₀}` and `{x₀, y}` at once. Over a sort with two elements it has no model. Then it is refused `setVariable` as a contradiction of the text, recorded upstream, and SV-1 applies to no kompiled text. Which form kompile writes is fixture `e3-setvar-read`'s to show (TRIAGE-A undecided 2).
Reverse SV-1 when C14's entailment from the element-variable equation to the written sentence fails on that fixture.

### 4.6 Headline statements

All five keep their text. `Step`, `NotApplies`, `RuleApplies` and `StepDecided` change underneath; `StepDecided` is a hypothesis of `complete_at`, and its added conjuncts hold by `Holds.top` for every rule with `pre = post = .top`, so nothing provable today is lost. Proof changes:
- `sound_at`: one lemma, by induction on `Holds`: at a substitution of values, Γ entails `Cond.kore p` when the result is `true` and its negation when `false`. The `ceil`, `equals`, `mem` cases are the existing evaluation soundness; `exMatch`'s `false` case is the argument `NotApplies` already has (no match of a value by a pattern, at any elements).
- `complete_at`: the same lemma in the other direction inside `step_complete_at`'s case analysis of the closure disjunct.
- `stepDecided_of_fnHyp`: every condition has a result when its terms do (induction on `Cond`; `exSome`'s `g` by classical choice).
- `consistent_of`: the value model satisfies a rule axiom with a condition because `Holds` is the condition's truth in that model (same lemma, read in the value model).
- the executor behind `run_exact` must decide `Holds`: quantifier-free forms by evaluation, `exMatch` by the existing matcher's enumeration.
- unit e3 only: every mutual induction over `Eval`'s block gains the `Holds` cases (`EvalFunctional`, `EvalSound`, `EvalComplete`, `FnSolves`, the call-rank certificate, which must count the calls inside a condition's terms). This is why e3 may be XL.

### 4.7 Tie and FD-C

- A `Cond` form whose arguments are terms prints as the written connective: rows 1 to 5 of TIE-0's table keep their directions (W1 and W2 for a rule; E for an equation), by equality of patterns where they have it today.
- A reader device (split, fresh variable, `ens := t ==K u`, `req := false`, the C-3 comprehension, SV-1): each is a `ReadingNote`, tied in direction E by a per-fixture proof from matching-logic laws, not by equality. This is C6 work with a guard per note; the notes are `orSplit`, `topAsVariable`, `existsAsVariable`, `andAsEnsures`, `bottomAsEnsures`, `notAsCondition`, `predicateAtBool`, `orAtBool`, `setVarAsElement`.
- M: nothing new; `Cond` adds no family to Γ.
- FD-C: not concerned.

## 5. Units

Order: S, c1, e0 and e1 can start at once and touch disjoint declarations. e2 before d1 (both edit `Step`'s neighbours; d1 is the larger rebase). c3, d4, e3 last, each behind a decision.
Every expectation below is derived from the text or the prose named, never from a run.

### Brief 1 (sub-case S; group (c))

| Unit | Content | Cost |
|---|---|---|
| S | 1.2; fixture `e5-hooked-int` (`syntax MyInt [hook(INT.Int)]`, `syntax MyInt ::= MyInt "+My" MyInt [function, hook(INT.add)]`, a rule `<k> go => 2 +My 3 </k>`) | S |
| c1 | 2.2, 2.3, 2.5: registry numbers, `CollKind.rangeMap`, `rangesOK`, `sortOf`, `builtinColls`, the 15 hooks, the silent keys, the model facts; headline proofs restored | M to L |
| c2 | reader: `Builtins.lean` module `RANGEMAP` (the constructor, the three parameters), hook names, `rangeMapPattern`; fixture `e6-rangemap` | M |

Expectations.
- S: `2 +My 3` is `\dv{SortMyInt{}}("5")` (INT.add's prose; the result sort from the declaration). `\dv{SortMyInt{}}("5")` and `\dv{SortInt{}}("5")` are apart: no sentence equates them.
- `e6-rangemap`, with `M := ([0,3) r|-> a) ([5,7) r|-> b)`:
  `size(M) = 2` (657); `M[1] = a` and `M[3] orDefault c = c` (498-499: inclusive below, exclusive above); `2 in_keys(M) = true`, `3 in_keys(M) = false`;
  `size(([0,3) r|-> a) ([3,5) r|-> a)) = 1` and `find_range(that, 4) = [0,5)` (499-500: merged);
  `([0,3) r|-> a) ([2,5) r|-> b)` has no value (600-602): Γ entails `¬⌈…⌉`;
  `([0,10) r|-> a)[[3,5) <- b]` has size 3 and the values `a`, `b`, `a` at 2, 3, 5 (564-566); `([0,10) r|-> a)[[3,5) <- undef]` has size 2 (574-576);
  `([0,10) r|-> a) -RangeMap ([3,5) r|-> a)` is `([0,3) r|-> a) ([5,10) r|-> a)`, and with `b` in the second map it is the first map (584-588);
  `param_undetermined` at: `M[9]` (RM-3), `[x, y) r|-> v` for non-Int `x` (476-477), `[3,3) r|-> v`, `M <=RangeMap M`, `choice(M)`.
- mutation the fixtures must kill: `rangesOK` without the merge conjunct (then `size` of the merged map is 2).

### Brief 2 (group (e), first part)

| Unit | Content | Cost |
|---|---|---|
| e0 | K texts only, each kompiled, with `account.txt` and no theorem: one per row of 4.4 outside `[simplification]` (`e3-ml-rule-lhs-{or,not,and,top,exists,ceil}`, `e3-ml-rule-rhs-{and-pred,and-term,bottom,or,top}`, `e3-ml-eq-rhs-{and-pred,bottom,or}`, `e3-ml-eq-arg-not`, `e3-ml-req-{and,or,ceil,not}`, `e3-setvar-read` and its non-linear twin) | S |
| e1 | reader: the rows of 4.4 with "Cone: none", each with its `ReadingNote`; `openExtent`, `manyValuedRightSide`, `setVariable` as named refusals in place of `patternConnective` | M |
| e2 | `Cond`, `Rule.pre`, `Rule.post`, `Holds`, `Step`'s four definitions, `applies`, `prioRuleK`, 4.6 for rules, the executor | L |

Expectations, each from the `tr s` of the sentence named in the fixture and the fixture's no-confusion axioms.
- `e7-guardors` (`rule <k> c(a() #Or b()) => a() ... </k>`): `c(a)` and `c(b)` each have the successor `a`; `c(c(a))` has none by this rule.
- `e3-ml-rule-lhs-not` (`Exp ::= a | b | c(Exp)`, `rule <k> c(#Not(a())) => a() ... </k>`): `c(b) → a` and `c(c(a)) → a` (`b` and `c(a)` are not `a` by the distinctness sentences); `c(a)` has no successor.
- `e3-ml-rule-rhs-and-term` (`rule <k> go(X) => f(X) #And g(X) ... </k>`, `f`, `g` functions): a step exactly where `f(X)` and `g(X)` are defined and equal, to that value.
- `e3-ml-rule-rhs-bottom` beside a rule of priority 60 with the same left side: no step at all (the first applies and has an empty right side; the second is blocked by it). Mutation: `bottomAsEnsures` read as a `requires` gives the second rule's step.
- `e3-ml-rule-lhs-ceil` (`rule <k> go(X) #And #Ceil(1 /Int X) => done ... </k>`): `go(0)` has no successor, `go(2)` has `done`.
- `e3-ml-req-ceil`: the rule never applies (C-2); a rule of larger priority beside it does.
- refusals: `e3-ml-eq-rhs-or` prints `manyValuedRightSide`; a fixture with `#Forall Y:Int. …` prints `openExtent`.

### Brief 3 (group (d))

| Unit | Content | Cost |
|---|---|---|
| d1 | 3.2: `ParamSig.raw`, `lookupOpen`, `keepsRaw`, `sortOf`, `paramVal`, `gens`, `consItemsK`, `enumerable`; the `withHooks` lemmas; the model; headline proofs restored | XL (split by file if the brief allows: Value/Evaluation, then Faithful/Model) |
| d2 | reader: open generators, `openLaw`, the no-junk match, `openGeneratorPattern`, the cut; fixtures `e2-comm-ctor` (re-accounted) and `e2-open-rule` | M |
| d3 | `OpenTotal`, `OpenAssoc`, `assocH`, the tie statements of 3.6 on `e2-comm-ctor`, the witnesses below | M |

Expectations (`e2-open-rule`: `Exp ::= "x" | "y" | Exp "&" Exp [comm]`, `syntax Bool ::= same(Exp, Exp) [function]`, `rule same(A, B) => A ==K B`, `rule <k> go => x & y </k>`).
- for every H with `OpenTotal`: `go` has exactly one successor, the configuration holding `paramVal and [x, y]`.
- undetermined: over all H, Γ entails neither `same(x & y, y & x) = true` nor `= false`. Two witnesses: `HookParams.none` (the two raw applications are distinct values) and the H with `app and [y, x] = some (.ctor and [x, y])`. From the text: sentences 151 and 182 and the absence of any no-confusion axiom naming `and` admit both.
- `e2-comm-ctor` at `none`: `OpenAssoc … or` fails (`or(or(x,x),x)` and `or(x,or(x,x))` are distinct raw values), and at `assocH or` sentence 172 holds at values. The first is the mutation test of the guard.
- today's reading is shown to assert more: with `and`, `or` as clause-less functions, `Γ ⊧ ∀ v : Exp, v = x` (TRIAGE-B's "to run"); with d1, it is not entailed at `none`.

### Behind a decision

| Unit | Needs | Cost |
|---|---|---|
| e3 | e0 showing kompile accepts a predicate in a function equation outside `[simplification]` (FL-5 to FL-9, FR-4) | L to XL |
| c3 | the orchestrator wanting range-map patterns that bind variables; 2.4's open question settled on paper first | L |
| d4 | a "closed sort" lemma; an open generator binding a variable in a left side | L |
| closure axioms for Bool and Int | TIE-0 TR-2's reversal; then `Cond.ex`, `Cond.all` | M each |

## 6. Findings

1. `Faithful.lean`, `ΓDomains` and TIE-0 F1. Claim: an unguarded quantifier or complement over a sort with domain values has no determined truth in the models of the text or of Γ, so it cannot be supported with `sound_at` and `complete_at` as stated. Evidence: graphs "on ground values" only; the text's no-junk for such a sort is `\or(\top, \bottom)`. Sure: shown for Γ, suspected for "no `Step` can be both" (argued in 4.3). Settles it: the counter-model of TIE-0 section 5 extended with one rule under `#Forall Y:Int`.
2. `Value.lean:224` (`sortOf`) under 3.2. Claim: making a raw open application a value forces `sortOf` to read `c.hooks`, which breaks the invariant "no decided condition reads this field" (`Core.lean`, comment on `hooks`). Sure: shown that the alternatives fail (3.1; a carrier of all free terms makes the `_==K_` graph contradict H's graph). Settles it: counting the `*_withHooks` lemmas that are `rfl` today.
3. 3.3. Claim: with the `assoc` axiom in Γ, `sound_hyp` is false at a non-associative H; without it, `HookParams.none` is not a model of the text for a definition with an `assoc` generator. Sure: shown by the definitions. Settles it: the owner's choice between OG-1 and its reversal.
4. 2.4. Claim: `mapElemAtomAx` and `mapDecompAx` are false of range maps, so `ΓColls` cannot reuse the map family. Evidence: `[0,10) r|-> v = ([0,3) r|-> v) ([3,10) r|-> v)` by lines 499-500. Sure: shown.
5. 4.5. Claim: a function rule over `@S` in kompile's argument-abstracted form has no model over a sort with two elements. Sure: suspected (the form is not in the tree). Settles it: fixture `e3-setvar-read`.
6. 4.4 C-2. Claim: a predicate written as a `requires` makes the rule never apply, as the text is written. Sure: suspected (needs the fixture's text to confirm the `\equals(…, true)` wrapper). Settles it: `e3-ml-req-ceil`.
7. 2.5. Claim: adding RANGEMAP's sorts and symbols to the registry renumbers every package's own sorts and symbols. Evidence: `nRegSorts := 21 + BuiltinNames.nNewSorts`, no RangeMap name in `FixedSignature`, `BuiltinNames`, `Builtins`, `BuiltinData`, `Parse` at `1e306534` (grep, 0 hits). Sure: shown.
8. TRIAGE-C's alternative for RANGEMAP ("declarations unread until a read sentence applies one") is not needed once c1 lands and is not taken: it would leave the row's status depending on use.

## 7. Not read, and what rests on it

- Lean proofs: none. `FaithfulColl*.lean`, `Model*.lean`, `CollExec*.lean`, `Exec.lean`, `Parse.lean` (cited through the triage files only), `FaithfulNeg.lean`, `OvlLaws.lean`. Every cost estimate and every "the proof gains a case" rests on declaration headers and the files' comments.
- The all-builtins `definition.kore`: RANGEMAP's declarations are taken from TRIAGE-C's quotation; whether kompile writes associativity and unit axioms for `_RangeMap_` is expected, not seen.
- No kompiled text holds a connective outside `[simplification]` except `e7-guardors`, none holds `@S` there, and none holds a user sort hooked to `INT.Int`. Section 4.4, 4.5 and 1.1 are conditional on unit e0's and S's fixtures.
- Lane CE's `Clause.ens` is not in `1e306534` (`Clause` has no such field there); rows FR-1 to FR-3 assume it as the brief describes it.
- The existential-variable (`?X`) and unbound-variable designs, which rows R-5 and L-6 hand to.
- `kore.k`: whether it declares an `assoc` or `comm` constructor production (3.3's note).
