# FD-K: the simulation statement for KORE in K

Fable design agent, 2026-11-14. Read-only; nothing was built or run (no lean, lake, kompile, krust).
Lean read at `<worktree:kcore-merge>/.../KcoreSpec` (`Step.lean`, `Evaluation.lean`, `Core.lean`, statements of `CollExecFinal.lean`); `kore.k` and its README at k-rust main; F3, SYNTH §2, KK-0, CS-0 §2.4/§4/§5, KT-1's last section, RE-0 §1 and §2.1-2.2.
Names followed outside the set, one declaration each: `sortOf`, `injNormal`, `GroundTerm.cmp` (`Value.lean`), `CoherentAll`, `Coherent`, `Eval.functional` (`EvalFunctional.lean`), `FnHyp` (`Statements.lean`), `Terminates` (`Terminates.lean`), `execReady`, `outOfFuel` (`CollExec.lean`), `silentTable` (`Hooks.lean:483`), `Config` (`Value.lean:324`).
"Shown" = by reading the quoted text. "Suspected" = follows from text read, depends on something not read or not run.

## 0. Decisions taken here

| # | Decision | Reason | Reverse when |
|---|---|---|---|
| K-1 | **Pointwise-definedness form**, not the fuel variant. | (a) A fuel argument does not remove the hypothesis from completeness: "has a result" becomes "the result at `n` is not out-of-fuel", the shape of `step_iff_at`'s `hf`. (b) What fuel buys is `FnHyp kk`, hence `sound_hyp` at `d := kk`, which the owner does not require. (c) It costs a third outcome threaded through about 25 functions of `kore.k` and every place that tests `bot` (finding 9). (d) The proof device the pointwise form needs is small and generic (§1.5). | The stage-4 spike measures the inversion of one clause of `eval` from `kk`'s literal above the cap or above about 60 lines per clause (then: fuel in a Lean mirror only, §1.5 device B, still no `kore.k` change); or `sound_hyp` at `kk` enters the goal (then fuel in `kore.k`). |
| K-2 | `succs_complete` is **not proved forward**. It is `succs_sound`'s characterization + `hdef` + `Eval.functional` on `d`. No `kk` derivation is ever built for the evaluation functions. | §1.4. Halves stage 6. | A forward statement is wanted (`succs_defined`, §1.6); it is a separate theorem with a ranked-termination hypothesis. |
| K-3 | `enc` re-sorts collection elements by `kore.k`'s `cmp`; `kore.k`'s order is not aligned to `GroundTerm.cmp`. | The two orders differ (finding 5); aligning means registry sort numbers and Lean's string order inside `kore.k`. The statements use `∈ L`, never an order of successors. | The sorting lemmas of stage 3 exceed about 300 lines. |
| K-4 | `CoherentAll kk.sem` is **discharged** (a theorem `KK.coherent`), not a hypothesis. | All 10 open pairs exclude each other by their `requires` (§2.2). It is used for uniqueness of every helper's result. | One pair is found not exclusive: then that is a defect of `kore.k`, fixed in `kore.k`. |
| K-5 | Termination of `kore.k`'s functions is never a hypothesis and never proved as `Terminates`. 11 of the 12 facts are false as stated (§2.1). | Each needed instance comes from a Lean function's own termination proof, on the arguments `encDef` produces. | — |
| K-6 | Lean mirrors of `kore.k`'s sorts (`KK.T`, …) with `emb` into `GroundTerm`, helper functions over the mirrors: the shape CS-0 §2.2/§2.4 gives k2lean. | One spike serves both rows. | CS-2 unit 3 changes the lemma shape. |

## 1. The statements

Nothing below is compiled. `d : Semantics` is the object definition, `K := kk.sem` the reader's result on the pinned `definition.kore` of `kore.k` (KT-1: 970,929 bytes, K 7.1.337, `kore.k` SHA-256 `6b064ca7…a69f`; the pin moves once, after §4's fixes).

### 1.1 Mirrors and embeddings (stage 3)

```lean
namespace KCore.KK
inductive Kind | map | set | list
inductive T            -- sort Term of kore.k, one constructor per production
  | ap (f : Int) (as : List T) | iv (i : Int) | bv (b : Bool) | tk (s : Int) (x : String)
  | ij (a b : Int) (t : T) | vr (i : Int) | as (p : T) (i : Int) | hk (o : Int) (as : List T)
  | bot | cb (k : Kind) (c : Int) (ps : List T) | co (k : Kind) (c : Int) (es : List T)
  | en (t e : T) | kv (a v : T) | el (x : T)
structure Cl where prio : Int; owise : Bool; pats : List T; req : T; rhs : T
structure Rl where prio : Int; owise : Bool; lhs : T; req : T; rhs : T
structure D  where subs : List (Int × Int); fns : List (Int × List Cl); rules : List Rl
inductive St | stuck | next (ss : List T)

def emb   : T → GroundTerm     -- the K value: `.ctor sym.ap [.dv Srt.int (.int f), embTs as]`, …
def embD  : D → GroundTerm
def embSt : St → GroundTerm
theorem emb_sorted   (t : T)  : K.sortOf (emb t)   = some srt.Term   -- every mirror value is a value of kk
theorem embD_sorted  (E : D)  : K.sortOf (embD E)  = some srt.Def
theorem emb_injective : Function.Injective emb
```
`emb_sorted` is needed by every forward lemma: `Eval.clause` asks `K.WellSorted cl.vars σ`.

### 1.2 `enc` and `encDef`

```lean
/-- A value of d as a kore.k value. Symbols and sorts keep KCore's numbers. -/
def enc : GroundTerm → T
  | .ctor f vs            => .ap f (vs.map enc)
  | .inj a b v            => .ij a b (enc v)
  | .dv 3 (.int i)        => .iv i            -- Srt.int
  | .dv 2 (.bool b)       => .bv b            -- Srt.bool
  | .dv s (.tok x)        => .tk s x
  | .dv _ _               => .bot             -- outside the fragment; excluded by encDef (enc_ne_bot)
  | .map s es             => .co .map s (sortK ((es.map fun (k, v) => .kv (enc k) (enc v))))
  | .set s es             => .co .set s (sortK (es.map fun x => .el (enc x)))
  | .list s es            => .co .list s (es.map fun x => .el (enc x))
-- sortK: insertion by `ckeyF` (the mirror of kore.k's ckey/cmp)

def encR : Option GroundTerm → T | some v => enc v | none => .bot      -- object-undefined is `bot`

def encTerm (d : Semantics) : Term → Option T     -- rule and clause terms
def encDef  (d : Semantics) : Option D
```

`encDef d = some E` holds exactly when every condition below holds; each is a `Bool` computed from `d`, so `hE` is closed by `rfl`/`decide` per definition. `E.subs = d.subsorts`, `E.fns` from `d.allFns` (the sort predicates are ordinary entries), `E.rules` from `d.rules`.

| | Condition (`none` otherwise) | Why |
|---|---|---|
| C1 | `d.ovls = []` | `PatVal.ovl`, `EvalTerm.ovl` have no counterpart in `kore.k`. |
| C2 | every `p ∈ d.params` has `impl = some g` with `g` a unit/element/concatenation symbol of the library's `Map`/`Set`/`List` and `p.sig.result` a collection sort of that kind | `paramVal` with `impl = none` reads `d.hooks`, a Lean function. With C2 and C6 no premise reads `d.hooks`, so the theorems hold for every `d.withHooks H`. |
| C3 | each `.app f ts`: a constructor (`isCtor`) → `ap`; a function of `allFns` → `ap`; `isHook f` with `opOf f = some o` (27 codes, `kore.k:412-415`) → `hk o`; a collection symbol (library or C2) → `cb` with nested concatenations flattened, units dropped, elements as `kv`/`el`; anything else → `none` | the four readings `kore.k` has |
| C4 | no symbol is both a constructor and a label of `allFns`; no hook code's symbol is either | `kore.k` decides constructor/function by `lookup(F, Fns)` (`apply-ctor`) |
| C5 | literals: `(Srt.int, .int)`, `(Srt.bool, .bool)`, `(s, .tok)`; no sort of a constructor or function signature admits another literal (Float, MInt, …) | `iv`, `bv` drop the sort |
| C6 | `silentKey f = false` for each of the 27 hook symbols | at a silent point `hookRes` is `d.hooks`' value, `kore.k` gives `bot`. Holds today: `silentTable = []` (`Hooks.lean:483`, kcore-merge). Recheck at the pin (main's log says silent points are not settled). |
| C7 | `d.subsorts` is irreflexive and transitive | `sortOf (.inj a b t)` reads `d.subsorts.contains (a, b)`; `kore.k`'s `leq` computes the closure and terminates only on an acyclic list (finding 2) |
| C8 | a Map or Set pattern has at most one part that is not an element; `encTerm` writes elements first; no `.as` directly over an element part (finding 7) | `kore.k:265-268` |
| C9 | every priority `< 1000000` (dropped if unit B of §4 removes the sentinel) | finding 4 |
| C10 | `.as` only in left sides; no variable of a right side or `requires` unbound by the left side (`execReady`'s `binds` gives it; listed so the proof may cite it) | `eval` has no equation for `vr`, `as` |
| C11 | after RE-0's E1: `r.ens = some e` → right side `en(rhs, e)`; before it `Rule` has no such field and `encDef` never writes `en` | `ev-en` |

```lean
theorem enc_injective (hE : encDef d = some E) {v w s s'} (hv : d.sortOf v = some s) (hw : d.sortOf w = some s') :
    enc v = enc w → v = w
theorem enc_ne_bot (hE : encDef d = some E) {v s} (hv : d.sortOf v = some s) : NoBot (enc v)   -- `bot` nowhere inside
theorem enc_canonical (hE …) (hv …) : Canon (enc v)     -- every `co` sorted by ckeyF, no key twice, no `ij` under `ij`
```
`enc_injective` is injectivity on sorted values only: `kore.k`'s `iv`/`bv` carry no sort.

### 1.3 `enc_config`

The three `succs` statements need **no** `Config kk.sem`: `Eval K f vs r` takes raw values, and only `emb_sorted`/`embD_sorted` are used. `enc_config` is needed by the `RunsTo` corollary alone (stage 7b), over the `step(D, T)` entry of §4 unit C:

```lean
def cfg (s : GroundTerm) : GroundTerm      -- <generatedTop>(<k>(kseq(inj{State,KItem}(s), dotk)), <generatedCounter>(0))
theorem enc_config (hE : encDef d = some E) (x : Config d) :
    K.sortOf (cfg (.ctor sym.step [embD E, emb (enc x.val)])) = some topCellSort
theorem one_config (y : Config d) : K.sortOf (cfg (.ctor sym.one [emb (enc y.val)])) = some topCellSort
```
Both follow from `emb_sorted` and `kk`'s signature by `decide`-size reasoning; no property of `d` is used.

### 1.4 The three statements, and what else falls out

```lean
variable {d : Semantics} {E : D}
local notation "succsAt" x => Eval K sym.succs [embD E, emb (enc x)]

theorem succs_sound (hr : CExec.execReady d = true) (hE : encDef d = some E) (x : Config d)
    {L : List T} (h : succsAt x.val (some (embSt (.next L)))) {y' : T} (hy : y' ∈ L) :
    ∃ y : Config d, enc y.val = y' ∧ Step d x y

theorem succs_stuck (hr : CExec.execReady d = true) (hE : encDef d = some E) (x : Config d)
    (h : succsAt x.val (some (embSt .stuck))) : ∀ r ∈ d.rules, NotApplies d r x.val

theorem succs_complete (hr : CExec.execReady d = true) (hco : CoherentAll d) (hE : encDef d = some E)
    {x y : Config d} {s : GroundTerm}
    (hdef : succsAt x.val (some s))                      -- pointwise: kk's call at x has a value
    (hst : Step d x y) : ∃ L, s = embSt (.next L) ∧ enc y.val ∈ L
```

Hypotheses, complete list:
- `hr`: `sortedOK` (patterns and right sides are sorted, so the bindings `kore.k` finds without variable sorts are `WellSorted`), `srReady` (results of calls are sorted, for nested matches and for `y : Config d`), `binds`.
- `hE`: §1.2.
- `hco`, completeness only: the `true` that `kore.k` computed for a `requires`, and the right side's value, must be the ones `Step` holds derivations for.
- `hdef`, completeness only: one call of `kk`'s evaluation, `succs` at `(E, enc x)`, has a value. Nothing is assumed of any other call, of any other `x`, or of `kk`'s functions in general.
- Named facts of `kk` assumed: **none** in the final form. `KK.coherent : CoherentAll K` is a theorem (K-4); until stage 4a closes it, it appears as `(hkk : CoherentAll K)` in all three.
- Not assumed: `wf d`, `FnHyp d`, `FnHyp kk`, `CoherentAll d` for soundness, any termination.

All three are corollaries of one characterization (stage 7), which also gives the rest of the observable:

```lean
theorem succs_char (hr) (hE) (x : Config d) {r} (h : succsAt x.val r) :
    (r = some (embSt .stuck) ∧ ∀ ru ∈ d.rules, NotApplies d ru x.val) ∨
    (∃ p L, r = some (embSt (.next L)) ∧
       (∃ ru ∈ d.rules, ru.prio = p ∧ AppliesAt d ru x.val) ∧                 -- some rule of priority p applies
       (∀ ru ∈ d.rules, ru.prio < p → NotApplies d ru x.val) ∧
       (∀ y', y' ∈ L ↔ ∃ ru ∈ d.rules, ru.prio = p ∧ ∃ σ o, FiresK d ru σ x.val o ∧ o = some (dec y')))
-- AppliesAt d ru x := ∃ σ, d.WellSorted ru.vars σ ∧ PatVal d σ ru.lhs x ∧ ∀ t, ru.req = some t → EvalTerm d σ t (some (bool true))
-- FiresK: σ is one of kore.k's listed matches, its requires and its right side each have the EvalTerm result kore.k computed

theorem succs_value        : succsAt x.val r → ∃ st, r = some (embSt st)        -- never kk-undefined on an encoding
theorem succs_stuck_iff  (hco) (hdef : succsAt x.val (some s)) : s = embSt .stuck ↔ ∀ ru ∈ d.rules, NotApplies d ru x.val
theorem succs_applies_no_result (hco) (h : succsAt x.val (some (embSt (.next [])))) :
    (∃ ru ∈ d.rules, AppliesAt d ru x.val) ∧ ∀ y, ¬ Step d x y                   -- the set U
theorem succs_unique : succsAt x.val r → succsAt x.val r' → r = r'               -- Eval.functional KK.coherent
```

Why completeness needs no forward proof (K-2). Take `hdef` and `hst = Step.rule ru σ …`. `succs_char` on `hdef`: if `stuck`, `NotApplies d ru x` gives an `EvalTerm` of `ru.req` to a value other than `true`, `hreq` gives `true`, `EvalTerm` is functional under `hco`: contradiction. If `next L` at priority `p`: the rule witnessing `p` applies, so by `hprio` and functionality `p ≥ ru.prio`; `kore.k` listed a match agreeing with σ on the left side's variables (match completeness, stage 5), computed a value for `ru.req` there which by functionality is `true`, so `ru` is a candidate and `p ≤ ru.prio`; its right side's computed value is, by functionality and `heval`, `enc y`; it is not `bot`, so `keep` keeps it.

Three kinds of "no value" that every lemma keeps apart:
1. object-undefined: `EvalTerm d σ t none`; in `kore.k` the value `bot`;
2. kk-undefined: `Eval K f vs none` (no equation of a `kore.k` function applies, e.g. `valOf(none)`, `matchTs` on lists of two lengths, `ckey(kv, el)`); `succs_value` shows it does not occur on encodings;
3. no derivation of `Eval K …` at all (a non-terminating object evaluation, or `leq` on a cyclic list). `hdef` excludes 2 and 3.

What `hdef` asks beyond what `Step d x y` itself asks, after §4's unit B (each is inherent to a function that lists all successors, and each matches `outOfFuel` in `step_iff_at`):
- every rule of the priority of the least applicable rule, at every match: its `requires` has a result, and where `true` its right side (and `ensures`) has one;
- inside a function call: every clause of the least applicable priority listed before the chosen one, at every match before the chosen one: its `requires` has a result.
Before unit B it also asks: the `requires` **and right side** of every rule and clause of every priority (finding 1).

### 1.5 The identity-on-values lemma, and the proof device for `eval`

```lean
theorem eval_value (hE : encDef d = some E) {v s} (hv : d.sortOf v = some s) :
    Eval K sym.eval [embD E, emb (enc v)] (some (emb (enc v)))
theorem eval_value_iff (hE) (hv) {r} :
    Eval K sym.eval [embD E, emb (enc v)] r ↔ r = some (emb (enc v))       -- by Eval.functional KK.coherent
```
By induction on `v`. Uses: C4 (a value's head is not in `E.fns`, so `apply-ctor`), `enc_ne_bot` (`hasBot` false), `sortOf`'s `!t.isInj` (so `mkInj` takes `inj-new`, never `inj-compose`: shown, `Value.lean` `sortOf`), `ev-val` for `co` (`kv`/`el` inside a `co` are not re-evaluated), D1 is not needed. Terminating, so proved forward.

`kore.k` evaluates `inst(Rhs, B)`, a term with values at its variables. The specification of `eval` is therefore over that shape:

```lean
/-- t is encTerm tm with each variable i replaced by enc (σ i). -/
inductive Inst (d : Semantics) (σ : Subst) : Term → T → Prop
theorem inst_Inst (h : encTerm d tm = some p) (hB : B represents σ on varOccs tm) : Inst d σ tm (instF p B)

theorem eval_spec (hr) (hE) {σ tm t r} (hσ : values of σ sorted in d) (ht : Inst d σ tm t)
    (h : Eval K sym.eval [embD E, emb t] r) : ∃ o, r = some (emb (encR o)) ∧ EvalTerm d σ tm o
theorem apply_spec … (h : Eval K sym.apply [embD E, .dv Srt.int (.int f), embTs (vs.map enc)] r) (hf : d.lookupFn f = some fn) :
    ∃ o, r = some (emb (encR o)) ∧ Eval d f vs o
theorem tryCl_none … : Eval K sym.tryCl [embD E, pats, req, rhs, embTs (vs.map enc)] (some resNone) → Fails d vs cl
```

`eval_spec` cannot be proved by induction on anything but the given `kk` derivation (no measure exists). `Eval.rec` on `K` needs motives for arbitrary `kk` terms; the device is one generic lemma, proved once from `Eval.rec`, outside the cone (it changes no definition):

```lean
/-- EvalTerm with `R f vs r` read at each call in place of `Eval c f vs r`; ClauseR, FailsR likewise. -/
inductive EvalTermR (c : Semantics) (R : Sym → List GroundTerm → Option GroundTerm → Prop) : Subst → Term → Option GroundTerm → Prop
def ByClause (c) (R) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop   -- Eval.clause / Eval.undef over EvalTermR c R
theorem Eval.calls_induct {c} {P : Sym → List GroundTerm → Option GroundTerm → Prop}
    (step : ∀ f vs r, ByClause c (fun g ws q => Eval c g ws q ∧ P g ws q) f vs r → P f vs r)
    {f vs r} (h : Eval c f vs r) : P f vs r
```
Then `P` is a case split on `f` over the 13 functions that reach `eval` (`eval`, `evalTs`, `apply`, `applyL`, `result`, `bestCl`, `bestCl2`, `tryCl`, `tryM`, `succs`, `cands`, `fire`, `fireM`) and `True` elsewhere: for a helper the premise `Eval K g ws q` itself is in hand and `g.eval_iff` rewrites `q`. In these 13 functions every clause has priority 50, so `hprio` is vacuous in each inversion.
Not searched: whether the library already has an equivalent principle (`EvalFunctional.lean` uses raw `Eval.rec` with five motives). If it has, use it.

Device B (fallback, K-1's reversal): a Lean function `evalN : Nat → D → T → Option T` mirroring the 13 functions with fuel in Lean only; `evalN n E t = some r → Eval K sym.eval […] (some (emb r))` forward by induction on `n`; the converse from the library's completeness of `CExec.evalT` on `K` (needs `execReady K`, measured true, and `KK.coherent`). The object-level proof is then by induction on `n`. `kore.k` is unchanged either way.

### 1.6 Not in the goal, recorded

`succs_defined`: a condition on `d` under which `hdef` holds at every `x`. `∀ f, Terminates d f` is **not** enough (shown by this definition: `f(X) => 0`; `f(X) => 1 requires f(X) ==Int 5`, both priority 50, the second listed first: `Eval d f [v] (some 0)` by the first clause, `kore.k` evaluates the second's `requires` first and recurses). A ranked termination certificate of `d` (every call in every `requires` and right side decreases) is enough. Size unknown; not needed for `kk_step`.

## 2. The 11 + 1 termination facts and the 10 agreement pairs

### 2.1 Termination (`Terminates K f := ∀ vs sorted, ∃ r, Eval K f vs r`)

| Function(s) | `Terminates K f` | Treatment |
|---|---|---|
| `eval`, `evalTs`, `bestCl2` | **false** by design: the object function may diverge | never stated. `eval_spec` is an implication from a given derivation; `eval_value` is the terminating instance. |
| `leq` | **false** (finding 2): `leq(1, 2, sub(1,3, sub(3,1, .Subs)))` has no derivation | pointwise lemma under C7: `Eval K sym.leq [a, b, embS E.subs] (some (bool (a == b || d.subsorts.contains (a,b))))`; the Lean mirror recurses on a rank that C7 gives. |
| `match`, `matchK`, `matchCol`, `choose`, `rest`, `split`, `splitOn` | **false**, only through `leq` (`m-inj-sub`'s `requires` calls it) | with an acyclic `S` they terminate: the pattern's size decreases along `match → matchCol → choose/split → rest → matchCol`, and within one function the subject list, the list of substitutions or `Post` decreases. KCore's rank does not see it because `mc-split` passes the rebuilt `P ; Ps` and `m-inj-sub` the rebuilt `ij(C, A, T)`. Discharged as a by-product: the Lean mirror `matchF` is accepted by Lean with that lexicographic measure, and `match_eval (hS : Acyclic S) : Eval K sym.match [emb p, emb a, embB B, embS S] (some (embMs (matchF S p a B)))` is built along `matchF.induct`. |
| `join` (decrease) | **true** (suspected): the summed size of the part list decreases in `join-col` (`co(_,_,Fs) ; Ps` to `app(Fs, Ps)`), `join-list`, `join-elem` | discharged by the Lean mirror's termination proof with that measure. |

So: none becomes a hypothesis; none is proved as `Terminates`; `FnHyp K` is false for two independent reasons (`eval`, `leq`), which confirms OD-11's reading.
How we would find out that a "true on encodings" claim is false: its forward lemma cannot be closed for the Lean mirror (stage 4/5), which shows the argument at which it fails. For `leq`'s falsity (cheap experiment, to run): a `kore.pgm` whose `def` has `sub(1, 3, sub(3, 1, .Subs))` and a rule whose left side is `ij(2, 9, vr(0))` against the initial term `ij(1, 9, iv(0))`; `kcore oracle` on `kore.k` reports `outOfFuel` at every fuel, `krust krun` does not return.
A false fact does not make a statement vacuous here, because no statement assumes one. Vacuity enters only through `hdef` (§1.4) and through `encDef d = none`.

### 2.2 Agreement (10 pairs in 4 functions): all must be discharged, all expected true

`Coherent K cl cl'` holds when the two clauses cannot both apply at one argument list. For each pair that is the proof: invert the two `requires`.

| Function | Pairs | Why exclusive | Needs |
|---|---|---|---|
| `cmpI` | 3: `<Int`/`==Int`/`>Int` on the same `X`, `Y` | trichotomy | the three Int hook values |
| `keep` | 1: `Q ==Int P andBool T =/=K bot` / `Q =/=Int P orBool T ==K bot` | one is the negation of the other | `==Int`, `=/=Int`, `==K`, `=/=K`, `andBool`, `orBool` hook values at defined arguments |
| `join` | 3, by my reading: (`join-col`, `join-list`), (`join-col`, `join-elem`): the second part is `co(…)` and `isElem(co(…))` has only the result `false` (invert `isElem`'s three clauses); (`join-list`, `join-elem`): `K = list` against `K =/=K list` | not examined by KT-1 | inversion of `isElem`; `=/=K` on `Kind` |
| `matchCol` | 3, by my reading `mc-choose` against `mc-head` (`K =/=K list` with `K = list`), against `mc-frame` and against `mc-split` (`isElem(P)` with `notBool isElem(P)`) | not examined by KT-1; which 3 the decider left open is not in KT-1 | same |

Sure: `cmpI`, `keep` shown (KT-1 agrees); `join`, `matchCol` shown for the pairs I list, suspected that these are the decider's 3 + 3.
Settles it: `kcore fn-facts` printed with the clause indices of each open pair; then `KK.coherent` from `coherentAll_of_parts`' parts with the four `ClausesAgree K fn` by hand (stage 4a, about 150-250 lines).
A false pair would mean two equations of `kore.k` give two results at one argument: `succs_unique` fails and the helper `_iff` lemmas with it. It would be found at stage 4a, as an unprovable `Coherent` with the argument list in hand.
`CoherentAll d` for the object definition stays a hypothesis of completeness, as in `step_iff_at`.

## 3. Stage plan from here

Stage 0 and 1 are done (KT-1) except two items carried below. Sizes are lines of Lean unless said.

| # | Work | Done when | Size | Needs |
|---|---|---|---|---|
| 0b | `kcore fn-facts` on `kore.k` with clause indices of the 10 pairs; C6 checked at the pin (`silentKey` of the 27 hook symbols); `leq` experiment of §2.1 | the three recorded in KT-1 | S, no proof | — |
| 2 | `kore.k` units A, B (§4); re-kompile; the pin of `kk` moves here and not again | zero differences from the `kcore` oracle on cases inside the fragment; K7's case has a result; kill matrix recorded | about 80 changed lines of K, 4-5 cases | OD-11, oracle (done) |
| 2c | unit C (observable step, U in `done`) | per-step comparison passes | about 30 lines of K, `check.py` | 2; not on the path to the three statements |
| 3 | `KK/Mirror.lean`, `KK/Enc.lean`: §1.1-1.2; `enc_injective`, `enc_ne_bot`, `enc_canonical`, `emb_sorted`. Native check: for the 44 cases, `CExec` on `K` at `succs [embD E, emb (enc x)]` equals `(CExec.successorsN d n x).map enc` as sets at every reached `x` (this is also stage 0's unrun item, with Lean's `enc` in place of `korek.py`) | lemmas built; the native check agrees or each difference is named | 400-600 | 2 |
| 4s | **Spike** (below) | the four measurements recorded, routes chosen | 300-500 | 3; with CS-2 unit 3 |
| 4a | `KK.coherent` (§2.2) | theorem, no hypothesis | 150-250 | 0b |
| 4 | Helper layer: for each of the about 45 functions that reach neither `eval` nor `match` (`app`, `look`, `lookup`, `inst`, `mkInj`, `cmp`, `insE`, `putE`, `hookOp`, `join`, `keep`, `pick`, …): Lean function, `F.eval`, `F.eval_iff`. Object-level facts in the same stage: `cmpF = 0 ↔ equal` on `Canon` values; `hookOp o (vs.map enc) = encR (d.hookRes f vs).join` per code; `colOf` against `collVal` | every helper has its lemma; the 27 hook lemmas | 2000-3000 by hand, far less if generated | 4s, 4a |
| 5 | `leq` under C7; `matchF` and `match_eval`; `matchF_sound` / `matchF_complete` against `PatVal` (bindings well-sorted from `sortedOK`; complete up to agreement on the pattern's variables). First without `cb` (KK-a), then `matchCol`/`choose`/`split`/`rest` | both directions for every pattern form `encTerm` writes | 300 + 800-1200 | 4 |
| 6 | `Eval.calls_induct`; `eval_value`; `Inst`; `eval_spec`, `apply_spec`, `tryCl_none`, `fire` against `AppliesAt`/`NotApplies` | no `sorry`; `#print axioms` standard | 150-250 (principle) + 500-900 | 4, 5, units A and B |
| 7 | `succs_char`, the three statements, `succs_value`, `succs_stuck_iff`, `succs_applies_no_result` | kernel-checked, hypotheses as §1.4; first KK-a, then with 5's collections | 300-500 | 6 |
| 7b | `kk_step` in KK-0's `RunsTo` form over unit C's rules; `enc_config` | `Step d x y ↔ RunsTo K (cfg (step E (enc x))) (cfg (one (enc y)))`, left to right under `hdef` and `hco` | 150-250 | 7, 2c |
| 8 (optional) | search level (`run`/`visit`/`push` invariant) | as F3 | 400-700 | 7 |
| 9 | KK-self: op codes for `==Bool`, `==String`, `<String` in `kore.k`, then `encDef K = some _` and the instance `d := K`; its `hdef` is "kk run on kk's encoding of x has a value" | the instance elaborates under the cap | small after 7; re-pins `kk` once more, so decide before stage 2 whether the three codes go into unit B's edit | 7 |
| RE | `ensures`: C11 and the `hens` case of `succs_char` | after RE-0's E1 lands in the tree stage 3 is built on | +100-150 | RE-0 E1 |

Changes from F3: stage 6 has one direction (K-2) and a named device; stage 5 carries the termination of the matching group; `CoherentAll kk` is its own small stage; 3k (kernel-checked instances) is dropped as a milestone, since stage 3's native check and the spike cover what it measured.
Total to the three statements without collections: roughly 3000-4500 by hand; collections 1000-1500 more.

**The stage-4 spike's question.** Are the helper lemmas written by hand or emitted by k2lean, and which device inverts the evaluation functions? Four measurements on `kk`'s literal, each with lines, heartbeats and peak memory under the cap:
1. `F.eval` by hand for `app` (structural, two clauses), `lookup` (two `requires` on Int hooks), `mkInj` (one `[owise]`: two `Fails`), and `match` at a pair no clause matches (`m-fail`: twelve `Fails`, each a `PatVals` inversion): the worst helper shape.
2. The same four as text in the generator's cascade form of CS-2 unit 3 (`pred.eval`, `pred.eval_iff`), written by hand as the generator would write it. Does it check, and at what multiple of 1?
3. One clause of `eval` (`ev-inj`) and one of `evalTs` inverted through `Eval.calls_induct` (if the principle is not yet proved, the spike lemma takes it as an explicit hypothesis; no `sorry`).
4. Device B's converse for the same clause through `CExec.evalT` on `K`.
Decision rule: generated if 2 costs at most twice 1 per function and nothing in it needs a tactic the generator cannot emit; device A if 3 is under about 60 lines per clause and under the cap, else B. CS-2 unit 3 (`pred` of `ref-peano`) gives the lemma shape; `kore.k` adds what CS-0 §5 says `ref-` packages lack: recursion (`app`), and a 13-clause function.

## 4. `kore.k` fixes first: Opus briefs (three units, one agent, in this order)

Common to all three. Place: a workspace of `krs/semantics/kore`. Judge: `tools/check.py` against the `kcore` entry of `expected.json` (OD-12), backends as labelled columns. After each unit: `kink-flow run --full` once (about 40 s, 12 GiB scope), `kill-matrix.json` and `kink.lock` regenerated, README's reading and numbers updated. Reasons in comments and commit messages come from K's text and from what `Step`/`Eval` state; a backend's answer is evidence. No Lean change. Stop and report if a case inside the fragment differs from the `kcore` oracle after the change.

**Unit A: a function no equation applies to has no value (D1).**
- `result-none`: `result(_, _, none) => bot`. Header lines 15-17 and README lines 17, 21, 38 reworded: an application no equation applies to is undefined; a `total` function is read the same and such a definition is outside what the cases assert (c42 stays `no-oracle` for totality, per KT-1).
- Mutations: `no-equation-undefined` removed; its converse added (the application stays as a term), expected killer c11.
- Cases: c11 expects N empty, U = `a(3)`; c42 unchanged in result.
- Done: c11 and c42 equal the `kcore` entry; `differences.toml` has no `kcore` line for them.

**Unit B: evaluate by ascending priority; only the chosen right side (F3 finding 12; finding 1, 4 here).**
- Equations: replace `bestCl`/`bestCl2` by a walk over priorities. A function of the clause list alone gives the least priority above `P` (no `eval`). At priority `P`: try the clauses of that priority in list order with `tryCl`; the first `some(T)` is the result; if none applies go to the next priority; no next priority: `none`. `tryM` is unchanged (first substitution whose `requires` holds; its right side only).
- Rules: the same walk in `succs`. At priority `P`: `fire` on the rules of that priority only; if the candidate list is non-empty the step is `next(` its non-`bot` results `)`; else the next priority; none: `stuck`. `minPrio`, `lesser`, `keep`'s priority test and both `1000000` literals go away.
- Reason to write: `Eval.clause` asks, of the other clauses, only that those of a **smaller** priority fail; `Step.rule` asks only that rules of a smaller priority do not apply. An evaluation of anything of a larger priority can only remove results.
- Cases (new): F3's K7 case (`f(0) => 0`, `f(N) => f(N -Int 1) [owise]`, `a(2)`: one final `b(0)`); a rule of priority 50 that applies beside a rule of priority 60 whose `requires` does not terminate (expected by `Step.rule`: the successor of the first; the `kcore` evaluator reports `outOfFuel` here because it evaluates every rule's `requires`, so this case is `no-oracle` with that reason and its expected result is written from `Step.rule` by hand); two rules of one priority, one with an undefined right side (U must not swallow the other's successor); an equation of a larger priority whose `requires` is undefined.
- Mutations: re-anchor those on `best-*`, `pick`, `keep`, `min-*`; add "right side of a larger priority evaluated" only if a terminating case can kill it (it cannot by result; then record it as not expressible, do not add).
- Optional in this unit, decide with the orchestrator before starting: op codes for `==Bool`, `==String`, `<String` (stage 9), so that `kk` is pinned once.
- Done: zero differences from the oracle on cases inside the fragment; the K7 case returns; kill matrix recorded.

**Unit C: the step and U are observable (S36). Not needed by the three statements; needed by 7b and by per-step checking.**
- `syntax Pgm ::= step(Def, Term)`; `State ::= choice(Step) | one(Term) | none1 | stuck1`. Rules: `step(D, T) => choice(succs(D, T))`; `choice(next(S ; _)) => one(S)`; `choice(next(_ ; Ss)) => choice(next(Ss))` (overlapping on purpose: each successor is one run); `choice(stuck) => stuck1`. `choice(next(.Ts))` has no rule: the run ends there, which is U.
- `done(Fs)` becomes `done(Ns, Us)`; `visit-step` with `next(.Ts)` adds the configuration to `Us`; `init-bot` gives `undef`, not `done(.Ts)`.
- `check.py`: N, U and, through `step`, the successors of every reached configuration against the oracle.
- Done: every case passes on N, U and per step.

Any other fix found: none required. `leq` (finding 2) and the `as`-over-element pattern (finding 7) are handled by `encDef` refusing, not by changing `kore.k`.

## 5. Findings

1. **`kore.k:209-216`, `kore.k:115-119` (F3-12, sharpened).** Under KCore's reading of `kore.k` the divergence is certain, not suspected: `EvalTerm.call` needs a derivation for every argument (`hts : EvalTerms …`), so `bestCl2(…, tryCl(…))` has a derivation only if `tryCl` of every clause has one, and `try-holds` evaluates the right side. With `f(N) => f(N -Int 1) [owise]`, `Eval K sym.eval [E, enc (f(0))] r` has no derivation. Consequence for the statements: none is false; `hdef` is false at every `x` that calls such a function, so all three say nothing there. Sure: shown (for `Eval K`; what an engine running `kore.k` does is K7, not known to me). Settles: unit B; K7 for the suite.
2. **`kore.k:314-322`, `leq`/`above`.** `Terminates K leq` is false: on a cyclic `Subs` the call recurs with the same arguments, and `orBool` being a hook both operands need derivations. Through `m-inj-sub` the whole matching group inherits it. Sure: shown by reading; experiment in §2.1 to run. Settles: C7 in `encDef`; no `kore.k` change.
3. **`Value.lean` `sortOf`, `.inj` case, against `kore.k:242-244`.** KCore reads `d.subsorts.contains (a, b)`; `kore.k` reads the reflexive-transitive closure of the encoded list. They agree only if the encoded list is `d.subsorts` and that list is transitive and irreflexive. `Core.lean` says NamesApart proves `declaredClosure` transitive; `subsorts` appends `(X, KItem)` for every sort below KItem, and whether the whole list is transitive I did not read. Sure: suspected. Settles: a lemma `subsorts_trans`, or C7 decided per definition (chosen).
4. **`kore.k:144`, `kore.k:200`: the literal `1000000`.** A clause of priority ≥ 1000000 is never chosen (`best-better` asks `P <Int Best`); with every applicable rule above it `keep` returns `.Ts`, read as "applies, no successor". `Clause.prio`, `Rule.prio` are any `Nat`. Sure: shown. Settles: unit B removes both; else C9.
5. **`kore.k:456-488` against `Value.lean:57-74`.** The two orders differ: `kore.k` has `iv < bv < ap < ij < co < tk`; `GroundTerm.cmp` has `ctor < inj < dv < map < set < list`, and within `dv` by sort number, so Bool (2) before Int (3). An `enc` that maps element lists in place would not produce `kore.k`'s canonical form. Sure: shown. Settles: K-3.
6. **`kore.k:465`, `kore.k:488`: `cmp` is `0` between two different forms of tag 6** (`kv` against `el`, `bot`, `vr`, …). `cmp = 0 ↔ equal` holds on `Canon` values of one kind, not on `T`. The lemma must be stated on `enc`'s image. Sure: shown.
7. **`kore.k:298-301`, `isElem(as(kv(…), X))` is `false`.** An alias directly over an element part is taken as the frame and then fails against `co`; `PatVal.as` over `mapElem` denotes the one-entry map. Sure: suspected (whether the reader ever produces it is not known). Settles: C8 refuses it; a case if it is to be covered.
8. **F3's statement, `Config kk.sem`.** F3 finding 4 (`enc_config` needed) holds for the `RunsTo` form only. The function form takes `GroundTerm`s; what it needs instead is `emb_sorted` for `WellSorted` in every forward lemma. Sure: shown (`Evaluation.lean` `Eval.clause`, `hσ`).
9. **The fuel variant in `kore.k`.** Every test of `bot` (`hasBot`, `mkInj`, `mkEl`, `ensure`, `join`, `keep`, `init-bot`, `fire-refuted`'s `=/=K bv(true)`) would need a third case, and `fire-refuted` in particular would read out-of-fuel as a refuted `requires` unless changed. Sure: shown. This is K-1's cost side.
10. **`∀ f, Terminates d f` does not give `hdef`** (§1.6 example). A reader of the theorem must not paraphrase `hdef` as "the object functions terminate". Sure: shown from `Eval.clause` and `tryM`'s order.
11. **KT-1 stage 0, last bullet.** `kore.k` run by `CExec` on the 44 programs was not run; stage 3's native check replaces it and removes the Python encoder from the comparison.
12. **C6.** `silentTable = []` in kcore-merge; k-rust main's last commit message says silent points are not settled. If `/Int` at 0 or a map lookup off the keys becomes a silent point, `kore.k`'s `bot` there differs from `hookRes` unless `d.hooks` gives nothing. Sure: suspected. Settles: recheck at the pin; if it fails, the three statements take `(hH : ∀ f vs, opOf f ≠ none → d.fallback f vs = none)`.

## 6. Not read

Every proof; `CollExec*.lean` beyond the statements quoted (so the exact name of the completeness theorem device B needs is not known; `evalT_sound` exists in `CollExecSound.lean:235`); `Hooks.lean` beyond line 483 (the 27 hook lemmas are stated from `kore.k`'s side only); `SubjectReduction.lean`; `Tie.lean`'s `ruleSorted`; `tools/korek.py`, so the encoder's symbol numbering and its flattening of collection symbols are taken from the README; the 44 cases; `MUTATIONS.toml`; whether K7 was run; RE-0 beyond §1 and §2.1-2.2; the TICKETS file.
