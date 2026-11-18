/-
  A variable held on a right side under a collection's symbols (CN-4b §2, HO-1), read from
  K 7.1.337 kompile's KORE of the fixtures e3-vars-* (copied to f2-examples as `held*.kompile.kore`;
  e3-vars-list's is `exvarslist.kompile.kore`).
  Run from the package root: `lake env lean -j1 test/HeldFixtures.lean`.

  ## openRefusal
  The reader's `Parse.openRefusal` reads the variables the right side holds under constructors,
  injections and the unit, element and concatenation symbols of a map, list or set collection
  (`heldOccs`), as `rulesPlain`'s conjunct for one rule does (`Semantics.rulePlainHO1`). For each
  text: the reader's verdict, and on its reading before the rules are checked (`Parse.coreBase`)
  each rule's `openRefusal` and `rulePlainHO1`, which agree (`agree true`):
  - e3-vars-map (`<m> .Map => K |-> ?V:Int </m>`), e3-vars-set (`SetItem(?V:Int)`), e3-vars-list
    (`ListItem(?V:Int)`): V is held under the collection's element symbol; read, no refusal.
  - e3-vars-update (`M [ 0 <- ?V:Int ] [ 0 <- 1 ]`): `_[_<-_]` is a hooked function, no collection
    pattern symbol, and the successor does not hold V: refused `openRight` at Int.
  - e3-vars-rangemap (`[0, 1) r|-> ?V:Int`): a range map's symbols hold nothing: refused `openRight`
    at Int.

  ## e3-vars-map (`Map`)
  `rule <k> set(K) => .K ... </k> <m> .Map => K |-> ?V:Int </m>`, the text's one rule (`r0`), V its
  existential variable 3. The text declares no function and no parameter, and has `coreOK`
  (`coreOK`) and `FnHyp` (`fnHyp`). V is under no constructor of the right side and under the map's
  element symbol `_|->_`, which `holds` (`held`: `heldOccs` holds V, `ctorOccs` does not,
  `rulePlainHO1`; Int is not confined). At `x = <k> set(5) </k> <m> .Map </m>` (`X`), the cell holding
  nothing else:
  - `Step` from x to `<k> . </k> <m> 5 |-> i </m>` (`Y i`) for every Int i (`step`), and to nothing
    else (`step_iff`);
  - in every model of `Γc`, x has a successor among the instances of the application
    (`Γc ⊧ den x ⇒ •famEx`) and each `Y i` is one of them (`sound_xy`, the pinned `sound_at`);
  - by `ExactC` (`exact_hyp`), a value is a successor of x in some model of `Γc` with the step's
    closure exactly where it is some `Y i` (`exact_y`): no other value is a successor in any model.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HeldFixtures

/-- The reader's semantics of a text before its rules are checked (`Parse.coreBase`, the stage
after which `Parse.coreOf` refuses a rule), and the names of each rule's variables. -/
def heldBaseOf (k : Kore.Definition) : Except String (Semantics × List (List String)) :=
  match k.modules.getLast? with
  | none => .error "no module"
  | some m =>
    let S := Parse.scan m.sentences
    let r : Parse.Rd (Semantics × List (List String)) := do
      let E ← Parse.envOf m S
      let sp ← (Parse.prodSyms S E).mapM (Parse.symProd E S.eqs)
      let rules ← S.rewrites.mapM (Parse.ruleOf E.N E.src)
      let c ← Parse.coreBase S E (Parse.prodsOf S E sp) rules
      pure (c, rules.map (·.2.names))
    match r with
    | .ok x => .ok x
    | .error f => .error s!"{repr f.reason} {f.detail}"

/-- The reader's verdict on the text, and each rule of its reading before the rules are checked
whose `openRefusal` or `rulePlainHO1` is not that of a plain rule: the two, and whether they agree. -/
def heldVerdict (name path : String) : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => IO.println s!"{name}: KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"{name}: parse refused {repr r.reason} {r.detail}"
    | .ok _ => IO.println s!"{name}: parse read"
    match heldBaseOf k with
    | .error e => IO.println s!"{name}: base {e}"
    | .ok (c, ns) =>
      for (r, names) in c.rules.zip ns do
        if !r.opens.isEmpty then
          let ref := Parse.openRefusal c r names
          let shown := match ref with
            | none => "none"
            | some (why, detail) => s!"{repr why} {detail}"
          IO.println s!"{name}: opens {r.opens} held {c.rulePlainHO1 r} agree {ref.isNone == c.rulePlainHO1 r} refusal {shown}"

def run : IO Unit := do
  heldVerdict "map" "f2-examples/heldmap.kompile.kore"
  heldVerdict "set" "f2-examples/heldset.kompile.kore"
  heldVerdict "list" "f2-examples/exvarslist.kompile.kore"
  heldVerdict "update" "f2-examples/heldupdate.kompile.kore"
  heldVerdict "rangemap" "f2-examples/heldrangemap.kompile.kore"

/--
info: map: parse read
map: opens [3] held true agree true refusal none
set: parse read
set: opens [3] held true agree true refusal none
list: parse read
list: opens [3] held true agree true refusal none
update: parse refused KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
update: opens [3] held false agree true refusal KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
rangemap: parse refused KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
rangemap: opens [3] held false agree true refusal KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
-/
#guard_msgs in
#eval run

section Shared

open ML Faithful

variable {c : Semantics} {σ : Subst}

/-- An application of an interpreted hooked symbol that is no constructor has the result `hookRes`
gives its arguments' results, and none where an argument has none. -/
theorem evalHook_inv_fxv {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = true) (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ (∀ vs, allSome rs = some vs → c.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | hook _ _ hts hh' hund => cases ht; exact ⟨_, hts, hh', hund⟩
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | param _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hh] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | ovl _ ho _ => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | ovlFn _ ho => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | _ => cases ht

/-- A constructor application has the sort of another of the same constructor whose arguments have
the same sorts. -/
theorem sortOf_ctor_congr_fxv {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_cons_congr_fxv {t t0 : GroundTerm} {ts ts0 : List GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hs : c.sortsOf ts = c.sortsOf ts0) : c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts0) := by
  simp only [Semantics.sortsOf, h, hs]

theorem sortOf_inj_congr_fxv {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

/-- `inj{Int, KItem}(i)`. -/
def ki (i : Int) : GroundTerm := .inj Srt.int Srt.kitem (int i)

/-- An Int injected into KItem has the sort of `inj{Int, KItem}(0)`. -/
theorem sortOf_ki_fxv (i : Int) : c.sortOf (ki i) = c.sortOf (ki 0) :=
  sortOf_inj_congr_fxv (by rw [sortOf_int, sortOf_int]) rfl

end Shared

namespace Map

open ML Faithful

definition_of defn from "f2-examples/heldmap.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 34
def kCell : Sym := 385
def mCell : Sym := 387
def symSet : Sym := 389

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName mCell = "Lbl'-LT-'m'-GT-'" ∧ c.symName symSet = "Lblset" ∧
    c.symName mapUnit = "Lbl'Stop'Map" ∧ c.symName mapElem = "Lbl'UndsPipe'-'-GT-Unds'" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem rules_eq : c.rules = [r0] := by
  have h : c.rules.length = 1 := by decide +kernel
  match hr : c.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]

theorem r0_vars : r0.vars = [Srt.int, Srt.k, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symSet [.var 0]),
    .var 1]], .app mCell [.app mapUnit []], .var 2] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.var 1],
    .app mCell [.app mapElem [.inj Srt.int Srt.kitem (.var 0), .inj Srt.int Srt.kitem (.var 3)]], .var 2] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `<m> .Map => K |-> ?V:Int </m>`: V (variable 3) is existential, under no constructor of the right
side but under the map's element symbol, which `holds`; the rule has `ruleSorted` and the conjunct
`rulePlainHO1`, and needs no witness. Int is not confined. -/
theorem held : c.ruleSorted r0 = true ∧ (heldOccs c r0.rhs).contains 3 = true ∧
    (ctorOccs c r0.rhs).contains 3 = false ∧ c.holds mapElem = true ∧ c.isCtor mapElem = false ∧
    c.rulePlainHO1 r0 = true ∧ c.confined Srt.int = false := by
  decide +kernel

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel
theorem shapesOK : c.shapesOK = true := by decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symSet = true ∧ c.isCtor mCell = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true ∧
    c.isCtor mapElem = false ∧ isHook mapElem = true := by
  decide +kernel
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symSet = false ∧
    patternHooks.contains mCell = false ∧ patternHooks.contains mapUnit = true := by
  decide +kernel

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]

/-- `<k> set(5) ~> . </k> <m> .Map </m>`. -/
def X : Config c :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symSet [int 5]), .ctor dotk []]],
    .ctor mCell [.map Srt.map []], ctr], by decide +kernel⟩

/-- The configuration `<k> . </k> <m> 5 |-> i </m>`. -/
def cfgY (i : Int) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor mCell [.map Srt.map [(ki 5, ki i)]], ctr]

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs mCell).isSome = true := by
  decide +kernel

theorem collOf_map : c.collOf Srt.map = some ⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩ := by
  decide +kernel

theorem sortOf_ki (j : Int) : c.sortOf (ki j) = some Srt.kitem := by
  rw [sortOf_ki_fxv j]; decide +kernel

/-- `<k> . </k> <m> 5 |-> i </m>` is a configuration for every Int i, as `5 |-> 0` is. -/
theorem sortOf_cfgY (i : Int) : c.sortOf (cfgY i) = some topCellSort := by
  have h0 : c.sortOf (cfgY 0) = some topCellSort := by decide +kernel
  rw [← h0]
  have hm : c.sortOf (.map Srt.map [(ki 5, ki i)]) = c.sortOf (.map Srt.map [(ki 5, ki 0)]) := by
    simp only [Semantics.sortOf, collOf_map, Semantics.entriesOK, Semantics.entryOK, keysSorted, sortOf_ki]
  exact sortOf_ctor_congr_fxv lookups_ok.1 (sortsOf_cons_congr_fxv rfl
    (sortsOf_cons_congr_fxv (sortOf_ctor_congr_fxv lookups_ok.2 (sortsOf_cons_congr_fxv hm rfl)) rfl))

def Y (i : Int) : Config c := ⟨cfgY i, sortOf_cfgY i⟩

/-! ## `Step` from `set(5)` to `5 |-> i`, for every Int i -/

def σ (i : Int) : Subst := [(0, int 5), (1, .ctor dotk []), (2, ctr), (3, int i)]

theorem hmatchX (τ : Subst) (h0 : τ.lookup 0 = some (int 5)) (h1 : τ.lookup 1 = some (.ctor dotk []))
    (h2 : τ.lookup 2 = some ctr) : PatVal c τ r0.lhs X.val := by
  rw [r0_lhs]
  exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
    (.cons (.inj (.ctor syms_ok.2.2.2.1 (.cons (.var h0) .nil))) (.cons (.var h1) .nil))) .nil))
    (.cons (.ctor syms_ok.2.2.2.2.1 (.cons (.hook hooks_ok.2.2.2.2.2 .nil rfl) .nil)) (.cons (.var h2) .nil)))

/-- `K |-> V` at K := 5, V := i is the map `5 |-> i`. -/
theorem elemEval (i : Int) : EvalTerm c (σ i)
    (.app mapElem [.inj Srt.int Srt.kitem (.var 0), .inj Srt.int Srt.kitem (.var 3)])
    (some (.map Srt.map [(ki 5, ki i)])) :=
  .hook syms_ok.2.2.2.2.2.2.2.1 syms_ok.2.2.2.2.2.2.2.2 (.cons (.inj .var) (.cons (.inj .var) .nil))
    (fun vs hvs => by
      obtain rfl : vs = [ki 5, ki i] := (Option.some.inj (show some [ki 5, ki i] = some vs from hvs)).symm
      exact Semantics.hookRes_of_value (Exec.hook_mapElem _ _))
    (fun h => nomatch (show some [ki 5, ki i] = none from h))

/-- **`set(5)` steps to `5 |-> i`** by the rule, V := i. -/
theorem stepBy (i : Int) : StepBy c r0 (σ i) X (Y i) where
  mem := by rw [rules_eq]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 5⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int i⟩
    | _ + 4, hs => simp at hs
  hmatch := hmatchX _ rfl rfl rfl
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons .var .nil))
      (.cons (.ctor syms_ok.2.2.2.2.1 (.cons (elemEval i) .nil)) (.cons .var .nil)))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

theorem step (i : Int) : Step c X (Y i) := step_iff_by.mpr ⟨r0, σ i, stepBy i⟩

/-! ## No other successor -/

/-- **What the left side denotes**: `<k> set(k) ~> w </k> <m> m </m>` with the counter cell u, k, w
and u the values σ gives the variables 0, 1 and 2. -/
theorem lhs_inv {τ : Subst} {x : GroundTerm} (h : PatVal c τ r0.lhs x) :
    ∃ k w m u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symSet [k]), w]],
      .ctor mCell [m], u] ∧ τ.lookup 0 = some k ∧ τ.lookup 1 = some w ∧ τ.lookup 2 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h syms_ok.1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨v2, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  obtain ⟨u, vs3, rfl, h3, hvs3⟩ := hvs2.cons_inv
  cases hvs3.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 syms_ok.2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, ns, rfl, hns⟩ := PatVal.app_inv hooks_ok.2.2.2.2.1 h2 syms_ok.2.2.2.2.1
  obtain ⟨m, ns1, rfl, -, hns1⟩ := hns.cons_inv
  cases hns1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 syms_ok.2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2.1 ha syms_ok.2.2.2.1
  obtain ⟨k, as1, rfl, hk, has1⟩ := has.cons_inv
  cases has1.nil_inv
  exact ⟨k, w, m, u, rfl, PatVal.var_inv hk, PatVal.var_inv hz2, PatVal.var_inv h3⟩

/-- **Every `Step` successor of `<k> set(5) </k> <m> .Map </m>` is a `5 |-> i`.** -/
theorem step_inv {y : Config c} (hs : Step c X y) : ∃ i : Int, y = Y i := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hr := hb.mem
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  obtain ⟨k, w, m, u, hx, h0, h1, h2⟩ := lhs_inv hb.hmatch
  simp only [X, GroundTerm.ctor.injEq, GroundTerm.inj.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hx
  obtain ⟨v, h3, hv⟩ := hb.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨i, rfl⟩ := shape_int shapesOK hv
  refine ⟨i, Subtype.ext ?_⟩
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv syms_ok.1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  obtain ⟨q3, rs3, rfl, hq3, hrs3⟩ := hrs2.cons_inv
  cases hrs3.nil_inv
  rw [hq3.var_inv, h2] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv syms_ok.2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  rw [hp1.var_inv, h1] at he
  obtain ⟨ms, hms, rfl⟩ := EvalTerm.ctor_inv syms_ok.2.2.2.2.1 hq2
  obtain ⟨m1, ms1, rfl, hm1, hms1⟩ := hms.cons_inv
  cases hms1.nil_inv
  obtain ⟨es, hes, hh, -⟩ := evalHook_inv_fxv syms_ok.2.2.2.2.2.2.2.1 syms_ok.2.2.2.2.2.2.2.2 hm1
  obtain ⟨e1, es1, rfl, he1, hes1⟩ := hes.cons_inv
  obtain ⟨e2, es2, rfl, he2, hes2⟩ := hes1.cons_inv
  cases hes2.nil_inv
  obtain ⟨e1', he1', rfl⟩ := EvalTerm.inj_inv he1
  obtain ⟨e2', he2', rfl⟩ := EvalTerm.inj_inv he2
  rw [he1'.var_inv, h0, he2'.var_inv, h3] at hh
  have hm := hh _ rfl
  rw [Semantics.hookRes_of_value (Exec.hook_mapElem _ _)] at hm
  cases hm
  simp only [allSome, Option.bind, Option.map, injNormal, Option.some.injEq] at he
  exact he

/-- **The successors of `<k> set(5) </k> <m> .Map </m>`** are exactly the `5 |-> i`, i an Int. -/
theorem step_iff (y : Config c) : Step c X y ↔ ∃ i : Int, y = Y i :=
  ⟨step_inv, fun ⟨i, hi⟩ => hi ▸ step i⟩

/-- **In every model of `Γc`, `<k> set(5) </k> <m> .Map </m>` has a successor among the instances of
the application, and `5 |-> i` is one of them**, for every Int i (`sound_at`; no competitor, no
function). -/
theorem sound_xy (i : Int) :
    (Γc c ⊧ (den c X.val ⇒ KoreAML.sNext (famEx c r0 (σ i)))) ∧ (Γc c ⊧ (den c (Y i).val ⇒ famEx c r0 (σ i))) :=
  sound_at c coreOK X (Y i) r0 (σ i) (stepBy i)
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn => by rw [fns_nil] at hfn; cases hfn)

/-- **By `ExactC`**: y is a successor of `<k> set(5) </k> <m> .Map </m>` in some model of `Γc` with
the step's closure exactly where y is some `5 |-> i`; in no model is another value a successor. -/
theorem exact_y (y : Config c) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ¬ (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ↔
    ∃ i : Int, y = Y i := by
  rw [← exact_hyp c coreOK fnHyp X y]
  exact step_iff y

/-- info: 'HeldFixtures.Map.held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms held
/-- info: 'HeldFixtures.Map.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'HeldFixtures.Map.sound_xy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xy
/-- info: 'HeldFixtures.Map.exact_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_y

end Map

end HeldFixtures
