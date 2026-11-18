/-
  KCore, checked layer: library equations whose terms apply parameter symbols and injections,
  entailed at values (`EntailsAtValues`) wherever their two sides have the same value under the
  semantics' interpretation of the parameters.

  `LibEv`'s terms apply interpreted hooked symbols only (`LibEv.srt?` reads `hookSigs`). Γ also
  states the graph of each parameter symbol (`ΓDomains`, its value `Semantics.paramVal`, which reads
  the interpretation `c.hooks` for a parameter without implementation), and of each injection
  (`inj{a, b}` at the pattern of a value is the pattern of the injected value). The terms here
  apply those too.
  - `LibEv.koreP`, `LibEv.valP`, `LibEv.srtP?`: such a term as a KORE pattern, its value at a
    substitution, its sort. An application of a symbol of `hookSigs` has `Semantics.hv`'s value, an
    application of a parameter symbol `paramVal`'s, an injection `inj{a, b}(t)` the value
    `.inj a b v` of t's value v, where `(a, b)` is one of the subsorts and no sort is below a (so v
    is no injection).
  - `LibEv.den_valP`: in a model of `Γ c`, at a valuation that gives each variable its value's
    element, the translated term denotes its value's element, or nothing where it has none.
  - `LibEv.FnEqn.entailedP`: an equation in the function form (`LibEv.FnEqn`, over these terms)
    whose sides have the same value at every substitution of values at which its `requires` is
    `true` and its patterns match (`FnEqn.HoldsP`) is entailed at values.
-/
import KcoreSpec.LibEvFn

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace LibEv

open ML Faithful

mutual
  /-- A term over variables, domain values, interpreted hooked symbols, parameter symbols and
  injections as a KORE pattern, the i-th variable under its name in `vars`. -/
  def koreP (c : Semantics) (vars : Vars) : Term → Kore.Pattern
    | .var i => .var (.evar (KoreAML.evar (vars.getD i ("", 0)).1 (srtOf c (vars.getD i ("", 0)).2)))
    | .app f ts => symApp c f (korePList c vars ts)
    | .dv s lit => .dv (srtOf c s) lit.text
    | .inj a b t => KoreAML.injP (c.sortName a) (c.sortName b) (koreP c vars t)
    | .as t _ => koreP c vars t
    termination_by structural t => t
  def korePList (c : Semantics) (vars : Vars) : List Term → List Kore.Pattern
    | [] => []
    | t :: ts => koreP c vars t :: korePList c vars ts
    termination_by structural ts => ts
end

/-- Γ's value of the symbol `f` at `ws`: an interpreted hooked symbol's (`Semantics.hv`), a
parameter symbol's (`Semantics.paramVal`) otherwise. -/
def appValP (c : Semantics) (f : Sym) (ws : List GroundTerm) : Option GroundTerm :=
  match lookupSig hookSigs f with
  | some _ => c.hv f ws
  | none => c.paramVal f ws

/-- The argument and result sorts of the symbol `f`: an interpreted hooked symbol's, a parameter
symbol's otherwise. -/
def sigOfP (c : Semantics) (f : Sym) : Option (List Srt × Srt) :=
  match lookupSig hookSigs f with
  | some k => some (k.args, k.result)
  | none => (c.lookupParam f).map fun kp => (kp.sig.args, kp.sig.result)

mutual
  /-- The value of such a term at σ: Γ's value of an interpreted symbol (`Semantics.hv`) or of a
  parameter symbol (`Semantics.paramVal`) at its arguments' values, the injected value of an
  injection, none where an argument has none. -/
  def valP (c : Semantics) (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .app f ts => (allSome (valPList c σ ts)).bind (appValP c f)
    | .dv s lit => some (.dv s lit)
    | .inj a b t => (valP c σ t).map (.inj a b)
    | .as _ _ => none
    termination_by structural t => t
  def valPList (c : Semantics) (σ : Subst) : List Term → List (Option GroundTerm)
    | [] => []
    | t :: ts => valP c σ t :: valPList c σ ts
    termination_by structural ts => ts
end

mutual
  /-- The sort of such a term: a variable's, a domain value's where it is a value of its sort, the
  result sort of an interpreted hooked symbol or of a parameter symbol applied to terms of its
  argument sorts, `b` for `inj{a, b}(t)` with t of the sort a, `(a, b)` one of the subsorts and no
  sort below a. -/
  def srtP? (c : Semantics) (vars : Vars) : Term → Option Srt
    | .var i => vars[i]?.map (·.2)
    | .app f ts => (sigOfP c f).bind fun k => if srtsP? c vars ts == some k.1 then some k.2 else none
    | .dv s lit => if c.sortOf (.dv s lit) == some s then some s else none
    | .inj a b t =>
      if c.subsorts.contains (a, b) && c.subsorts.all (fun p => p.2 != a) && srtP? c vars t == some a
      then some b else none
    | .as _ _ => none
    termination_by structural t => t
  def srtsP? (c : Semantics) (vars : Vars) : List Term → Option (List Srt)
    | [] => some []
    | t :: ts => (srtP? c vars t).bind fun s => (srtsP? c vars ts).map (s :: ·)
    termination_by structural ts => ts
end

theorem lookupParam_some_paramP {c : Semantics} {f : Sym} {kp : ParamSig} (h : c.lookupParam f = some kp) :
    kp ∈ c.params ∧ kp.sig.name = f := by
  rw [Semantics.lookupParam_eq] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A value of a sort with no sort below it is no injection. -/
theorem not_isInj_of_noSubP {c : Semantics} {a : Srt} (hno : c.subsorts.all (fun p => p.2 != a) = true)
    {w : GroundTerm} (hw : c.sortOf w = some a) : w.isInj = false := by
  cases w with
  | inj x y u =>
    exfalso
    rw [Semantics.sortOf] at hw
    by_cases hc : (c.subsorts.contains (x, y) && !u.isInj && c.sortOf u == some x) = true
    · simp only [hc, ↓reduceIte] at hw
      cases hw
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      have := List.all_eq_true.mp hno _ hc.1.1
      simp at this
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hw
  | _ => rfl

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
include h hI hσ hag

set_option linter.unusedSectionVars false in
mutual
  /-- **A term over parameter symbols and injections denotes its value.** In a model of `Γ c`, at
  a valuation that gives each variable the element of its value under σ, the translation of a term
  of the sort `s` denotes the element of its value, or nothing where it has none; and its value is
  of the sort `s`. -/
  theorem den_valP : ∀ (t : Term) {s : Srt}, srtP? c vars t = some s →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (koreP c vars t)).interpret I e m ↔ Res c I e (valP c σ t) m) ∧
      (∀ v, valP c σ t = some v → c.sortOf v = some s)
    | .var i, s, ht => by
      simp only [srtP?] at ht
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨v, hv, hvs⟩ := hσ i p hp
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨fun m => ?_, fun w hw => ?_⟩
      · rw [koreP, KoreAML.tr, valP, hv]
        exact hag i v hlt hv m
      · rw [valP, hv] at hw
        cases hw
        exact hvs
    | .dv s' lit, s, ht => by
      simp only [srtP?] at ht
      by_cases hd : c.sortOf (.dv s' lit) = some s'
      · simp only [hd, beq_self_eq_true, ite_true, Option.some.injEq] at ht
        subst ht
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [koreP, valP]
          show _ ↔ (den c (.dv s' lit)).interpret I e m
          unfold den KoreAML.den
          rw [GroundTerm.kore]
          unfold srtOf
          rw [KoreAML.tr_dv, KoreAML.tr_dv]
        · rw [valP] at hw
          cases hw
          exact hd
      · simp [hd] at ht
    | .app f ts, s, ht => by
      simp only [srtP?] at ht
      obtain ⟨kk, hkk, ht⟩ := Option.bind_eq_some_iff.mp ht
      cases hl : lookupSig hookSigs f with
      | some k =>
        rw [sigOfP, hl] at hkk
        cases hkk
        dsimp only at ht
        by_cases hargs : srtsP? c vars ts = some k.args
        · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at ht
          subst ht
          obtain ⟨hks, hkn⟩ := lookupSig_spec hl
          have hih := den_valsP ts hargs
          have hhook : isHook f = true := by
            cases hh : isHook f with
            | true => rfl
            | false => rw [lookupSig_hookSigs_of_not_isHook hh] at hl; cases hl
          refine ⟨fun m => ?_, fun w hw => ?_⟩
          · rw [koreP, tr_symApp, valP]
            cases hall : allSome (valPList c σ ts) with
            | none =>
              simp only [Option.bind_none, Res, iff_false]
              exact hih.2 hall _ m
            | some ws =>
              obtain ⟨hws, hcong⟩ := hih.1 ws hall
              obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
              have hax := sat_hookRes hI hks hws (by rw [hkn]; exact ho)
              have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
              rw [hkn] at hgr
              unfold KoreAML.den at hgr
              rw [tr_symApp] at hgr
              rw [hcong _ _ (fun _ => Iff.rfl) m, hgr]
              simp only [Option.bind_some, appValP, hl, Semantics.hv, ho, Option.join_some]
              cases o with
              | none => simp [Res, Pattern.interpret]
              | some v => rfl
          · rw [valP] at hw
            cases hall : allSome (valPList c σ ts) with
            | none => rw [hall] at hw; cases hw
            | some ws =>
              rw [hall] at hw
              simp only [Option.bind_some, appValP, hl] at hw
              obtain ⟨hws, -⟩ := hih.1 ws hall
              obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
              have ho' : o = some w := by simpa [Semantics.hv, ho] using hw
              exact hookRes_sorted (fun _ => rangeBelow_of_core h) hl hws (ho' ▸ ho)
        · simp [hargs] at ht
      | none =>
        rw [sigOfP, hl] at hkk
        obtain ⟨kp, hkp, rfl⟩ := Option.map_eq_some_iff.mp hkk
        have ht2 := ht
        dsimp only at ht2
        by_cases hargs : srtsP? c vars ts = some kp.sig.args
        · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at ht2
          subst ht2
          obtain ⟨hkpm, hkn⟩ := lookupParam_some_paramP hkp
          have hih := den_valsP ts hargs
          refine ⟨fun m => ?_, fun w hw => ?_⟩
          · rw [koreP, tr_symApp, valP]
            cases hall : allSome (valPList c σ ts) with
            | none =>
              simp only [Option.bind_none, Res, iff_false]
              exact hih.2 hall _ m
            | some ws =>
              obtain ⟨hws, hcong⟩ := hih.1 ws hall
              have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, ws, hkpm, hws, rfl⟩))
              have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
              rw [hkn] at hgr
              unfold KoreAML.den at hgr
              rw [tr_symApp] at hgr
              rw [hcong _ _ (fun _ => Iff.rfl) m, hgr]
              simp only [Option.bind_some, appValP, hl]
              cases c.paramVal f ws with
              | none => simp [Res, Pattern.interpret]
              | some v => rfl
          · rw [valP] at hw
            cases hall : allSome (valPList c σ ts) with
            | none => rw [hall] at hw; cases hw
            | some ws =>
              rw [hall] at hw
              simp only [Option.bind_some, appValP, hl] at hw
              obtain ⟨k', hk', hs'⟩ := c.paramVal_sorted hw
              rw [hkp] at hk'
              cases hk'
              exact hs'
        · simp [hargs] at ht2
    | .inj a b t, s, ht => by
      simp only [srtP?] at ht
      by_cases hc : (c.subsorts.contains (a, b) && c.subsorts.all (fun p => p.2 != a) &&
          srtP? c vars t == some a) = true
      · simp only [hc, ↓reduceIte] at ht
        cases ht
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨hab, hno⟩, hta⟩ := hc
        have ih := den_valP t hta
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [koreP, KoreAML.tr_injP, valP]
          cases hv : valP c σ t with
          | none =>
            simp only [Option.map_none, Res, iff_false]
            intro hm
            simp only [KoreAML.appList] at hm
            obtain ⟨-, x, -, hx, -⟩ := KoreAML.interp_app.mp hm
            have := (ih.1 x).mp hx
            rw [hv] at this
            exact this
          | some w =>
            simp only [Option.map_some, Res]
            rw [den_inj]
            simp only [KoreAML.appList]
            refine KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun x => ?_) m
            rw [ih.1 x, hv]
            rfl
        · rw [valP] at hw
          cases hv : valP c σ t with
          | none => rw [hv] at hw; cases hw
          | some u =>
            rw [hv] at hw
            simp only [Option.map_some, Option.some.injEq] at hw
            subst hw
            have hu := ih.2 u hv
            rw [Semantics.sortOf, hab, not_isInj_of_noSubP hno hu, hu]
            simp
      · simp only [hc, ↓reduceIte, reduceCtorEq] at ht
    | .as _ _, s, ht => by simp [srtP?] at ht
  termination_by structural t => t
  /-- The arguments of an application: where each has a value, the values are of the argument
  sorts and the application of any head to the translated arguments is its application to the
  values' patterns; where one has none, the application denotes nothing. -/
  theorem den_valsP : ∀ (ts : List Term) {ss : List Srt}, srtsP? c vars ts = some ss →
      (∀ ws, allSome (valPList c σ ts) = some ws → c.sortsOf ws = some ss ∧
        ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
          ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (korePList c vars ts)).interpret I e m ↔
            (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome (valPList c σ ts) = none →
        ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (korePList c vars ts)).interpret I e m)
    | [], ss, ht => by
      simp only [srtsP?, Option.some.injEq] at ht
      subst ht
      refine ⟨fun ws hws => ?_, fun hn => by simp [valPList, allSome] at hn⟩
      simp only [valPList, allSome, Option.some.injEq] at hws
      subst hws
      refine ⟨sortsOf_nil, fun acc acc' hacc m => ?_⟩
      rw [korePList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | t :: ts, ss, ht => by
      simp only [srtsP?] at ht
      obtain ⟨s, h1, hrest⟩ := Option.bind_eq_some_iff.mp ht
      obtain ⟨ss', h2, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ih1 := den_valP t h1
      have ih2 := den_valsP ts h2
      constructor
      · intro ws hws
        simp only [valPList, allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, hw, ws', hws', rfl⟩ := hws
        obtain ⟨hs', hc'⟩ := ih2.1 ws' hws'
        refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.2 w hw, hs', rfl⟩, fun acc acc' hacc m => ?_⟩
        rw [korePList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact hc' _ _ (KoreAML.interp_app_congr hacc (fun m => by rw [ih1.1 m, hw]; rfl)) m
      · intro hn acc m
        rw [korePList, KoreAML.trArgs_cons]
        cases hr : valP c σ t with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            have hb' := (ih1.1 b).mp hb
            rw [hr] at hb'
            exact hb') _ m
        | some w =>
          cases hrs : allSome (valPList c σ ts) with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [valPList, allSome, hr, hrs] at hn
  termination_by structural ts => ts
end

end

theorem fq_valP_var (c : Semantics) (σ : Subst) (k : Nat) : valP c σ (.var k) = σ.lookup k := by rw [valP]

namespace FnEqn

/-- A pattern as KORE (`koreP`): its term, or `\and{s}(t, V)` for `t #as V`. -/
def patKP (c : Semantics) (vs : Vars) (s : Srt) (t : Term) : Option Nat → Kore.Pattern
  | none => koreP c vs t
  | some j => .and (srtOf c s) [koreP c vs t, koreP c vs (.var j)]

/-- The conjunction of the `\in` premises (`koreP`), the first argument variable the variable `k`. -/
def insP (c : Semantics) (vs : Vars) : Nat → List FnPat → Kore.Pattern
  | _, [] => .top KoreAML.R
  | k, p :: ps => .and KoreAML.R
      [.in (srtOf c p.1) KoreAML.R (koreP c vs (.var k)) (patKP c vs p.1 p.2.1 p.2.2), insP c vs (k + 1) ps]

/-- The first conjunct of the premise (`koreP`). -/
def reqPP (c : Semantics) (E : FnEqn) : Kore.Pattern :=
  match E.req with
  | none => .top KoreAML.R
  | some q => .equals (srtOf c Srt.bool) KoreAML.R (koreP c E.av q) (.dv (srtOf c Srt.bool) "true")

/-- The pattern of the equation's axiom over these terms, as kompile writes it over the sort
variable `R`. -/
def patternP (c : Semantics) (E : FnEqn) : Kore.Pattern :=
  .implies KoreAML.R (.and KoreAML.R [E.reqPP c, insP c E.av E.vars.length E.pats])
    (.equals (srtOf c E.s) KoreAML.R (koreP c E.av E.lhs)
      (.and (srtOf c E.s) [koreP c E.av E.rhs, .top (srtOf c E.s)]))

/-- Each pattern is a term (`srtP?`) of its argument's sort, a registry sort, and so are the
argument variable and the `#as` variable. -/
def patsTypedP (c : Semantics) (vs : Vars) : Nat → List FnPat → Bool
  | _, [] => true
  | k, p :: ps => decide (p.1 < nRegSorts) && srtP? c vs (.var k) == some p.1 &&
      srtP? c vs p.2.1 == some p.1 &&
      (match p.2.2 with
        | none => true
        | some j => srtP? c vs (.var j) == some p.1) && patsTypedP c vs (k + 1) ps

/-- The equation is over registry sorts, its sides are terms (`srtP?`) of the sort `s`, its
patterns terms of the argument sorts and its `requires` a term of the sort Bool. -/
def typedP (c : Semantics) (E : FnEqn) : Bool :=
  decide (E.s < nRegSorts) && E.av.all (fun p => decide (p.2 < nRegSorts)) &&
  srtP? c E.av E.lhs == some E.s && srtP? c E.av E.rhs == some E.s &&
  patsTypedP c E.av E.vars.length E.pats &&
  match E.req with
  | none => true
  | some q => srtP? c E.av q == some Srt.bool

/-- At σ, each pattern has (`valP`) the value of its argument variable, and the variable of a
`#as` has that value too. -/
def MatchesP (c : Semantics) (σ : Subst) : Nat → List FnPat → Prop
  | _, [] => True
  | k, p :: ps => valP c σ p.2.1 = σ.lookup k ∧ (∀ j, p.2.2 = some j → σ.lookup j = σ.lookup k) ∧
      MatchesP c σ (k + 1) ps

/-- `f` at the argument variables and the right side have the same value (`valP`), or both none,
at every substitution of values of the variables' sorts at which the `requires` has the value
`true` and the patterns match the arguments. -/
def HoldsP (c : Semantics) (E : FnEqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, E.req = some q → valP c σ q = some (bool true)) → MatchesP c σ E.vars.length E.pats →
    valP c σ E.lhs = valP c σ E.rhs

end FnEqn

theorem FnEqn.entailedP {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (ht : E.typedP c = true)
    (hE : E.HoldsP c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patternP c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [FnEqn.typedP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htp⟩, htq⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI E.av hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srtP? c E.av u = some s) =>
    den_valP (tbl := t) (e := e) h hI hσ hag u hu
  -- two terms of a sort that denote a common element have the same value
  have hsame : ∀ (u u' : Term) (s : Srt), srtP? c E.av u = some s → srtP? c E.av u' = some s → ∀ b,
      (KoreAML.tr ⟨t, []⟩ (koreP c E.av u)).interpret I e b →
      (KoreAML.tr ⟨t, []⟩ (koreP c E.av u')).interpret I e b → valP c σ u = valP c σ u' := by
    intro u u' s hu hu' b h1 h2
    rw [(hDV u s hu).1] at h1
    rw [(hDV u' s hu').1] at h2
    cases hv : valP c σ u with
    | none => rw [hv] at h1; exact h1.elim
    | some w =>
      cases hv' : valP c σ u' with
      | none => rw [hv'] at h2; exact h2.elim
      | some w' =>
        rw [hv] at h1
        rw [hv'] at h2
        have hw := (hDV u s hu).2 w hv
        have hw' := (hDV u' s hu').2 w' hv'
        exact congrArg some (values_apart hI hg hsc.trans (apartSort_of_sorted hg hw) hw hw'
          ((((elemOf_spec hI hw e).1 b).mp h1).symm.trans (((elemOf_spec hI hw' e).1 b).mp h2)))
  -- the sorts
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI (hnum (show Srt.bool < nRegSorts by decide))
  have hdist : (distinctSorts c).contains Srt.bool = true := by
    refine List.elem_eq_true_of_mem ?_
    unfold distinctSorts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  -- the `\in` premises give the match
  have hmatch : ∀ (ps : List FnPat) (k : Nat) (a : M), FnEqn.patsTypedP c E.av k ps = true →
      (KoreAML.tr ⟨t, []⟩ (FnEqn.insP c E.av k ps)).interpret I e a → FnEqn.MatchesP c σ k ps := by
    intro ps
    induction ps with
    | nil => intro k a _ _; trivial
    | cons p ps ih =>
      intro k a htp' hi
      obtain ⟨s', u, as⟩ := p
      simp only [FnEqn.patsTypedP, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
      obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
      simp only [FnEqn.insP] at hi
      rw [tr_and2, KoreAML.interp_sAnd] at hi
      obtain ⟨hin, hi'⟩ := hi
      obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI (hnum hpR)
      have hφ : ∀ a', (KoreAML.tr ⟨t, []⟩ (koreP c E.av (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
        intro a' ha'
        rw [(hDV (.var k) s' hxk).1] at ha'
        cases hv : valP c σ (.var k) with
        | none => rw [hv] at ha'; exact ha'.elim
        | some w =>
          rw [hv] at ha'
          have hw := (hDV (.var k) s' hxk).2 w hv
          obtain ⟨hw1, hw2⟩ := elemOf_spec hI hw e
          rw [(hw1 a').mp ha']
          refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
          have := hτp t e a''
          rwa [trSort_srtOf_twoT] at this
      rw [KoreAML.tr, KoreAML.interp_sIn hD hc (hτp t e) hRv hτpsort hR hφ] at hin
      obtain ⟨⟨b, hxb, hpb⟩, -⟩ := hin
      cases as with
      | none =>
        simp only [FnEqn.patKP] at hpb
        refine ⟨?_, fun j hj => (by cases hj), ih (k + 1) a hrest hi'⟩
        have := hsame u (.var k) s' hpt hxk b hpb hxb
        rwa [fq_valP_var] at this
      | some j =>
        simp only [FnEqn.patKP] at hpb
        rw [tr_and2, KoreAML.interp_sAnd] at hpb
        refine ⟨?_, fun j' hj' => ?_, ih (k + 1) a hrest hi'⟩
        · have := hsame u (.var k) s' hpt hxk b hpb.1 hxb
          rwa [fq_valP_var] at this
        · cases hj'
          have := hsame (.var j) (.var k) s' (eq_of_beq has) hxk b hpb.2 hxb
          rwa [fq_valP_var, fq_valP_var] at this
  rw [hp]
  unfold FnEqn.patternP
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hprem, hins⟩ := hprem
    have hreq : ∀ q, E.req = some q → valP c σ q = some (bool true) := by
      intro q hq
      unfold FnEqn.reqPP at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srtP? c E.av q = some Srt.bool := eq_of_beq htq
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) hRv hτbsort hR] at hprem
      have hT : c.sortOf (bool true) = some Srt.bool := rmS_sortOf_bool c true
      obtain ⟨hT1, hT2⟩ := elemOf_spec hI hT e
      have hinh : KoreAML.Inh I τb (elemOf c I (bool true)) := by
        refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hT2
        have := hτb t e a'
        rwa [trSort_srtOf_twoT] at this
      have hq1 := (hprem.2 _ hinh).mpr (by
        show (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e _
        have : (den c (bool true)).interpret I e (elemOf c I (bool true)) := (hT1 _).mpr rfl
        unfold den KoreAML.den bool at this
        rw [GroundTerm.kore] at this
        unfold srtOf
        rw [KoreAML.tr_dv] at this ⊢
        exact this)
      rw [(hDV q _ htq').1] at hq1
      cases hvq : valP c σ q with
      | none => rw [hvq] at hq1; exact hq1.elim
      | some w =>
        rw [hvq] at hq1
        have hw := (hDV q _ htq').2 w hvq
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩
            (dom_apart hI hdist hw hT hne e _)
    have heq := hE σ hσ hreq (hmatch E.pats E.vars.length a htp hins)
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, heq, ← (hDV E.rhs _ htr).1 b, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (koreP c E.av E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)))).interpret I e b
    rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)) =
      KoreAML.sTop (KoreAML.trSort t (srtOf c E.s)) from by rw [KoreAML.tr]]
    rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
    exact ⟨fun h' => ⟨h', hb⟩, And.left⟩


end LibEv

end KCore
