/-
  KCore, checked layer: library sentences over set variables, at sets of values.

  A set variable `@X` of a sort ranges over sets of elements of that sort; `SetVarsAtValues` sends
  it into the elements of values (KcoreSpec/TieDefs.lean). An application of a symbol at sets
  denotes, in a model, the union of its values at each choice of one element per argument
  (application is pointwise). So a term over set variables, domain values and interpreted hooked
  symbols denotes, where each set variable holds the elements of a set `ρ i` of values, the
  elements of a set of values, `svVals c ρ t`: Γ's value of each symbol at each choice of one value
  per argument.

  - `LibEv.svKore`: such a term as a KORE pattern over the registry's names, the i-th variable the
    set variable `@n` of `vars`; `svVals`: its set of values.
  - `LibEv.svDen`: in a model of `Γ c`, at a valuation whose i-th set variable holds the elements of
    the values of `ρ i`, the translated term denotes the elements of the values of `svVals c ρ t`.
  - `LibEv.SvPred`: a predicate of such a sentence (`\equals`, `\ceil`, `\and` of two, `\top`) and
    `SvPred.Holds`, what it says of the sets of values; `SvPred.den`: the translated predicate holds
    every element of the sort `Q0` where it `Holds`, none otherwise.
  - `LibEv.SvEqn`: a library sentence `\implies{R}(\top{R}(), \equals{Q0,R}(lhs, \and{Q0}(rhs,
    \top{Q0}())))` between two such predicates, over set variables only.
  - `SvEqn.entailed`: where the two sides hold at the same sets of values, the sentence is
    `EntailsAtSetValues`; `SvEqn.entailed_one`: where they hold at the same sets of at most one
    value, it holds at every valuation meeting `AtValues`, `SetVarsAtValues` and `SetVarsAtMostOne`
    (`SvAtMostOne`); `SvEqn.refuted_at`: where they do not hold at the same sets `ρ`, in every model
    of `Γ c` the sentence fails at a valuation meeting `AtValues` and `SetVarsAtValues`.
-/
import KcoreSpec.LibEvPred

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The key of the i-th variable of `vars` as a set variable, under the registry's sort names. -/
def svKey (vars : Vars) (i : Nat) : KoreAML.VarKey :=
  .svar (vars.getD i ("", 0)).1 (regSrtK (vars.getD i ("", 0)).2)

mutual
  /-- A term over set variables, domain values and interpreted hooked symbols as a KORE pattern over
  the registry's names, the i-th variable the set variable named in `vars`. -/
  def svKore (vars : Vars) : Term → Kore.Pattern
    | .var i => .var (.svar ⟨⟨⟨(vars.getD i ("", 0)).1⟩⟩, regSrtK (vars.getD i ("", 0)).2⟩)
    | .app f ts => .app ⟨⟨regSymNames.getD f ""⟩⟩ [] (svKoreList vars ts)
    | .dv s lit => .dv (regSrtK s) lit.text
    | .inj _ _ t => svKore vars t
    | .as t _ => svKore vars t
    termination_by structural t => t
  def svKoreList (vars : Vars) : List Term → List Kore.Pattern
    | [] => []
    | t :: ts => svKore vars t :: svKoreList vars ts
    termination_by structural ts => ts
end

mutual
  /-- The values of such a term where the i-th set variable holds the values `ρ i`: Γ's value of
  an interpreted symbol at each choice of one value per argument. -/
  def svVals (c : Semantics) (ρ : Nat → GroundTerm → Prop) : Term → GroundTerm → Prop
    | .var i => ρ i
    | .app f ts => fun w => ∃ ws, svValsList c ρ ts ws ∧ c.hv f ws = some w
    | .dv s lit => fun w => w = .dv s lit
    | .inj _ _ _ => fun _ => False
    | .as _ _ => fun _ => False
    termination_by structural t => t
  def svValsList (c : Semantics) (ρ : Nat → GroundTerm → Prop) : List Term → List GroundTerm → Prop
    | [], ws => ws = []
    | t :: ts, ws => ∃ w ws', ws = w :: ws' ∧ svVals c ρ t w ∧ svValsList c ρ ts ws'
    termination_by structural ts => ts
end

/-- Application is pointwise in its left side: where the accumulator denotes the union of the
`B w` over `W`, the arguments applied to it denote the union of the arguments applied to each. -/
theorem sv_trArgs_union {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} (ctx : KoreAML.Ctx)
    {α : Type} (W : α → Prop) : ∀ (ps : List Kore.Pattern) (A : KoreAML.P) (B : α → KoreAML.P),
    (∀ a, A.interpret I e a ↔ ∃ w, W w ∧ (B w).interpret I e a) →
    ∀ m, (KoreAML.trArgs ctx A ps).interpret I e m ↔ ∃ w, W w ∧ (KoreAML.trArgs ctx (B w) ps).interpret I e m
  | [], A, B, h, m => by simp only [KoreAML.trArgs_nil]; exact h m
  | p :: ps, A, B, h, m => by
    simp only [KoreAML.trArgs_cons]
    refine sv_trArgs_union ctx W ps _ (fun w => B w ⬝ KoreAML.tr ctx p) (fun a => ?_) m
    simp only [KoreAML.interp_app, h]
    constructor
    · rintro ⟨x, y, ⟨w, hw, hx⟩, hy, hxy⟩; exact ⟨w, hw, x, y, hx, hy, hxy⟩
    · rintro ⟨w, hw, x, y, hx, hy, hxy⟩; exact ⟨x, y, ⟨w, hw, hx⟩, hy, hxy⟩

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {ρ : Nat → GroundTerm → Prop}
  {tbl : KoreAML.VarTable} {e : Valuation M}
  (hρ : ∀ i p, vars[i]? = some p → ∀ v, ρ i v → c.sortOf v = some p.2)
  (hag : ∀ i, i < vars.length → ∀ m,
    e.evalSvar (tbl.sv (svKey vars i)) m ↔ ∃ v, ρ i v ∧ (den c v).interpret I e m)
include h hI hρ hag

set_option linter.unusedSectionVars false in
mutual
  /-- **A term over set variables denotes the elements of its values.** In a model of `Γ c`, at a
  valuation whose i-th set variable holds the elements of the values `ρ i`, the translation of a
  term of the sort `s` denotes the elements of the values `svVals c ρ t`, and these are of the
  sort `s`. -/
  theorem svDen : ∀ (t : Term) {s : Srt}, reg t = true → srt? c vars t = some s →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (svKore vars t)).interpret I e m ↔
        ∃ v, svVals c ρ t v ∧ (den c v).interpret I e m) ∧
      (∀ v, svVals c ρ t v → c.sortOf v = some s)
    | .var i, s, _, ht => by
      simp only [srt?] at ht
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨fun m => ?_, fun v hv => hρ i p hp v hv⟩
      rw [svKore, svVals]
      exact hag i hlt m
    | .dv s' lit, s, hr, ht => by
      simp only [srt?] at ht
      simp only [reg, decide_eq_true_eq] at hr
      by_cases hd : c.sortOf (.dv s' lit) = some s'
      · simp only [hd, beq_self_eq_true, ite_true, Option.some.injEq] at ht
        subst ht
        have hdv : KoreAML.tr ⟨tbl, []⟩ (.dv (regSrtK s') lit.text) = den c (.dv s' lit) := by
          unfold den KoreAML.den
          rw [GroundTerm.kore, ← srtOf_reg c hr]
          unfold srtOf
          rw [KoreAML.tr_dv, KoreAML.tr_dv]
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [svKore, svVals, hdv]
          exact ⟨fun hm => ⟨_, rfl, hm⟩, fun ⟨w, hw, hm⟩ => hw ▸ hm⟩
        · rw [svVals] at hw
          subst hw
          exact hd
      · simp [hd] at ht
    | .app f ts, s, hr, ht => by
      simp only [reg, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hr
      obtain ⟨⟨hf, hite⟩, hrs⟩ := hr
      simp only [srt?] at ht
      obtain ⟨k, hk, hk2⟩ := Option.bind_eq_some_iff.mp ht
      by_cases hargs : srts? c vars ts = some k.args
      · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at hk2
        subst hk2
        obtain ⟨hks, hkn⟩ := lookupSig_spec hk
        have hih := svDens ts hrs hargs
        have hhook : isHook f = true := by
          cases hh : isHook f with
          | true => rfl
          | false => rw [lookupSig_hookSigs_of_not_isHook hh] at hk; cases hk
        have hhead : KoreAML.sym (.symbol (regSymNames.getD f "")) = symHead c f := by
          unfold symHead; rw [symName_reg c hf, hite]
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [svKore, KoreAML.tr_app0, hhead, hih.2 _ m, svVals]
          constructor
          · rintro ⟨ws, hws, hm⟩
            have hso := hih.1 ws hws
            obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
            have hax := sat_hookRes hI hks hso (by rw [hkn]; exact ho)
            have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
            rw [hkn] at hgr
            unfold KoreAML.den at hgr
            rw [tr_symApp] at hgr
            have hm' := hgr.mp hm
            cases o with
            | none => exact hm'.elim
            | some v => exact ⟨v, ⟨ws, hws, by simp [Semantics.hv, ho]⟩, hm'⟩
          · rintro ⟨v, ⟨ws, hws, hv⟩, hm⟩
            have hso := hih.1 ws hws
            obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
            have hax := sat_hookRes hI hks hso (by rw [hkn]; exact ho)
            have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
            rw [hkn] at hgr
            unfold KoreAML.den at hgr
            rw [tr_symApp] at hgr
            have ho' : o = some v := by simpa [Semantics.hv, ho] using hv
            subst ho'
            exact ⟨ws, hws, hgr.mpr hm⟩
        · rw [svVals] at hw
          obtain ⟨ws, hws, hv⟩ := hw
          obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
          have ho' : o = some w := by simpa [Semantics.hv, ho] using hv
          exact hookRes_sorted (fun _ => rangeBelow_of_core h) hk (hih.1 ws hws) (ho' ▸ ho)
      · simp [hargs] at hk2
    | .inj _ _ _, s, hr, _ => by simp [reg] at hr
    | .as _ _, s, hr, _ => by simp [reg] at hr
  termination_by structural t => t
  /-- The arguments of an application at sets of values: each choice of one value per argument
  is of the argument sorts, and any head applied to the translated arguments denotes the union of
  its applications to the values' patterns. -/
  theorem svDens : ∀ (ts : List Term) {ss : List Srt}, regList ts = true → srts? c vars ts = some ss →
      (∀ ws, svValsList c ρ ts ws → c.sortsOf ws = some ss) ∧
      (∀ (acc : KoreAML.P) m, (KoreAML.trArgs ⟨tbl, []⟩ acc (svKoreList vars ts)).interpret I e m ↔
        ∃ ws, svValsList c ρ ts ws ∧ (KoreAML.trArgs ⟨[], []⟩ acc (GroundTerm.koreList c ws)).interpret I e m)
    | [], ss, _, ht => by
      simp only [srts?, Option.some.injEq] at ht
      subst ht
      refine ⟨fun ws hws => ?_, fun acc m => ?_⟩
      · rw [svValsList] at hws; subst hws; exact sortsOf_nil
      · simp only [svKoreList, svValsList, KoreAML.trArgs_nil]
        constructor
        · intro hm; exact ⟨[], rfl, by rw [GroundTerm.koreList, KoreAML.trArgs_nil]; exact hm⟩
        · rintro ⟨ws, rfl, hm⟩; rw [GroundTerm.koreList, KoreAML.trArgs_nil] at hm; exact hm
    | t :: ts, ss, hr, ht => by
      simp only [regList, Bool.and_eq_true] at hr
      simp only [srts?] at ht
      obtain ⟨s, h1, hrest⟩ := Option.bind_eq_some_iff.mp ht
      obtain ⟨ss', h2, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ih1 := svDen t hr.1 h1
      have ih2 := svDens ts hr.2 h2
      refine ⟨fun ws hws => ?_, fun acc m => ?_⟩
      · rw [svValsList] at hws
        obtain ⟨w, ws', rfl, hw, hws'⟩ := hws
        exact sortsOf_cons.mpr ⟨s, ss', ih1.2 w hw, ih2.1 ws' hws', rfl⟩
      · rw [svKoreList, KoreAML.trArgs_cons,
          sv_trArgs_union ⟨tbl, []⟩ (svVals c ρ t) _ _ (fun w => acc ⬝ den c w) (fun a => by
            simp only [KoreAML.interp_app, ih1.1]
            constructor
            · rintro ⟨x, y, hx, ⟨w, hw, hy⟩, hxy⟩; exact ⟨w, hw, x, y, hx, hy, hxy⟩
            · rintro ⟨w, hw, x, y, hx, hy, hxy⟩; exact ⟨x, y, hx, ⟨w, hw, hy⟩, hxy⟩) m]
        simp only [ih2.2, svValsList]
        constructor
        · rintro ⟨w, hw, ws', hws', hm⟩
          exact ⟨w :: ws', ⟨w, ws', rfl, hw, hws'⟩, by rw [GroundTerm.koreList, KoreAML.trArgs_cons]; exact hm⟩
        · rintro ⟨_, ⟨w, ws', rfl, hw, hws'⟩, hm⟩
          rw [GroundTerm.koreList, KoreAML.trArgs_cons] at hm
          exact ⟨w, hw, ws', hws', hm⟩
  termination_by structural ts => ts
end

end

/-! ## Predicates over set variables -/

/-- A predicate of a library sentence over set variables: an equation of two terms of the sort
`s`, the definedness of a term of the sort `s`, a conjunction of two, `\top`. -/
inductive SvPred where
  | eq (s : Srt) (t u : Term)
  | ceil (s : Srt) (t : Term)
  | and (p q : SvPred)
  | top

namespace SvPred

/-- The predicate as a KORE pattern of the sort `Q0`, over the registry's names. -/
def kore (vars : Vars) : SvPred → Kore.Pattern
  | .eq s t u => .equals (regSrtK s) Q0 (svKore vars t) (svKore vars u)
  | .ceil s t => .ceil (regSrtK s) Q0 (svKore vars t)
  | .and p q => .and Q0 [p.kore vars, q.kore vars]
  | .top => .top Q0

/-- Each term is over the registry's symbols and sorts and of its sort, a registry sort. -/
def typed (c : Semantics) (vars : Vars) : SvPred → Bool
  | .eq s t u => decide (s < nRegSorts) && reg t && reg u && srt? c vars t == some s && srt? c vars u == some s
  | .ceil s t => decide (s < nRegSorts) && reg t && srt? c vars t == some s
  | .and p q => p.typed c vars && q.typed c vars
  | .top => true

/-- Each equation is at a sort whose distinct values are distinct elements. -/
def Apart (c : Semantics) : SvPred → Prop
  | .eq s _ _ => apartSort c s = true
  | .ceil _ _ => True
  | .and p q => p.Apart c ∧ q.Apart c
  | .top => True

/-- What the predicate says where the i-th set variable holds the values `ρ i`: an equation, that
its terms have the same values; definedness, that the term has a value. -/
def Holds (c : Semantics) (ρ : Nat → GroundTerm → Prop) : SvPred → Prop
  | .eq _ t u => ∀ v, svVals c ρ t v ↔ svVals c ρ u v
  | .ceil _ t => ∃ v, svVals c ρ t v
  | .and p q => p.Holds c ρ ∧ q.Holds c ρ
  | .top => True

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {ρ : Nat → GroundTerm → Prop}
  {tbl : KoreAML.VarTable} {e : Valuation M}
  (hρ : ∀ i p, vars[i]? = some p → ∀ v, ρ i v → c.sortOf v = some p.2)
  (hag : ∀ i, i < vars.length → ∀ m,
    e.evalSvar (tbl.sv (svKey vars i)) m ↔ ∃ v, ρ i v ∧ (KCore.den c v).interpret I e m)
  (hQ : KoreAML.IsSort I (e.evalEvar (tbl.ev (.sortVar "Q0"))))
include h hI hρ hag hQ

/-- **A predicate over set variables denotes what it says of the sets of values.** In a model of
`Γ c`, at a valuation whose i-th set variable holds the elements of the values `ρ i` and that
gives `Q0` a sort, the translated predicate holds the elements of `Q0` where `Holds`, and none
otherwise. -/
theorem den : ∀ (p : SvPred), p.typed c vars = true → p.Apart c → ∀ a,
    (KoreAML.tr ⟨tbl, []⟩ (p.kore vars)).interpret I e a ↔
      KoreAML.Inh I (e.evalEvar (tbl.ev (.sortVar "Q0"))) a ∧ p.Holds c ρ
  | .eq s t u, ht, hap, a => by
    haveI : OvlOK c := ovlOK_of_core h
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    obtain ⟨hok, hfa, -, -, hids⟩ := Semantics.coreOK_parts h
    obtain ⟨-, hg, -⟩ := faithCoreOK_parts hfa
    simp only [typed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
    obtain ⟨⟨⟨⟨hs, hrt⟩, hru⟩, h1⟩, h2⟩ := ht
    obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _))
    have hQv : ∀ b, (KoreAML.trSort tbl Q0).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "Q0")) :=
      fun b => by rw [trSort_Q0, KoreAML.interp_evar]
    have d1 := svDen h hI hρ hag t hrt h1
    have d2 := svDen h hI hρ hag u hru h2
    have hin : ∀ v, c.sortOf v = some s → KoreAML.Inh I τ (elemOf c I v) := fun v hv => by
      refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp (elemOf_spec hI hv e).2
      have := hτ tbl e a'
      rwa [trSort_srtOf_twoT] at this
    have hel : ∀ v, c.sortOf v = some s → ∀ b, (KCore.den c v).interpret I e b ↔ b = elemOf c I v :=
      fun v hv b => (elemOf_spec hI hv e).1 b
    rw [kore, KoreAML.tr, ← srtOf_reg c hs, KoreAML.interp_sEquals hD hc (hτ tbl e) hQv hτsort hQ]
    refine and_congr_right fun _ => ?_
    show _ ↔ ∀ v, svVals c ρ t v ↔ svVals c ρ u v
    have hap' : ∀ v w, c.sortOf v = some s → c.sortOf w = some s → elemOf c I v = elemOf c I w → v = w :=
      fun v w hv hw he => values_apart hI hg (NamesApart.subsorts_trans_of hids hok) hap hv hw he
    constructor
    · intro hall v
      constructor
      · intro hv
        have hs1 := d1.2 v hv
        have hx := (hall _ (hin v hs1)).mp ((d1.1 _).mpr ⟨v, hv, (hel v hs1 _).mpr rfl⟩)
        obtain ⟨w, hw, hwm⟩ := (d2.1 _).mp hx
        have hs2 := d2.2 w hw
        rw [hel w hs2] at hwm
        rw [hap' v w hs1 hs2 hwm]; exact hw
      · intro hv
        have hs2 := d2.2 v hv
        have hx := (hall _ (hin v hs2)).mpr ((d2.1 _).mpr ⟨v, hv, (hel v hs2 _).mpr rfl⟩)
        obtain ⟨w, hw, hwm⟩ := (d1.1 _).mp hx
        have hs1 := d1.2 w hw
        rw [hel w hs1] at hwm
        rw [hap' v w hs2 hs1 hwm]; exact hw
    · intro heq b _
      rw [d1.1, d2.1]
      exact ⟨fun ⟨v, hv, hb⟩ => ⟨v, (heq v).mp hv, hb⟩, fun ⟨v, hv, hb⟩ => ⟨v, (heq v).mpr hv, hb⟩⟩
  | .ceil s t, ht, _, a => by
    haveI : OvlOK c := ovlOK_of_core h
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    simp only [typed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
    obtain ⟨⟨hs, hrt⟩, h1⟩ := ht
    obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _))
    have hQv : ∀ b, (KoreAML.trSort tbl Q0).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "Q0")) :=
      fun b => by rw [trSort_Q0, KoreAML.interp_evar]
    have d1 := svDen h hI hρ hag t hrt h1
    have hin : ∀ v, c.sortOf v = some s → KoreAML.Inh I τ (elemOf c I v) := fun v hv => by
      refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp (elemOf_spec hI hv e).2
      have := hτ tbl e a'
      rwa [trSort_srtOf_twoT] at this
    have hφ : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (svKore vars t)).interpret I e b → KoreAML.Inh I τ b := by
      intro b hb
      obtain ⟨v, hv, hbv⟩ := (d1.1 b).mp hb
      have hs1 := d1.2 v hv
      rw [(elemOf_spec hI hs1 e).1 b] at hbv
      rw [hbv]; exact hin v hs1
    rw [kore, KoreAML.tr, ← srtOf_reg c hs, KoreAML.interp_sCeil hD hc (hτ tbl e) hQv hτsort hQ hφ, and_comm]
    refine and_congr_right fun _ => ?_
    show _ ↔ ∃ v, svVals c ρ t v
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨v, hv, -⟩ := (d1.1 b).mp hb
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨elemOf c I v, (d1.1 _).mpr ⟨v, hv, ((elemOf_spec hI (d1.2 v hv) e).1 _).mpr rfl⟩⟩
  | .and p q, ht, hap, a => by
    simp only [typed, Bool.and_eq_true] at ht
    rw [kore, KoreAML.tr]
    simp only [KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, den p ht.1 hap.1 a, den q ht.2 hap.2 a]
    constructor
    · rintro ⟨⟨hq, hp⟩, -, hq'⟩
      exact ⟨hq, hp, hq'⟩
    · rintro ⟨hq, hp, hq'⟩
      exact ⟨⟨hq, hp⟩, hq, hq'⟩
  | .top, _, _, a => by
    have hD := defOK hI
    have hQv : ∀ b, (KoreAML.trSort tbl Q0).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "Q0")) :=
      fun b => by rw [trSort_Q0, KoreAML.interp_evar]
    rw [kore, KoreAML.tr,
      KoreAML.interp_sTop hD (by rw [trSort_Q0]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm),
      KoreAML.interp_inhOf_of hQv]
    simp [Holds]

end

end SvPred

/-! ## A sentence between two predicates over set variables -/

/-- A library sentence `lhs => rhs` between two predicates over the set variables `vars`. -/
structure SvEqn where
  vars : Vars
  lhs : SvPred
  rhs : SvPred

namespace SvEqn

/-- The pattern of the sentence's axiom, as kompile writes it over the sort variables `R`, `Q0`,
over the registry's names. -/
def patR (E : SvEqn) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0 KoreAML.R (E.lhs.kore E.vars) (.and Q0 [E.rhs.kore E.vars, .top Q0]))

/-- The keys of the set variables. -/
def keys (E : SvEqn) : List KoreAML.VarKey := (List.range E.vars.length).map (svKey E.vars)

/-- The variables are of registry sorts and the two sides are typed. -/
def typed (c : Semantics) (E : SvEqn) : Bool :=
  E.vars.all (fun p => decide (p.2 < nRegSorts)) && E.lhs.typed c E.vars && E.rhs.typed c E.vars

/-- The free variables of the pattern are exactly the set variables `vars`, which have distinct
places in the table of the sentence's axiom over `R`, `Q0`. -/
def regular (E : SvEqn) : Bool :=
  E.keys.all (fun k => (KoreAML.freeOf [] E.patR).contains k) &&
  (KoreAML.freeOf [] E.patR).all (fun k => match k with
    | .svar _ _ => E.keys.contains k
    | .evar _ _ => false
    | .sortVar _ => true) &&
  (List.range E.vars.length).all (fun i => (List.range E.vars.length).all (fun j =>
    i == j || (KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR).idxOf (svKey E.vars i) !=
      (KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR).idxOf (svKey E.vars j)))

/-- `ρ` gives each variable values of its sort. -/
def Sorted (c : Semantics) (vars : Vars) (ρ : Nat → GroundTerm → Prop) : Prop :=
  ∀ i p, vars[i]? = some p → ∀ v, ρ i v → c.sortOf v = some p.2

/-- Each variable holds at most one value. -/
def AtMostOne (ρ : Nat → GroundTerm → Prop) : Prop := ∀ i v w, ρ i v → ρ i w → v = w

/-- The two sides hold at the same sets of values of the variables' sorts that meet `Adm`. -/
def Holds (c : Semantics) (E : SvEqn) (Adm : (Nat → GroundTerm → Prop) → Prop) : Prop :=
  ∀ ρ, Sorted c E.vars ρ → Adm ρ → (E.lhs.Holds c ρ ↔ E.rhs.Holds c ρ)

end SvEqn

/-- The values whose elements the valuation `e` gives the i-th set variable. -/
noncomputable def svRho (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M)
    (e : Valuation M) (t : KoreAML.VarTable) (vars : Vars) : Nat → GroundTerm → Prop :=
  fun i v => i < vars.length ∧ c.sortOf v = some (vars.getD i ("", 0)).2 ∧
    e.evalSvar (t.sv (svKey vars i)) (elemOf c I v)

/-- **The companion of a sentence over set variables**: `φ` holds in every model of `Γ c` at every
valuation that sends the free element variables of the axiom to values, its free set variables to
sets of elements of values, each of at most one element. -/
def SvAtMostOne (c : Semantics) (ad : KoreAML.AxiomDecl) (φ : KoreAML.P) : Prop :=
  ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c →
    ∀ e, AtValues c I e ad.ax → SetVarsAtValues c I e ad.ax → SetVarsAtMostOne e ad.ax → ∀ m, φ.interpret I e m

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The body of the sentence.** In a model of `Γ c`, at a valuation whose i-th set variable holds
the elements of the values `ρ i` and that gives `R` and `Q0` sorts, the translated pattern holds
an element of `R` exactly where, at every element of `Q0`, the two sides agree. -/
theorem SvEqn.body (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) (E : SvEqn) (ht : E.typed c = true)
    (hap : E.lhs.Apart c ∧ E.rhs.Apart c) {ρ : Nat → GroundTerm → Prop} {t : KoreAML.VarTable}
    {e : Valuation M} (hρ : SvEqn.Sorted c E.vars ρ)
    (hag : ∀ i, i < E.vars.length → ∀ m,
      e.evalSvar (t.sv (svKey E.vars i)) m ↔ ∃ v, ρ i v ∧ (den c v).interpret I e m)
    (hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))))
    (hQ : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "Q0")))) (a : M) :
    (KoreAML.tr ⟨t, []⟩ E.patR).interpret I e a ↔
      KoreAML.Inh I (e.evalEvar (t.ev (.sortVar "R"))) a ∧
        ∀ b, KoreAML.Inh I (e.evalEvar (t.ev (.sortVar "Q0"))) b → (E.lhs.Holds c ρ ↔ E.rhs.Holds c ρ) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [SvEqn.typed, Bool.and_eq_true] at ht
  obtain ⟨⟨-, htl⟩, htr⟩ := ht
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hQv : ∀ b, (KoreAML.trSort t Q0).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "Q0")) :=
    fun b => by rw [trSort_Q0, KoreAML.interp_evar]
  unfold SvEqn.patR
  rw [KoreAML.tr, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hRv, KoreAML.tr,
    KoreAML.interp_sTop hD (by rw [trSort_R]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm),
    KoreAML.interp_inhOf_of hRv, KoreAML.tr, KoreAML.interp_sEquals hD hc hQv hRv hQ hR]
  have hden := fun (p : SvPred) (hp : p.typed c E.vars = true) (hpa : p.Apart c) =>
    SvPred.den h hI hρ hag hQ p hp hpa
  have hrhs : ∀ b, (KoreAML.tr ⟨t, []⟩ (.and Q0 [E.rhs.kore E.vars, .top Q0])).interpret I e b ↔
      KoreAML.Inh I (e.evalEvar (t.ev (.sortVar "Q0"))) b ∧ E.rhs.Holds c ρ := by
    intro b
    rw [KoreAML.tr]
    simp only [KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, hden _ htr hap.2 b, KoreAML.tr,
      KoreAML.interp_sTop hD (by rw [trSort_Q0]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm),
      KoreAML.interp_inhOf_of hQv]
    exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, hx.1⟩⟩
  simp only [hden _ htl hap.1, hrhs]
  constructor
  · rintro ⟨ha, hk⟩
    obtain ⟨-, hall⟩ := hk ha
    exact ⟨ha, fun b hb => ⟨fun hl => ((hall b hb).mp ⟨hb, hl⟩).2, fun hr => ((hall b hb).mpr ⟨hb, hr⟩).2⟩⟩
  · rintro ⟨ha, hall⟩
    refine ⟨ha, fun _ => ⟨ha, fun b hb => ?_⟩⟩
    have := hall b hb
    exact ⟨fun ⟨x, y⟩ => ⟨x, this.mp y⟩, fun ⟨x, y⟩ => ⟨x, this.mpr y⟩⟩

/-- At a valuation meeting `SetVarsAtValues`, the i-th set variable holds the elements of the
values `svRho`, which are of its sort. -/
theorem svRho_spec (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) (E : SvEqn) (hr : E.regular = true)
    (ht : E.typed c = true) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR) (e : Valuation M)
    (hsv : SetVarsAtValues c I e ad.ax) :
    SvEqn.Sorted c E.vars (svRho c I e (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern) E.vars) ∧
    ∀ i, i < E.vars.length → ∀ m,
      e.evalSvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).sv (svKey E.vars i)) m ↔
        ∃ v, svRho c I e (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern) E.vars i v ∧ (den c v).interpret I e m := by
  haveI : OvlOK c := ovlOK_of_core h
  obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
  simp only [SvEqn.typed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  have hvR := ht.1.1
  simp only [SvEqn.regular, Bool.and_eq_true, List.all_eq_true] at hr
  have hfree := hr.1.1
  refine ⟨fun i p hp v hv => ?_, fun i hi m => ?_⟩
  · have : E.vars.getD i ("", 0) = p := by rw [List.getD_eq_getElem?_getD, hp]; rfl
    rw [← this]; exact hv.2.1
  · have hpi : E.vars.getD i ("", 0) ∈ E.vars := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    have hs : (E.vars.getD i ("", 0)).2 < nRegSorts := hvR _ hpi
    constructor
    · intro hm
      have hk : svKey E.vars i ∈ (KoreAML.freeOf [] ad.ax.pattern).eraseDups := by
        rw [hp]
        exact List.mem_eraseDups.mpr (List.mem_of_elem_eq_true
          (hfree _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
      obtain ⟨v, S, hS, hvS, hden⟩ := hsv _ _ hk m hm
      rw [← srtOf_reg c hs] at hS
      have hSe : S = (E.vars.getD i ("", 0)).2 :=
        sort_eq_of_name hn (sortOf_numbered_ofCl hg hsn (Semantics.coreOK_ovls h) hvS)
          (Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)) (srt_inj hS)
      subst hSe
      have hme := ((elemOf_spec hI hvS e).1 m).mp hden
      subst hme
      exact ⟨v, ⟨hi, hvS, hm⟩, hden⟩
    · rintro ⟨v, ⟨-, hvS, hv⟩, hden⟩
      rw [((elemOf_spec hI hvS e).1 m).mp hden]
      exact hv

omit [Inhabited M] in
/-- The guards of the sort variables `R` and `Q0` give them sorts. -/
theorem sv_sortGuards {e : Valuation M} {m : M} (hI : I ⊧ᴵP Γ c) (ad : KoreAML.AxiomDecl)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    (hgd : (KoreAML.conjList ((ad.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ad.ax.pattern).eraseDups.map
      (KoreAML.guardOf (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern)))).interpret I e m) :
    KoreAML.IsSort I (e.evalEvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (.sortVar "R"))) ∧
    KoreAML.IsSort I (e.evalEvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (.sortVar "Q0"))) := by
  have hD := defOK hI
  refine ⟨(KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_cons_self ..)), rfl⟩)),
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "Q0",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by
        rw [hsv]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))), rfl⟩))⟩

/-- **A sentence over set variables whose sides hold at the same sets of values meeting `Adm`
holds** in every model of `Γ c`, at every valuation meeting `SetVarsAtValues` whose sets meet
`Adm`. -/
theorem SvEqn.entailed_gen (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) (E : SvEqn) (hr : E.regular = true)
    (ht : E.typed c = true) (hap : E.lhs.Apart c ∧ E.rhs.Apart c) (Adm : (Nat → GroundTerm → Prop) → Prop)
    (hE : E.Holds c Adm) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) (e : Valuation M) (hsvv : SetVarsAtValues c I e ad.ax)
    (hadm : Adm (svRho c I e (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern) E.vars)) (m : M) :
    (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  have hD := defOK hI
  obtain ⟨hρ, hag⟩ := svRho_spec h hI E hr ht ad hp e hsvv
  unfold KoreAML.trAxiom
  dsimp only
  rw [interpret_impl]
  intro hgd
  obtain ⟨hR, hQ⟩ := sv_sortGuards hI ad hsv hgd
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hρ hag hR hQ hadm ⊢
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [hp]
  simp only [SvEqn.patR, KoreAML.sortOf]
  rw [KoreAML.interp_inhOf_of hRv]
  have hb := SvEqn.body h hI E ht hap hρ hag hR hQ a
  unfold SvEqn.patR at hb
  rw [hb]
  exact ⟨fun hx => hx.1, fun ha => ⟨ha, fun _ _ => hE _ hρ hadm⟩⟩

/-- The free set variables of the sentence's axiom are its variables `vars`. -/
theorem sv_key_of_free (E : SvEqn) (hr : E.regular = true) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] E.patR) : (∃ n s, k = .svar n s) → ∃ i, i < E.vars.length ∧ k = svKey E.vars i := by
  rintro ⟨n, s, rfl⟩
  simp only [SvEqn.regular, Bool.and_eq_true, List.all_eq_true] at hr
  have := hr.1.2 _ hk
  simp only at this
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_of_elem_eq_true this)
  exact ⟨i, List.mem_range.mp hi, he.symm⟩

/-- The pattern has no free element variable. -/
theorem sv_no_evar (E : SvEqn) (hr : E.regular = true) {n : String} {s : Kore.KSort} :
    KoreAML.VarKey.evar n s ∉ KoreAML.freeOf [] E.patR := by
  intro hk
  simp only [SvEqn.regular, Bool.and_eq_true, List.all_eq_true] at hr
  have := hr.1.2 _ hk
  simp at this

/-- Two set variables of `vars` with one place in the table are one. -/
theorem sv_key_inj (E : SvEqn) (hr : E.regular = true) {i j : Nat} (hi : i < E.vars.length)
    (hj : j < E.vars.length)
    (he : (KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR).sv (svKey E.vars i) =
      (KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR).sv (svKey E.vars j)) : i = j := by
  simp only [SvEqn.regular, Bool.and_eq_true, List.all_eq_true] at hr
  have hnd := hr.2 i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
  have hidx : (KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR).idxOf (svKey E.vars i) =
      (KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR).idxOf (svKey E.vars j) := by
    unfold KoreAML.VarTable.sv KoreAML.VarTable.index at he
    have := congrArg SVar.val he
    simp only at this
    omega
  rw [hidx] at hnd
  simpa using hnd

/-- **`EntailsAtSetValues`, for a sentence over set variables whose sides hold at the same sets of
values.** -/
theorem SvEqn.entailed (h : c.coreOK = true) (E : SvEqn) (hr : E.regular = true) (ht : E.typed c = true)
    (hap : E.lhs.Apart c ∧ E.rhs.Apart c) (hE : E.Holds c (fun _ => True)) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    EntailsAtSetValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fun _ _ _ hI e _ hsvv m => SvEqn.entailed_gen h hI E hr ht hap _ hE ad hp hsv e hsvv trivial m

/-- **The companion, for a sentence over set variables whose sides hold at the same sets of at most
one value** of sorts whose distinct values are distinct elements. -/
theorem SvEqn.entailed_one (h : c.coreOK = true) (E : SvEqn) (hr : E.regular = true) (ht : E.typed c = true)
    (hap : E.lhs.Apart c ∧ E.rhs.Apart c) (hvap : ∀ p ∈ E.vars, apartSort c p.2 = true)
    (hE : E.Holds c SvEqn.AtMostOne) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    SvAtMostOne c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e _ hsvv hone m
  haveI : OvlOK c := ovlOK_of_core h
  obtain ⟨hok, hfa, -, -, hids⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -⟩ := faithCoreOK_parts hfa
  refine SvEqn.entailed_gen h hI E hr ht hap _ hE ad hp hsv e hsvv (fun i v w hv hw => ?_) m
  have hi : i < E.vars.length := hv.1
  have hk : svKey E.vars i ∈ (KoreAML.freeOf [] ad.ax.pattern).eraseDups := by
    simp only [SvEqn.regular, Bool.and_eq_true, List.all_eq_true] at hr
    rw [hp]
    exact List.mem_eraseDups.mpr (List.mem_of_elem_eq_true
      (hr.1.1 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
  have he := hone _ _ hk _ _ hv.2.2 hw.2.2
  have hpi : E.vars.getD i ("", 0) ∈ E.vars := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  exact values_apart hI hg (NamesApart.subsorts_trans_of hids hok) (hvap _ hpi) hv.2.1 hw.2.1 he

/-- **A sentence over set variables whose sides do not hold at the same sets of values `ρ` is
refuted at values**: in every model of `Γ c`, it fails at the valuation whose set variables hold
the elements of the values `ρ i` (and whose sort variables are Bool's sort), which meets
`AtValues` and `SetVarsAtValues`. -/
theorem SvEqn.refuted_at (h : c.coreOK = true) (E : SvEqn) (hr : E.regular = true) (ht : E.typed c = true)
    (hap : E.lhs.Apart c ∧ E.rhs.Apart c) (ρ : Nat → GroundTerm → Prop) (hρ : SvEqn.Sorted c E.vars ρ)
    (hn : ¬ (E.lhs.Holds c ρ ↔ E.rhs.Holds c ρ)) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  obtain ⟨idx, md, ⟨svs, pat, attrs⟩⟩ := ad
  simp only at hp hsv
  subst hp hsv
  have htyp := ht
  simp only [SvEqn.typed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at htyp
  have hvR := htyp.1.1
  obtain ⟨σB, hB1, hB2⟩ := sortSing hI (s := Srt.bool) (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _))
  let T := KoreAML.tableOf [KoreAML.Rv, Q0v] E.patR
  let e : Valuation M := ⟨fun _ => σB, fun X m => ∃ i, i < E.vars.length ∧ X = T.sv (svKey E.vars i) ∧
    ∃ v, ρ i v ∧ m = elemOf c I v⟩
  have hgetD : ∀ i, i < E.vars.length → E.vars[i]? = some (E.vars.getD i ("", 0)) := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hsort : ∀ i v, i < E.vars.length → ρ i v → c.sortOf v = some (E.vars.getD i ("", 0)).2 :=
    fun i v hi hv => hρ i _ (hgetD i hi) v hv
  have hreg : ∀ i, i < E.vars.length → (E.vars.getD i ("", 0)).2 < nRegSorts := fun i hi => by
    refine hvR _ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  have hag : ∀ i, i < E.vars.length → ∀ m,
      e.evalSvar (T.sv (svKey E.vars i)) m ↔ ∃ v, ρ i v ∧ (den c v).interpret I e m := by
    intro i hi m
    constructor
    · rintro ⟨j, hj, hX, v, hv, rfl⟩
      obtain rfl := sv_key_inj E hr hi hj hX
      exact ⟨v, hv, ((elemOf_spec hI (hsort i v hi hv) e).1 _).mpr rfl⟩
    · rintro ⟨v, hv, hm⟩
      exact ⟨i, hi, rfl, v, hv, ((elemOf_spec hI (hsort i v hi hv) e).1 m).mp hm⟩
  -- a free set variable of the pattern is the i-th of `vars`, and its sort is the i-th's
  have hfreeS : ∀ n s, KoreAML.VarKey.svar n s ∈ KoreAML.freeOf [] E.patR → ∀ m, e.evalSvar (T.sv (.svar n s)) m →
      ∃ j v, j < E.vars.length ∧ s = regSrtK (E.vars.getD j ("", 0)).2 ∧ ρ j v ∧ m = elemOf c I v := by
    intro n s hk m hm
    obtain ⟨i, hi, hki⟩ := sv_key_of_free E hr hk ⟨n, s, rfl⟩
    obtain ⟨j, hj, hX, v, hv, rfl⟩ := hm
    rw [hki] at hX
    obtain rfl := sv_key_inj E hr hi hj hX
    unfold svKey at hki
    injection hki with _ hs
    exact ⟨i, v, hi, hs, hv, rfl⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro n s hk
    exact absurd (List.mem_eraseDups.mp hk) (sv_no_evar E hr)
  · intro n s hk m hm
    obtain ⟨j, v, hj, hs, hv, rfl⟩ := hfreeS n s (List.mem_eraseDups.mp hk) m hm
    refine ⟨v, (E.vars.getD j ("", 0)).2, ?_, hsort j v hj hv, ((elemOf_spec hI (hsort j v hj hv) e).1 _).mpr rfl⟩
    rw [hs, srtOf_reg c (hreg j hj)]
  · intro hax
    unfold KoreAML.trAxiom at hax
    dsimp only at hax
    rw [interpret_impl] at hax
    have hgd := hax (KoreAML.interp_conjList fun w hw => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
      have hk' := List.mem_eraseDups.mp hk
      cases k with
      | sortVar n => exact (KoreAML.interp_guard_sortVar hD).mpr hB2
      | evar n s =>
        rcases List.mem_append.mp hk' with hs | hf
        · obtain ⟨_, -, hx⟩ := List.mem_map.mp hs; cases hx
        · exact absurd hf (sv_no_evar E hr)
      | svar n s =>
        have hf : KoreAML.VarKey.svar n s ∈ KoreAML.freeOf [] E.patR := by
          rcases List.mem_append.mp hk' with hs | hf
          · obtain ⟨_, -, hx⟩ := List.mem_map.mp hs; cases hx
          · exact hf
        unfold KoreAML.guardOf
        refine (KoreAML.interp_included hD).mpr fun a ha => ?_
        obtain ⟨j, v, hj, hs, hv, rfl⟩ := hfreeS n s hf a ha
        rw [hs, ← srtOf_reg c (hreg j hj), trSort_srtOf_twoT]
        exact (elemOf_spec hI (hsort j v hj hv) e).2)
    rw [KoreAML.interp_equal hD] at hgd
    have hRv : ∀ b, (KoreAML.trSort T KoreAML.R).interpret I e b ↔ b = σB :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    let a := elemOf c I (KCore.bool true)
    have hbool : c.sortOf (KCore.bool true) = some Srt.bool := rfl
    have ha : KoreAML.Inh I σB a :=
      (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hB1).mp (elemOf_spec hI hbool e).2
    have hpat := (hgd a).mpr (by
      simp only [SvEqn.patR, KoreAML.sortOf]
      exact (KoreAML.interp_inhOf_of hRv).mpr ha)
    have hb := (SvEqn.body h hI E ht hap hρ hag hB2 hB2 a).mp hpat
    exact hn (hb.2 a ha)

end

end LibEv

end KCore
