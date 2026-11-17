/-
  `t #And u` on a rule's right side, read as `t` with the ensures `t == u`: a weakening the text
  entails, not an equality. Run from the package root: `lake env lean -j1 test/RuleAndWeaken.lean`.

  The text's sentence is `L → •r` with `r = C[t ∧ u]`; the reading's is `(L ∧ ⌈R'⌉) → •R'` with
  `R' = C[t] ∧ (E = T)` (`gamRule`, whose right side `ensRight` is `ruleRight`'s for a rule with an
  `ensures`, no existential variable and a `\top` post: `ruleRight_ens`, `prioRuleK_ens`).
  - `rewrites_weaken`, `denB_rule_and_weaken`: every element of the text's sentence is an element
    of the reading's, in every interpretation of definedness and of the definedness symbols in
    which the two sorts denote sorts and `r` lies inside the rule's sort and inside `C[t]`.
    Nothing is asked of `t`, `u`, `E` or `T`.
  - The interpretation `J hk` of the rule `k(X) => k(f(X) #And g(X))`, X of Int: Int holds `one`
    and `e`, `f(x) = {one, e}`, `g(x) = {one}`, so the conjuncts meet and one has two elements;
    `eqInt(e, one)` is `tt` where `hk` and `ff` otherwise. `text_at`, `gam_at`: the lemma's
    instance at `k(one)`. With `hk = true` (`strict_left`, `strict_step`, `strict_more`): the
    reading's right side is `k(f(X))`, which holds `k(e)` where the text's does not, so the two
    right sides are not equal. With `hk = false` (`exact_right_empty`, `exact_left_fails`,
    `exact_text_step`): the reading's right side is empty and its sentence says nothing at
    `k(one)`, where the text's gives a successor. `left_forces`: a valuation whose `k(X)` holds
    `k(one)` gives X the element `one`.
  - `hoist_sub`, `hoistList_sub`: for every KORE pattern p, every element of p is an element of
    the pattern `Parse.hoist` returns for it (argument by argument for an application), at every
    table and valuation, in every interpretation of definedness. So the inclusion `hsub` of the
    two lemmas holds for every right side the reader reads (`rewrites_weaken_hoist`,
    `denB_rule_and_weaken_hoist`; `gam_at_hoist` at the instance). No alias is excluded: an
    application of an alias has one pattern on both sides.
  - `rewrites_weaken_left`, `prioRuleK_and_weaken`: the same entailment into `prioRuleK c r`
    itself, whose left side is the flat `\and` of the rule's left side, its `requires`, the
    conjuncts of `pre`, the competitors' negation where a rule has a smaller priority number, and
    `⌈R'⌉`; the text's two sides are taken in the rule's variable names.
  Not covered: a rule with an existential variable (`ruleRight` then stands under `\exists`, and
  where the variable is first met in the second conjunct the two sentences' tables are a
  permutation of each other); that the reader's right side, written back with `canonVars`' names,
  is `hoist` of the text's (`hrhs`, a hypothesis); the inclusion of the read left side in the
  text's (`hl`, a hypothesis).
-/
import KcoreSpec

set_option autoImplicit false

namespace RuleAndWeaken

open ML KoreAML

/-- The right side of the reading: `t' ∧ \equals{B,C}(E, T)`. -/
def ensRight (C B : Kore.KSort) (t' E T : Kore.Pattern) : Kore.Pattern :=
  .and C [t', .equals B C E T]

/-- The rule of the reading, in `prioRuleK`'s form without competitors:
`\rewrites{C}(\and{C}(l, \ceil{C,C}(right)), right)`. -/
def gamRule (C B : Kore.KSort) (l t' E T : Kore.Pattern) : Kore.Pattern :=
  .rewrites C (.and C [l, .ceil C C (ensRight C B t' E T)]) (ensRight C B t' E T)

section lemma
variable {M : Type} {I : Interpretation Sym M}

/-- The monotonicity, at one table and one valuation. -/
theorem rewrites_weaken [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {cx : Ctx} {C B : Kore.KSort} {l r t' E T : Kore.Pattern} {e : Valuation M} {σC σB : M}
    (hSC : ∀ a, (trSort cx.vars C).interpret I e a ↔ a = σC)
    (hSB : ∀ a, (trSort cx.vars B).interpret I e a ↔ a = σB)
    (hσC : IsSort I σC) (hσB : IsSort I σB)
    (hsub : ∀ b, (tr cx r).interpret I e b → (tr cx t').interpret I e b)
    (hin : ∀ b, (tr cx r).interpret I e b → Inh I σC b)
    {m : M} (h : (tr cx (.rewrites C l r)).interpret I e m) :
    (tr cx (gamRule C B l t' E T)).interpret I e m := by
  have h' : (sRewrites (trSort cx.vars C) (tr cx l) (tr cx r)).interpret I e m := by
    simpa only [tr] using h
  have goal' : (sRewrites (trSort cx.vars C)
      (sAnd (tr cx l) (sCeil (trSort cx.vars C) (trSort cx.vars C)
        (sAnd (tr cx t') (sEquals (trSort cx.vars B) (trSort cx.vars C) (tr cx E) (tr cx T)))))
      (sAnd (tr cx t') (sEquals (trSort cx.vars B) (trSort cx.vars C) (tr cx E) (tr cx T)))).interpret I e m := by
    unfold sRewrites at h' ⊢
    rw [interp_sImp] at h' ⊢
    refine ⟨h'.1, fun hl => ?_⟩
    rw [interp_sAnd] at hl
    obtain ⟨hl1, hceil⟩ := hl
    obtain ⟨_, _, x, _, _, hx, _⟩ := interp_sCeil_raw.mp hceil
    rw [interp_sAnd] at hx
    have heq := (interp_sEquals hD hc hSB hSC hσB hσC x).mp hx.2
    have hn := h'.2 hl1
    unfold sNext at hn ⊢
    rw [interp_app] at hn ⊢
    obtain ⟨a, b, ha, hb, hab⟩ := hn
    exact ⟨a, b, ha, interp_sAnd.mpr ⟨hsub b hb,
      (interp_sEquals hD hc hSB hSC hσB hσC b).mpr ⟨hin b hb, heq.2⟩⟩, hab⟩
  simpa only [gamRule, ensRight, tr, trAndList] using goal'

/-- **The monotonicity over `denB`.** Where the two sentences have one table (the left side holds
every variable), every element of the text's sentence is an element of the reading's. -/
theorem denB_rule_and_weaken [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {C B : Kore.KSort} {l r t' E T : Kore.Pattern} {e : Valuation M} {σC σB : M}
    (htab : tableOf [] (gamRule C B l t' E T) = tableOf [] (.rewrites C l r))
    (hSC : ∀ a, (trSort (tableOf [] (.rewrites C l r)) C).interpret I e a ↔ a = σC)
    (hSB : ∀ a, (trSort (tableOf [] (.rewrites C l r)) B).interpret I e a ↔ a = σB)
    (hσC : IsSort I σC) (hσB : IsSort I σB)
    (hsub : ∀ b, (tr ⟨tableOf [] (.rewrites C l r), []⟩ r).interpret I e b →
      (tr ⟨tableOf [] (.rewrites C l r), []⟩ t').interpret I e b)
    (hin : ∀ b, (tr ⟨tableOf [] (.rewrites C l r), []⟩ r).interpret I e b → Inh I σC b)
    {m : M} (h : (denB (.rewrites C l r)).interpret I e m) :
    (denB (gamRule C B l t' E T)).interpret I e m := by
  unfold denB at h ⊢
  rw [htab]
  exact rewrites_weaken (cx := ⟨tableOf [] (.rewrites C l r), []⟩) hD hc hSC hSB hσC hσB hsub hin h

end lemma

/-! ## An instance

The rule `k(X) => k(f(X) #And g(X))`, X of sort Int. Int holds `one` (a value's element) and `e`
(no value's); `f(x) = {one, e}` and `g(x) = {one}` at both, so the conjuncts meet and one has two
elements. `eqInt(one, one) = tt`; `eqInt(e, one)` is `tt` where `hk`, `ff` otherwise (no sentence
of `Γ` names it: `e` is no value's element). `k(one)` and `k(e)` step to `k(one)`. -/

inductive El where
  | sS | sC | sB | sI
  | cdef | cinh | cceil | cnext | ck | cf | cg | ceq | cdv | junk
  | one | e | tt | ff | k1 | ke
  | ceil1 (s : El) | ceil2 (s s' : El) | eq1 (a : El)

instance : Inhabited El := ⟨.junk⟩

def inhP (s m : El) : Prop :=
  match s with
  | .sS => m = .sC ∨ m = .sB ∨ m = .sI
  | .sC => m = .k1 ∨ m = .ke
  | .sB => m = .tt ∨ m = .ff
  | .sI => m = .one ∨ m = .e
  | _ => False

def app (hk : Bool) (f a m : El) : Prop :=
  match f with
  | .cdef => True
  | .cinh => inhP a m
  | .cceil => m = .ceil1 a
  | .ceil1 s => m = .ceil2 s a
  | .ceil2 _ s' => inhP s' m
  | .cnext => a = .k1 ∧ (m = .k1 ∨ m = .ke)
  | .ck => (a = .one ∧ m = .k1) ∨ (a = .e ∧ m = .ke)
  | .cf => (a = .one ∨ a = .e) ∧ (m = .one ∨ m = .e)
  | .cg => (a = .one ∨ a = .e) ∧ m = .one
  | .ceq => m = .eq1 a
  | .eq1 x => a = .one ∧ ((x = .one ∧ m = .tt) ∨ (x = .e ∧ ((hk = true ∧ m = .tt) ∨ (hk = false ∧ m = .ff))))
  | .cdv => a = .sB ∧ m = .tt
  | _ => False

def sortEl (n : String) : El :=
  if n = "SortCfg" then .sC else if n = "SortBool" then .sB else if n = "SortInt" then .sI else .junk

def symEl (n : String) : El :=
  if n = "k" then .ck else if n = "f" then .cf else if n = "g" then .cg
  else if n = "eqInt" then .ceq else .junk

def evS (s : Sym) (m : El) : Prop :=
  match s with
  | .defined => m = .cdef
  | .inh => m = .cinh
  | .sortSort => m = .sS
  | .sort n => m = sortEl n
  | .symbol n => m = symEl n
  | .ceil => m = .cceil
  | .next => m = .cnext
  | .dv _ => m = .cdv
  | _ => False

def J (hk : Bool) : Interpretation Sym El := ⟨evS, app hk⟩

theorem sortEl_C : sortEl "SortCfg" = .sC := by simp [sortEl]
theorem sortEl_B : sortEl "SortBool" = .sB := by simp [sortEl]
theorem symEl_k : symEl "k" = .ck := by simp [symEl]
theorem symEl_f : symEl "f" = .cf := by simp [symEl]
theorem symEl_g : symEl "g" = .cg := by simp [symEl]
theorem symEl_eq : symEl "eqInt" = .ceq := by simp [symEl]

section model
variable {hk : Bool}

theorem hD : DefOK (J hk) := fun _ _ => ⟨.cdef, rfl, trivial⟩

theorem inh_iff {σ m : El} : Inh (J hk) σ m ↔ inhP σ m := by
  constructor
  · rintro ⟨i, hi, h⟩
    have hi : i = .cinh := hi
    subst hi
    exact h
  · intro h
    exact ⟨.cinh, rfl, h⟩

theorem hc : (J hk) ⊧ᴵ ceilDefItem.pat := by
  intro ρ m
  unfold ceilDefItem
  dsimp only
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sCeil_raw, interp_inhOf]
  simp only [interp_evar]
  constructor
  · rintro ⟨σ, σ', x, rfl, rfl, rfl, c2, ⟨c1, ⟨h, hh, h1⟩, h2⟩, h3⟩
    have hh : h = .cceil := hh
    subst hh
    have h1 : c1 = .ceil1 _ := h1
    subst h1
    have h2 : c2 = .ceil2 _ _ := h2
    subst h2
    exact ⟨_, rfl, inh_iff.mpr h3⟩
  · rintro ⟨σ, rfl, h⟩
    exact ⟨_, _, _, rfl, rfl, rfl, .ceil2 _ _, ⟨.ceil1 _, ⟨.cceil, rfl, rfl⟩, rfl⟩, inh_iff.mp h⟩

theorem isC : IsSort (J hk) .sC := ⟨.sS, rfl, inh_iff.mpr (Or.inl rfl)⟩
theorem isB : IsSort (J hk) .sB := ⟨.sS, rfl, inh_iff.mpr (Or.inr (Or.inl rfl))⟩

/-! The patterns. -/

def Cs : Kore.KSort := .ctor ⟨⟨"SortCfg"⟩⟩ []
def Bs : Kore.KSort := .ctor ⟨⟨"SortBool"⟩⟩ []
def Is : Kore.KSort := .ctor ⟨⟨"SortInt"⟩⟩ []
def vX : Kore.Pattern := .var (.evar ⟨⟨⟨"X"⟩⟩, Is⟩)
def ap (n : String) (ps : List Kore.Pattern) : Kore.Pattern := .app ⟨⟨n⟩⟩ [] ps
def kl : Kore.Pattern := ap "k" [vX]
def kt : Kore.Pattern := ap "f" [vX]
def ku : Kore.Pattern := ap "g" [vX]
/-- the text's right side, `k(f(X) ∧ g(X))` -/
def kr : Kore.Pattern := ap "k" [.and Is [kt, ku]]
def kt' : Kore.Pattern := ap "k" [kt]
def kE : Kore.Pattern := ap "eqInt" [kt, ku]
def kT : Kore.Pattern := .dv Bs "true"
def text : Kore.Pattern := .rewrites Cs kl kr
def gam : Kore.Pattern := gamRule Cs Bs kl kt' kE kT

def x1 : P := .evar ⟨1⟩
def SC : P := sym (.sort "SortCfg")
def SB : P := sym (.sort "SortBool")
def PF : P := sym (.symbol "f") ⬝ x1
def PG : P := sym (.symbol "g") ⬝ x1
def PL : P := sym (.symbol "k") ⬝ x1
def PR : P := sym (.symbol "k") ⬝ sAnd PF PG
def PT' : P := sym (.symbol "k") ⬝ PF
def PE : P := sym (.symbol "eqInt") ⬝ PF ⬝ PG
def PT : P := sym (.dv "true") ⬝ SB
def PR' : P := sAnd PT' (sEquals SB SC PE PT)


theorem htab : tableOf [] gam = tableOf [] text := by decide
theorem tr_C : trSort (tableOf [] (Kore.Pattern.rewrites Cs kl kr)) Cs = SC := rfl
theorem tr_B : trSort (tableOf [] (Kore.Pattern.rewrites Cs kl kr)) Bs = SB := rfl
theorem tr_r : tr ⟨tableOf [] (Kore.Pattern.rewrites Cs kl kr), []⟩ kr = PR := by decide
theorem tr_t' : tr ⟨tableOf [] (Kore.Pattern.rewrites Cs kl kr), []⟩ kt' = PT' := by decide
theorem denB_text : denB text = sRewrites SC PL PR := by decide
theorem denB_gam : denB gam = sRewrites SC (sAnd PL (sCeil SC SC PR')) PR' := by decide

theorem hSC {ρ : Valuation El} (a : El) : SC.interpret (J hk) ρ a ↔ a = .sC := by
  show a = sortEl "SortCfg" ↔ _
  rw [sortEl_C]

theorem hSB {ρ : Valuation El} (a : El) : SB.interpret (J hk) ρ a ↔ a = .sB := by
  show a = sortEl "SortBool" ↔ _
  rw [sortEl_B]

theorem iApp1 {ρ : Valuation El} {n : String} (c : El) (hn : symEl n = c) {φ : P} {m : El} :
    (sym (.symbol n) ⬝ φ).interpret (J hk) ρ m ↔ ∃ b, φ.interpret (J hk) ρ b ∧ app hk c b m := by
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    have ha : a = symEl n := ha
    rw [ha, hn] at h
    exact ⟨b, hb, h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨c, b, hn.symm, hb, h⟩

theorem iT {ρ : Valuation El} {m : El} : PT.interpret (J hk) ρ m ↔ m = .tt := by
  unfold PT
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, _, h⟩
    have ha : a = .cdv := ha
    subst ha
    exact h.2
  · rintro rfl
    exact ⟨.cdv, .sB, rfl, (hSB _).mpr rfl, ⟨rfl, rfl⟩⟩

theorem inhC {m : El} (h : m = .k1 ∨ m = .ke) : Inh (J hk) .sC m := inh_iff.mpr h

variable {ρ : Valuation El} (hρ : ρ.evalEvar ⟨1⟩ = .one)
include hρ

theorem iF {m : El} : PF.interpret (J hk) ρ m ↔ (m = .one ∨ m = .e) := by
  unfold PF
  rw [iApp1 .cf symEl_f]
  constructor
  · rintro ⟨b, _, h⟩
    exact h.2
  · intro h
    exact ⟨.one, hρ.symm, Or.inl rfl, h⟩

theorem iG {m : El} : PG.interpret (J hk) ρ m ↔ m = .one := by
  unfold PG
  rw [iApp1 .cg symEl_g]
  constructor
  · rintro ⟨b, _, h⟩
    exact h.2
  · intro h
    exact ⟨.one, hρ.symm, Or.inl rfl, h⟩

theorem iL : PL.interpret (J hk) ρ .k1 := by
  unfold PL
  rw [iApp1 .ck symEl_k]
  exact ⟨.one, hρ.symm, Or.inl ⟨rfl, rfl⟩⟩

/-- The text's right side `k(f(X) ∧ g(X))` is `{k(one)}`. -/
theorem iR {m : El} : PR.interpret (J hk) ρ m ↔ m = .k1 := by
  unfold PR
  rw [iApp1 .ck symEl_k]
  constructor
  · rintro ⟨b, hb, h⟩
    rw [interp_sAnd] at hb
    have hb2 := (iG hρ).mp hb.2
    subst hb2
    rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · cases h
  · rintro rfl
    exact ⟨.one, interp_sAnd.mpr ⟨(iF hρ).mpr (Or.inl rfl), (iG hρ).mpr rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- `k(f(X))` is `{k(one), k(e)}`. -/
theorem iT' {m : El} : PT'.interpret (J hk) ρ m ↔ (m = .k1 ∨ m = .ke) := by
  unfold PT'
  rw [iApp1 .ck symEl_k]
  constructor
  · rintro ⟨b, _, h⟩
    rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨.one, (iF hρ).mpr (Or.inl rfl), Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨.e, (iF hρ).mpr (Or.inr rfl), Or.inr ⟨rfl, rfl⟩⟩

/-- `eqInt(f(X), g(X))`: `tt` from `(one, one)`, and from `(e, one)` what `hk` says. -/
theorem iE {m : El} : PE.interpret (J hk) ρ m ↔
    (m = .tt ∨ (hk = false ∧ m = .ff)) := by
  unfold PE
  rw [interp_app]
  constructor
  · rintro ⟨p, b, hp, _, h⟩
    rw [iApp1 .ceq symEl_eq] at hp
    obtain ⟨a, _, hpa⟩ := hp
    have hpa : p = .eq1 a := hpa
    subst hpa
    rcases h.2 with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  · rintro (rfl | ⟨h1, rfl⟩)
    · exact ⟨.eq1 .one, .one, (iApp1 .ceq symEl_eq).mpr ⟨.one, (iF hρ).mpr (Or.inl rfl), rfl⟩,
        (iG hρ).mpr rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨.eq1 .e, .one, (iApp1 .ceq symEl_eq).mpr ⟨.e, (iF hρ).mpr (Or.inr rfl), rfl⟩,
        (iG hρ).mpr rfl, rfl, Or.inr ⟨rfl, Or.inr ⟨h1, rfl⟩⟩⟩

/-- **The text's sentence at `k(one)`**, X being `one`: `k(one)` is in `k(X) → •k(f(X) ∧ g(X))`. -/
theorem text_at : (denB text).interpret (J hk) ρ .k1 := by
  rw [denB_text]
  unfold sRewrites
  rw [interp_sImp]
  refine ⟨(interp_inhOf_of hSC).mpr (inhC (Or.inl rfl)), fun _ => ?_⟩
  unfold sNext
  rw [interp_app]
  exact ⟨.cnext, .k1, rfl, (iR hρ).mpr rfl, rfl, Or.inl rfl⟩

/-- **The instance of the lemma**: the reading's sentence at `k(one)`, from the text's. -/
theorem gam_at : (denB gam).interpret (J hk) ρ .k1 :=
  denB_rule_and_weaken (σC := .sC) (σB := .sB) hD hc htab
    (fun a => by rw [tr_C]; exact hSC a) (fun a => by rw [tr_B]; exact hSB a) isC isB
    (fun b hb => by rw [tr_r] at hb; rw [tr_t']; exact (iT' hρ).mpr (Or.inl ((iR hρ).mp hb)))
    (fun b hb => by rw [tr_r] at hb; exact inhC (Or.inl ((iR hρ).mp hb)))
    (text_at hρ)

end model

/-! ### `hk = true`: the hook answers `tt` at `(e, one)`. The reading's right side is `k(f(X))`,
two elements, strictly more than the text's one; its premise holds at `k(one)`. -/

section strict
variable {ρ : Valuation El} (hρ : ρ.evalEvar ⟨1⟩ = .one)
include hρ

theorem strict_right {m : El} : PR'.interpret (J true) ρ m ↔ (m = .k1 ∨ m = .ke) := by
  unfold PR'
  rw [interp_sAnd, iT' hρ, interp_sEquals hD hc hSB hSC isB isC m]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, inhC h, fun a _ => ?_⟩
    rw [iE hρ, iT]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact h
      · cases h
    · exact Or.inl

/-- The premise of the reading's sentence holds at `k(one)`: the instance is not vacuous. -/
theorem strict_left : (sAnd PL (sCeil SC SC PR')).interpret (J true) ρ .k1 := by
  rw [interp_sAnd]
  refine ⟨iL hρ, ?_⟩
  rw [interp_sCeil hD hc hSC hSC isC isC (fun a ha => inhC ((strict_right hρ).mp ha))]
  exact ⟨⟨.k1, (strict_right hρ).mpr (Or.inl rfl)⟩, inhC (Or.inl rfl)⟩

/-- So the reading's sentence gives `k(one)` a successor in `{k(one), k(e)}`. -/
theorem strict_step : (sNext PR').interpret (J true) ρ .k1 := by
  have h := gam_at (hk := true) hρ
  rw [denB_gam] at h
  unfold sRewrites at h
  rw [interp_sImp] at h
  exact h.2 (strict_left hρ)

/-- `k(e)` is in the reading's right side and not in the text's: a weakening, not an equality. -/
theorem strict_more : PR'.interpret (J true) ρ .ke ∧ ¬ PR.interpret (J true) ρ .ke :=
  ⟨(strict_right hρ).mpr (Or.inr rfl), fun h => by cases (iR hρ).mp h⟩

end strict

/-! ### `hk = false`: the hook is the equality at every element. The reading's right side is
empty, its sentence says nothing at `k(one)`, and the text's gives `k(one)` the successor `k(one)`. -/

section exact
variable {ρ : Valuation El} (hρ : ρ.evalEvar ⟨1⟩ = .one)
include hρ

theorem exact_right_empty {m : El} : ¬ PR'.interpret (J false) ρ m := by
  unfold PR'
  rw [interp_sAnd, interp_sEquals hD hc hSB hSC isB isC m]
  rintro ⟨_, _, h⟩
  have := (h .ff (inh_iff.mpr (Or.inr rfl))).mp ((iE hρ).mpr (Or.inr ⟨rfl, rfl⟩))
  cases (iT).mp this

/-- The premise of the reading's sentence fails at `k(one)`. -/
theorem exact_left_fails : ¬ (sAnd PL (sCeil SC SC PR')).interpret (J false) ρ .k1 := by
  rw [interp_sAnd]
  rintro ⟨_, h⟩
  obtain ⟨_, _, x, _, _, hx, _⟩ := interp_sCeil_raw.mp h
  exact exact_right_empty hρ hx

/-- The text's sentence gives `k(one)` a successor in `k(f(X) ∧ g(X))`. -/
theorem exact_text_step : (sNext PR).interpret (J false) ρ .k1 := by
  have h := text_at (hk := false) hρ
  rw [denB_text] at h
  unfold sRewrites at h
  rw [interp_sImp] at h
  exact h.2 (iL hρ)

end exact

/-- A valuation whose `k(X)` holds `k(one)` gives X the element `one`: the rule's disjunct of the
closure at `k(one)` is read at no other X. -/
theorem left_forces {hk : Bool} {ρ : Valuation El} (h : PL.interpret (J hk) ρ .k1) :
    ρ.evalEvar ⟨1⟩ = .one := by
  unfold PL at h
  rw [iApp1 .ck symEl_k] at h
  obtain ⟨b, hb, h⟩ := h
  have hb : b = ρ.evalEvar ⟨1⟩ := hb
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · rw [← hb, h]
  · cases h


/-! ## The reading's right side is `ruleRight`'s -/

open KCore Faithful in
/-- **`ruleRight` of a rule with an `ensures`, no existential variable and a `\top` post is
`ensRight`**: its right-hand side and `\equals{Bool,C}(ens, true)` under one `\and`. -/
theorem ruleRight_ens (c : Semantics) (r : Rule) (E : Term) (hex : r.exs = []) (hpost : r.post = .top)
    (hens : r.ens = some E) :
    ruleRight c r = ensRight (srtOf c topCellSort) (srt "Bool") (Term.kore c (canonVars c r.vars) r.rhs)
      (Term.kore c (canonVars c r.vars) E) (.dv (srt "Bool") "true") := by
  simp only [ruleRight, ensRight, hex, hpost, hens, Cond.conj, Cond.isTop, ite_true, reqPat, Option.map_some,
    List.filterMap_nil, List.foldr_nil, List.append_nil]

open KCore Faithful in
/-- **`prioRuleK` of such a rule without a `requires`, with `\top` pre and no rule of a smaller
priority is `gamRule`** up to the flat `\and` of its left side: its right side is `ensRight`, and
its left side holds the rule's left side, `\top` for the absent `requires`, and `⌈ensRight⌉`. -/
theorem prioRuleK_ens (c : Semantics) (r : Rule) (E : Term) (hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) (hens : r.ens = some E) (hreq : r.req = none)
    (hcomp : c.rules.filter (·.prio < r.prio) = []) :
    prioRuleK c r =
      (let C := srtOf c topCellSort
       let right := ensRight C (srt "Bool") (Term.kore c (canonVars c r.vars) r.rhs)
         (Term.kore c (canonVars c r.vars) E) (.dv (srt "Bool") "true")
       .rewrites C (.and C [Term.kore c (canonVars c r.vars) r.lhs, .top C, .ceil C C right]) right) := by
  rw [prioRuleK_top hex hpre hpost]
  simp only [hcomp, hens, hreq, ensRight, reqPat, Option.map_some, Option.map_none, List.map_nil,
    List.isEmpty_nil, ite_true]


/-! ## Every right side `hoist` returns holds the text's right side

`Parse.hoist` is the reader's function on a right side: it lifts the conjunctions out of the
applications, keeps the first of two term conjuncts and reads `t ∨ ⊥` as t. -/

open KCore (Parse.hoist Parse.hoistList Parse.isTrueOf?)

section hoistSub
variable {M : Type} {I : Interpretation KoreAML.Sym M}

mutual
  /-- The variable `⊤_s` binds is not free in a sort's pattern. -/
  theorem trSort_topFree (t : VarTable) : ∀ s : Kore.KSort, (trSort t s).isFreeEvar topVar = false
    | .var α => by
      rw [trSort]
      simp only [Pattern.isFreeEvar]
      simp [VarTable.ev, VarTable.index, topVar]
    | .ctor C args => by
      rw [trSort]
      exact trSortApp_topFree t args _ rfl
  theorem trSortApp_topFree (t : VarTable) : ∀ (ss : List Kore.KSort) (acc : P),
      acc.isFreeEvar topVar = false → (trSortApp t acc ss).isFreeEvar topVar = false
    | [], acc, h => by rw [trSortApp]; exact h
    | s :: ss, acc, h => by
      rw [trSortApp]
      exact trSortApp_topFree t ss _ (by simp [Pattern.isFreeEvar, h, trSort_topFree t s])
end

/-- `⊥_s` has no element. -/
theorem sBot_empty (hD : DefOK I) {e : Valuation M} {s : P} (hs : s.isFreeEvar topVar = false) {m : M} :
    ¬ (sBot s).interpret I e m := by
  unfold sBot
  rw [interp_sNot, interp_sTop hD hs]
  exact fun h => h.1 h.2

mutual
  /-- **Every element of a pattern is an element of what `hoist` returns for it**, at every table,
  valuation and interpretation of definedness. An application of an alias has the same pattern
  on both sides (its arguments are not read), so nothing is asked of the aliases. -/
  theorem hoist_sub (hD : DefOK I) (cx : Ctx) (e : Valuation M) : ∀ (p : Kore.Pattern) (m : M),
      (tr cx p).interpret I e m → (tr cx (Parse.hoist p).1).interpret I e m
    | .app h ss ps, m, hm => by
      simp only [Parse.hoist]
      rw [tr] at hm ⊢
      split
      · rename_i ha; simp only [ha] at hm; exact hm
      · rename_i ha; simp only [ha] at hm
        exact hoistList_sub hD cx e ps _ _ (fun _ h => h) m hm
    | .or s [t, u], m, hm => by
      simp only [Parse.hoist]
      rw [tr, trOrList, trOrList, interp_sOr] at hm
      split
      · rcases hm.2 with h | h
        · exact hoist_sub hD cx e t m h
        · rw [tr] at h; exact absurd h (sBot_empty hD (trSort_topFree _ _))
      · rcases hm.2 with h | h
        · rw [tr] at h; exact absurd h (sBot_empty hD (trSort_topFree _ _))
        · exact hoist_sub hD cx e u m h
      · rw [tr, trOrList, trOrList, interp_sOr]; exact hm
    | .and s [t, u], m, hm => by
      simp only [Parse.hoist]
      rw [tr, trAndList, trAndList, interp_sAnd] at hm
      have iht := hoist_sub hD cx e t m hm.1
      have ihu := hoist_sub hD cx e u m hm.2
      split
      · exact iht
      · exact ihu
      · exact iht
    | .var _, m, hm | .string _, m, hm | .top _, m, hm | .bottom _, m, hm | .not _ _, m, hm
    | .implies _ _ _, m, hm | .iff _ _ _, m, hm | .exist _ _ _, m, hm | .forall _ _ _, m, hm
    | .mu _ _, m, hm | .nu _ _, m, hm | .ceil _ _ _, m, hm | .floor _ _ _, m, hm
    | .equals _ _ _ _, m, hm | .in _ _ _ _, m, hm | .next _ _, m, hm | .rewrites _ _ _, m, hm
    | .dv _ _, m, hm | .leftAssoc _ _ _, m, hm | .rightAssoc _ _ _, m, hm
    | .and _ [], m, hm | .and _ [_], m, hm | .and _ (_ :: _ :: _ :: _), m, hm
    | .or _ [], m, hm | .or _ [_], m, hm | .or _ (_ :: _ :: _ :: _), m, hm => by
      simp only [Parse.hoist]
      exact hm
  /-- The same for the arguments of an application, one by one: `trArgs` over `hoistList`'s
  patterns holds what it holds over the arguments, from any head that holds the first head. -/
  theorem hoistList_sub (hD : DefOK I) (cx : Ctx) (e : Valuation M) : ∀ (ps : List Kore.Pattern) (acc acc' : P),
      (∀ m, acc.interpret I e m → acc'.interpret I e m) → ∀ m,
      (trArgs cx acc ps).interpret I e m → (trArgs cx acc' (Parse.hoistList ps).1).interpret I e m
    | [], acc, acc', h, m, hm => by
      simp only [Parse.hoistList]
      rw [trArgs] at hm ⊢
      exact h m hm
    | p :: ps, acc, acc', h, m, hm => by
      rw [trArgs] at hm
      have ih := hoistList_sub hD cx e ps (acc ⬝ tr cx p) (acc' ⬝ tr cx (Parse.hoist p).1)
        (fun m hm => by
          rw [interp_app] at hm ⊢
          obtain ⟨a, b, ha, hb, hab⟩ := hm
          exact ⟨a, b, h a ha, hoist_sub hD cx e p b hb, hab⟩) m hm
      simp only [Parse.hoistList]
      generalize Parse.hoist p = x at ih ⊢
      generalize Parse.hoistList ps = y at ih ⊢
      rw [trArgs]
      exact ih
end

/-- The monotonicity with any conjuncts on the reading's left side: the reading's left side is
`\and{C}(ls ++ [⌈R'⌉])`, and every element of all of `ls` is an element of the text's left side
`l` (`hl`). -/
theorem rewrites_weaken_left [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {cx : Ctx} {C B : Kore.KSort} {l r t' E T : Kore.Pattern} {ls : List Kore.Pattern} {e : Valuation M}
    {σC σB : M}
    (hSC : ∀ a, (trSort cx.vars C).interpret I e a ↔ a = σC)
    (hSB : ∀ a, (trSort cx.vars B).interpret I e a ↔ a = σB)
    (hσC : IsSort I σC) (hσB : IsSort I σB)
    (hl : ∀ b, (∀ p ∈ ls, (tr cx p).interpret I e b) → (tr cx l).interpret I e b)
    (hsub : ∀ b, (tr cx r).interpret I e b → (tr cx t').interpret I e b)
    (hin : ∀ b, (tr cx r).interpret I e b → Inh I σC b)
    {m : M} (h : (tr cx (.rewrites C l r)).interpret I e m) :
    (tr cx (.rewrites C (.and C (ls ++ [.ceil C C (ensRight C B t' E T)])) (ensRight C B t' E T))).interpret I e m := by
  have h' : (sRewrites (trSort cx.vars C) (tr cx l) (tr cx r)).interpret I e m := by
    simpa only [tr] using h
  have hR : ∀ b, (tr cx (ensRight C B t' E T)).interpret I e b ↔
      (sAnd (tr cx t') (sEquals (trSort cx.vars B) (trSort cx.vars C) (tr cx E) (tr cx T))).interpret I e b :=
    fun b => by simp only [ensRight, tr, trAndList]
  have hgoal : tr cx (.rewrites C (.and C (ls ++ [.ceil C C (ensRight C B t' E T)])) (ensRight C B t' E T)) =
      sRewrites (trSort cx.vars C) (trAndList cx (trSort cx.vars C) (ls ++ [.ceil C C (ensRight C B t' E T)]))
        (tr cx (ensRight C B t' E T)) := by rw [tr, tr]
  rw [hgoal]
  unfold sRewrites at h' ⊢
  rw [interp_sImp] at h' ⊢
  refine ⟨h'.1, fun hl' => ?_⟩
  rw [KCore.Faithful.interp_trAndList (by simp)] at hl'
  have hceil := hl' (.ceil C C (ensRight C B t' E T)) (by simp)
  rw [tr] at hceil
  obtain ⟨_, _, x, _, _, hx, _⟩ := interp_sCeil_raw.mp hceil
  have hx' := (hR x).mp hx
  rw [interp_sAnd] at hx'
  have heq := (interp_sEquals hD hc hSB hSC hσB hσC x).mp hx'.2
  have hn := h'.2 (hl _ fun p hp => hl' p (List.mem_append_left _ hp))
  unfold sNext at hn ⊢
  rw [interp_app] at hn ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := hn
  exact ⟨a, b, ha, (hR b).mpr (interp_sAnd.mpr ⟨hsub b hb,
    (interp_sEquals hD hc hSB hSC hσB hσC b).mpr ⟨hin b hb, heq.2⟩⟩), hab⟩

/-- `rewrites_weaken` with the right side `hoist` returns: no hypothesis on the two right sides. -/
theorem rewrites_weaken_hoist [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {cx : Ctx} {C B : Kore.KSort} {l r E T : Kore.Pattern} {e : Valuation M} {σC σB : M}
    (hSC : ∀ a, (trSort cx.vars C).interpret I e a ↔ a = σC)
    (hSB : ∀ a, (trSort cx.vars B).interpret I e a ↔ a = σB)
    (hσC : IsSort I σC) (hσB : IsSort I σB)
    (hin : ∀ b, (tr cx r).interpret I e b → Inh I σC b)
    {m : M} (h : (tr cx (.rewrites C l r)).interpret I e m) :
    (tr cx (gamRule C B l (Parse.hoist r).1 E T)).interpret I e m :=
  rewrites_weaken hD hc hSC hSB hσC hσB (hoist_sub hD cx e r) hin h

/-- **`denB_rule_and_weaken` with the right side `hoist` returns**: its hypothesis `hsub` holds
for every right side the reader reads. -/
theorem denB_rule_and_weaken_hoist [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {C B : Kore.KSort} {l r E T : Kore.Pattern} {e : Valuation M} {σC σB : M}
    (htab : tableOf [] (gamRule C B l (Parse.hoist r).1 E T) = tableOf [] (.rewrites C l r))
    (hSC : ∀ a, (trSort (tableOf [] (.rewrites C l r)) C).interpret I e a ↔ a = σC)
    (hSB : ∀ a, (trSort (tableOf [] (.rewrites C l r)) B).interpret I e a ↔ a = σB)
    (hσC : IsSort I σC) (hσB : IsSort I σB)
    (hin : ∀ b, (tr ⟨tableOf [] (.rewrites C l r), []⟩ r).interpret I e b → Inh I σC b)
    {m : M} (h : (denB (.rewrites C l r)).interpret I e m) :
    (denB (gamRule C B l (Parse.hoist r).1 E T)).interpret I e m :=
  denB_rule_and_weaken hD hc htab hSC hSB hσC hσB (hoist_sub hD _ e r) hin h

open KCore Faithful in
/-- **The text's sentence entails `prioRuleK`'s**, whatever `prioRuleK` holds on its left side
beside the rule's left side and `requires` (the conjuncts of `pre`, the competitors' negation):
for a rule r with an `ensures`, no existential variable and a `\top` post, `l` and `rt` the
text's two sides in r's variable names, where r's right side is what `hoist` returns for `rt`
(`hrhs`) and r's left side with its `requires` lies inside `l` (`hl`), every element of
`\rewrites(l, rt)` is an element of `prioRuleK c r`, at one table and one valuation. -/
theorem prioRuleK_and_weaken [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {c : Semantics} {r : Rule} {E : Term} (hex : r.exs = []) (hpost : r.post = .top) (hens : r.ens = some E)
    {cx : Ctx} {l rt : Kore.Pattern} {e : Valuation M} {σC σB : M}
    (hSC : ∀ a, (trSort cx.vars (srtOf c topCellSort)).interpret I e a ↔ a = σC)
    (hSB : ∀ a, (trSort cx.vars (srt "Bool")).interpret I e a ↔ a = σB)
    (hσC : IsSort I σC) (hσB : IsSort I σB)
    (hl : ∀ b, (tr cx (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e b →
      (tr cx (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e b →
      (tr cx l).interpret I e b)
    (hrhs : Term.kore c (canonVars c r.vars) r.rhs = (Parse.hoist rt).1)
    (hin : ∀ b, (tr cx rt).interpret I e b → Inh I σC b)
    {m : M} (h : (tr cx (.rewrites (srtOf c topCellSort) l rt)).interpret I e m) :
    (tr cx (prioRuleK c r)).interpret I e m := by
  have hsub : ∀ b, (tr cx rt).interpret I e b →
      (tr cx (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e b := fun b hb => by
    rw [hrhs]; exact hoist_sub hD cx e rt b hb
  unfold prioRuleK
  simp only [ruleRight_ens c r E hex hpost hens]
  split
  · exact rewrites_weaken_left hD hc hSC hSB hσC hσB
      (fun b hb => hl b (hb _ (by simp)) (hb _ (by simp))) hsub hin h
  · rw [show ∀ (xs : List Kore.Pattern) (a b : Kore.Pattern), xs ++ [a, b] = (xs ++ [a]) ++ [b] from
      fun xs a b => by simp]
    exact rewrites_weaken_left hD hc hSC hSB hσC hσB
      (fun b hb => hl b (hb _ (by simp)) (hb _ (by simp))) hsub hin h
end hoistSub

/-! The instance: `hoist` of `k(f(X) ∧ g(X))` is `k(f(X))`, with the one condition that `f(X)` and
`g(X)` have one value. -/

theorem hoist_kr : (Parse.hoist kr).1 = kt' ∧ (Parse.hoist kr).2.2 = false := by
  simp [Parse.hoist, Parse.hoistList, Parse.isTrueOf?, kr, kt', kt, ku, ap, vX]

/-- `gam_at` with the right side `hoist` returns: no inclusion is given by hand. -/
theorem gam_at_hoist {hk : Bool} {ρ : Valuation El} (hρ : ρ.evalEvar ⟨1⟩ = .one) :
    (denB (gamRule Cs Bs kl (Parse.hoist kr).1 kE kT)).interpret (J hk) ρ .k1 :=
  denB_rule_and_weaken_hoist (σC := .sC) (σB := .sB) hD hc (by rw [hoist_kr.1]; exact htab)
    (fun a => by rw [tr_C]; exact hSC a) (fun a => by rw [tr_B]; exact hSB a) isC isB
    (fun b hb => by rw [tr_r] at hb; exact inhC (Or.inl ((iR hρ).mp hb)))
    (text_at hρ)

end RuleAndWeaken

#print axioms RuleAndWeaken.rewrites_weaken
#print axioms RuleAndWeaken.denB_rule_and_weaken
#print axioms RuleAndWeaken.text_at
#print axioms RuleAndWeaken.gam_at
#print axioms RuleAndWeaken.strict_left
#print axioms RuleAndWeaken.strict_step
#print axioms RuleAndWeaken.strict_more
#print axioms RuleAndWeaken.exact_right_empty
#print axioms RuleAndWeaken.exact_left_fails
#print axioms RuleAndWeaken.exact_text_step
#print axioms RuleAndWeaken.left_forces
#print axioms RuleAndWeaken.ruleRight_ens
#print axioms RuleAndWeaken.prioRuleK_ens
#print axioms RuleAndWeaken.hoist_sub
#print axioms RuleAndWeaken.denB_rule_and_weaken_hoist
#print axioms RuleAndWeaken.prioRuleK_and_weaken
#print axioms RuleAndWeaken.gam_at_hoist
