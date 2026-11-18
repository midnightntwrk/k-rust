import OpenRuleK
/-
  A user module of the package of `f2-examples/openrule.kompile.kore` (e2-open-rule: `and` an open
  generator without a law, `same(A, B) => A ==K B`, `rule <k> go => x & y </k>`), built against it
  by test/open-gen.sh. `and` has no law, so `OpenLaws` holds at every H (`openLaws_any`). For every
  H with `OpenTotal`, `<k> go </k>` has one successor (`go_one`): `<k> v </k>`, v the value of
  `x & y` under H. The text's rule is the one rule of the semantics (`rules_eq`); its right side has
  that value (`go_rhs`), and it has no other: the functions are deterministic, by the package's
  `fnHyp_defn` (`fnModel_of_fnHyp`). Also its instance at `lawHooks defn.sem H`.
-/
set_option autoImplicit false

namespace OpenRuleK.User
open KCore

def exp : Srt := 32
def kS : Sym := 383
def goS : Sym := 385
def xS : Sym := 386
def yS : Sym := 387
def andS : Sym := 389

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kS = "Lbl'-LT-'k'-GT-'" ∧ c.symName goS = "Lblgo" ∧
    c.symName xS = "Lblx" ∧ c.symName yS = "Lbly" ∧ c.symName andS = "Lbland" := by
  decide +kernel

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }

theorem params_eq : c.params = [andP] := by decide +kernel

/-- The one-item sequence `kseq(inj{Exp,KItem}(t), dotk)`. -/
def item (t : Term) : Term := .app kseq [.inj exp Srt.kitem t, .app dotk []]

/-- `<k> go => x & y </k>`, as the text writes it: the top cell with the counter cell a variable. -/
def ruleGo : Rule :=
  { vars := [Srt.counter]
    lhs := .app topLabel [.app kS [.app kseq [.app goS [], .app dotk []]], .var 0]
    req := none
    rhs := .app topLabel [.app kS [item (.app andS [.app xS [], .app yS []])], .var 0]
    ens := none
    prio := 50 }

/-- The semantics' one rule is the text's. -/
theorem rules_eq : c.rules = [ruleGo] := by kernel_rfl

theorem totalParams_nil : defn.totalParams = [] := by kernel_rfl

theorem hooksTotal (H : HookParams) : HooksTotal H := by
  unfold HooksTotal; rw [totalParams_nil]; exact ParamsTotal.nil

/-- `and` has no law: `OpenLaws` holds under every interpretation. -/
theorem openLaws_any (H : HookParams) : OpenLaws (c.withHooks H) := fun k hk _ => by
  have hk' : k = andP := by
    have : k ∈ c.params := hk
    rw [params_eq] at this; exact List.mem_singleton.mp this
  subst hk'
  exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []
/-- The counter cell at 0. -/
def cnt : GroundTerm := .ctor counterLabel [int 0]
/-- `<k> go </k>`. -/
def goV : GroundTerm := .ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]
/-- `<k> v </k>`, v a value of Exp. -/
def afterV (v : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]], cnt]

theorem go_rawFree : c.rawFree goV = true ∧ c.sortOf goV = some topCellSort ∧
    c.rawFree cnt = true ∧ c.sortOf cnt = some Srt.counter ∧
    c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree yV = true ∧ c.sortOf yV = some exp := by
  decide +kernel

/-- `<k> go </k>` as a configuration under H. -/
def goCfg (H : HookParams) : Config (c.withHooks H) :=
  ⟨goV, (Semantics.sortOf_withHooks_rawFree c H go_rawFree.1).trans go_rawFree.2.1⟩

theorem and_mem (H : HookParams) : andP ∈ (c.withHooks H).params := by
  show andP ∈ c.params; rw [params_eq]; exact List.mem_singleton_self _

theorem sorts_xy (H : HookParams) : (c.withHooks H).sortsOf [xV, yV] = some [exp, exp] :=
  OvlLaws.sortsOf_cons_iff.mpr
    ⟨(Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.2.2.1).trans go_rawFree.2.2.2.2.2.1,
     OvlLaws.sortsOf_cons_iff.mpr
      ⟨(Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.2.2.2.2.1).trans go_rawFree.2.2.2.2.2.2.2, rfl⟩⟩

/-- The rule's right side under a σ that gives the counter cell: `<k> v </k>`, v the value of
`x & y`. -/
theorem go_rhs (H : HookParams) {v : GroundTerm} (hv : (c.withHooks H).paramVal andS [xV, yV] = some v)
    {σ : Subst} (h0 : σ.lookup 0 = some cnt) :
    EvalTerm (c.withHooks H) σ ruleGo.rhs (some (afterV v)) := by
  have hx : EvalTerm (c.withHooks H) σ (.app xS []) (some xV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor xS = true by decide +kernel) .nil
  have hy : EvalTerm (c.withHooks H) σ (.app yS []) (some yV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor yS = true by decide +kernel) .nil
  have hand : EvalTerm (c.withHooks H) σ (.app andS [.app xS [], .app yS []]) (some v) :=
    EvalTerm.param (rs := [some xV, some yV]) (show c.isCtor andS = false by decide +kernel)
      (by decide +kernel) (show c.isParam andS = true by decide +kernel) (.cons hx (.cons hy .nil)) hv.symm
  have hinj : EvalTerm (c.withHooks H) σ (.inj exp Srt.kitem (.app andS [.app xS [], .app yS []]))
      (some (injNormal exp Srt.kitem v)) := EvalTerm.inj hand
  have hdot : EvalTerm (c.withHooks H) σ (.app dotk []) (some (.ctor dotk [])) :=
    EvalTerm.ctor (rs := []) (show c.isCtor dotk = true by decide +kernel) .nil
  have hseq : EvalTerm (c.withHooks H) σ (item (.app andS [.app xS [], .app yS []]))
      (some (.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []])) :=
    EvalTerm.ctor (rs := [some (injNormal exp Srt.kitem v), some (.ctor dotk [])])
      (show c.isCtor kseq = true by decide +kernel) (.cons hinj (.cons hdot .nil))
  have hk : EvalTerm (c.withHooks H) σ (.app kS [item (.app andS [.app xS [], .app yS []])])
      (some (.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]])) :=
    EvalTerm.ctor (rs := [some (.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []])])
      (show c.isCtor kS = true by decide +kernel) (.cons hseq .nil)
  have hvar : EvalTerm (c.withHooks H) σ (.var 0) (some cnt) := h0 ▸ EvalTerm.var
  exact EvalTerm.ctor (rs := [some (.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]]), some cnt])
    (show c.isCtor topLabel = true by decide +kernel) (.cons hk (.cons hvar .nil))

/-- A match of the rule's left side at `<k> go </k>` gives the counter cell to its variable. -/
theorem go_match (H : HookParams) {σ : Subst} (hm : PatVal (c.withHooks H) σ ruleGo.lhs goV) :
    σ.lookup 0 = some cnt := by
  have hm' : PatVal (c.withHooks H) σ
      (.app topLabel [.app kS [.app kseq [.app goS [], .app dotk []]], .var 0])
      (.ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]) := hm
  have hct : (c.withHooks H).isCtor topLabel = true := show c.isCtor topLabel = true by decide +kernel
  cases hm' with
  | ctor _ hs =>
    cases hs with
    | cons _ hs2 =>
      cases hs2 with
      | cons h2 _ =>
        cases h2 with
        | var h => exact h
  | hook hp _ _ => exact absurd hp (by decide +kernel)
  | coll hc _ _ _ => rw [hct] at hc; cases hc
  | ovl hc _ _ _ => rw [hct] at hc; cases hc

/-- **For every H with `OpenTotal`, `<k> go </k>` has one successor**: `<k> v </k>`, v the value
of `x & y` under H. -/
theorem go_one (H : HookParams) (ht : OpenTotal (c.withHooks H)) :
    ∃ y : Config (c.withHooks H), ∀ y', Step (c.withHooks H) (goCfg H) y' ↔ y' = y := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht andP (and_mem H) rfl [xV, yV] (sorts_xy H))
  have hc : (c.withHooks H).coreOK = true := coreOK_withHooks_defn H
  have hd := (fnModel_of_fnHyp hc (fnHyp_defn H (openLaws_any H) ht (hooksTotal H))).1
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core hc
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hcnt : (c.withHooks H).sortOf cnt = some Srt.counter :=
    (Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.1).trans go_rawFree.2.2.2.1
  have hσ : (c.withHooks H).WellSorted ruleGo.vars [(0, cnt)] := fun i s hs => by
    match i, hs with
    | 0, hs => exact ⟨cnt, rfl, by cases hs; exact hcnt⟩
    | i + 1, hs => simp [ruleGo] at hs
  have he := go_rhs H hv (σ := [(0, cnt)]) rfl
  have hsort : (c.withHooks H).sortOf (afterV v) = some topCellSort :=
    EvalTerm.sorted hsc he (L := (c.withHooks H).fns.map Fn.sig) (headsOK_fns _) hσ
      (show sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) ruleGo.vars ruleGo.rhs = some topCellSort by
        decide +kernel) rfl
  have hmem : ruleGo ∈ (c.withHooks H).rules := by
    show ruleGo ∈ c.rules; rw [rules_eq]; exact List.mem_singleton_self _
  refine ⟨⟨afterV v, hsort⟩, fun y' => ⟨fun hs => ?_, fun e => ?_⟩⟩
  · cases hs with
    | rule r mem σ _ hmatch _ _ heval _ _ _ =>
      have hr : r = ruleGo := by
        have : r ∈ c.rules := mem
        rw [rules_eq] at this; exact List.mem_singleton.mp this
      subst hr
      exact Subtype.ext (Option.some.inj
        (EvalTerm.functional_of_fnDet hd heval (go_rhs H hv (go_match H hmatch))))
  · subst e
    have hct : ∀ f, c.isCtor f = true → (c.withHooks H).isCtor f = true := fun _ h => h
    refine Step.rule ruleGo hmem [(0, cnt)] hσ ?_ (fun _ h => by cases h) .top he
      (fun _ h => by cases h) .top (fun r' hr' hlt => ?_)
    · exact PatVal.ctor (hct _ (by decide +kernel))
        (.cons (PatVal.ctor (hct _ (by decide +kernel))
          (.cons (PatVal.ctor (hct _ (by decide +kernel))
            (.cons (PatVal.ctor (hct _ (by decide +kernel)) .nil)
              (.cons (PatVal.ctor (hct _ (by decide +kernel)) .nil) .nil))) .nil))
          (.cons (PatVal.var rfl) .nil))
    · have hr : r' = ruleGo := by
        have : r' ∈ c.rules := hr'
        rw [rules_eq] at this; exact List.mem_singleton.mp this
      subst hr
      exact absurd hlt (Nat.lt_irrefl _)

/-- `go_one` at `lawHooks defn.sem H`, the obligation discharged. -/
theorem go_one_lawHooks (H : HookParams) :
    ∃ y : Config (c.withHooks (lawHooks defn.sem H)),
      ∀ y', Step (c.withHooks (lawHooks defn.sem H)) (goCfg (lawHooks defn.sem H)) y' ↔ y' = y :=
  go_one (lawHooks defn.sem H) (openTotal_lawHooks_defn H)

end OpenRuleK.User

#print axioms OpenRuleK.User.go_one
#print axioms OpenRuleK.User.go_one_lawHooks
