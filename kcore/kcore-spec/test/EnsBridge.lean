/-
  The two encodings of a rewrite rule's `ensures` that the reader used before `Rule.ens`, each
  related to the field (`Step.rule`'s `hens`). Run from the package root:
  `lake env lean test/EnsBridge.lean`.

  The text's rule is `\rewrites(lhs ∧ req, rhs ∧ (E = true))`; the reader now reads it as the rule
  with `ens := some E` (`Rule.ens`).

  - **B-guard** (`guardOf`, `guardSem`): the right side with its first injection into KItem t
    replaced by `Map:lookup(inj{Bool,KItem}(true) |-> t, inj{Bool,KItem}(E andBool true))`
    (`ensGuard`, `ensGuardFirst`), and no `ensures`. Where `Map:lookup`, `|->` and `_andBool_` are no
    constructors of the semantics, it gives the same steps as the field (`guard_step`), and each rule
    applies where its guarded rule does (`guard_notApplies`). The guard's two properties
    (`guard_true`, `guard_some`; `guard_none`, `guard_no_value`) are facts about `EvalTerm`: every
    evaluation rule is strict, so the guard may stand under any applications and injections.
  - **B-conj** (`conjOf`, `conjSem`): the `ensures` conjoined to the `requires` (`_andBool_` after the
    written one), and no `ensures`. Where `_andBool_` is no constructor:
    (1) `conj_step`: every step of the field is one of the conjunct reading, provided each rule's
        `ensures` has a result wherever the rule matches (`EnsDefined`: where every function has a result (`FnTerminates`) every
        well-sorted term has one, `evalTerm_total`); without it the conjunct `q andBool E` has no
        result where E has none, so a rule whose `requires` q is false would not be shown not to
        apply, and a rule of a larger priority would lose its step (`conj_step_needs_defined`);
    (2) `step_of_conj`: every step of the conjunct reading is one of the field where no rule with
        an `ensures` matches a value a rule of a larger priority matches (`Apart`);
    (3) `conj_notApplies`: a rule that does not apply does not apply in the conjunct reading
        (with its `ensures` defined, as (1));
    (4) `notApplies_of_conj`: where the conjunct reading's rule does not apply, at each match the
        `requires` fails or the `ensures` evaluates to something other than `true`.
  The evaluation and matching of a semantics do not read its rules (`evalTerm_rules`,
  `patVal_rules`), so the rule lists may be compared over one evaluation.
-/
import KcoreSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

open KCore

namespace EnsBridge

/-! ## The guard encoding -/

/-- `ensGuard C t`, `Map:lookup(inj{Bool,KItem}(true) |-> t, inj{Bool,KItem}(C andBool true))`, a
term of sort KItem when t is one: t's value where C evaluates to `true`, and no value where C
evaluates to anything else or has none. `|->`, `Map:lookup` and `_andBool_` are strict; `C andBool
true` is `true` exactly where C's value is `true` (`bool2`), and the lookup of any other key in the
one-entry map has no value. -/
def ensGuard (cond t : Term) : Term :=
  .app mapLookup [.app mapElem [.inj Srt.bool Srt.kitem (.dv Srt.bool (.bool true)), t],
    .inj Srt.bool Srt.kitem (.app boolAnd [cond, .dv Srt.bool (.bool true)])]

mutual
  /-- The term t with its first injection into KItem (`inj{A,KItem}(u)`, arguments from left to
  right), reached through applications and injections only, guarded by `cond` (`ensGuard`); none
  when t has no such subterm. -/
  def ensGuardFirst (cond : Term) : Term → Option Term
    | .inj a b u => if b == Srt.kitem then some (ensGuard cond (.inj a b u))
        else (ensGuardFirst cond u).map (.inj a b)
    | .app f ts => (ensGuardList cond ts).map (.app f)
    | _ => none
    termination_by structural t => t
  def ensGuardList (cond : Term) : List Term → Option (List Term)
    | [] => none
    | t :: ts => match ensGuardFirst cond t with
      | some t' => some (t' :: ts)
      | none => (ensGuardList cond ts).map (t :: ·)
    termination_by structural ts => ts
end

section GuardEval

variable {c : Semantics} {σ : Subst}

/-! ## Applications -/

/-- An application of an interpreted hook that is no constructor and has no silent point is
evaluated by `EvalTerm.hook`, by `hook`'s value. -/
theorem hook_inv {f : Sym} {ts : List Term} {r : Option GroundTerm} (hc : c.isCtor f = false)
    (hh : isHook f = true) (hk : silentKey f = false) (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ (∀ vs, allSome rs = some vs → hook f vs = some r) ∧
      (allSome rs = none → r = none) := by
  cases h with
  | ctor h' _ => rw [hc] at h'; cases h'
  | hook _ _ hts hh' hund =>
    exact ⟨_, hts, fun vs h => by rw [← Semantics.hookRes_of_notKey (c := c) hk]; exact hh' vs h, hund⟩
  | param _ hhk _ _ _ => rw [hh] at hhk; cases hhk
  | call _ hh' _ _ _ _ => rw [hh] at hh'; cases hh'
  | callUndef _ hh' _ _ _ => rw [hh] at hh'; cases hh'
  | ovl _ ho _ => rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | ovlFn _ ho => rw [(c.isOvl_parts ho).2.1] at hh; cases hh

/-- A two-argument application of an interpreted hook with no silent point: its arguments' results,
and the hook's value on them when both are defined, undefined otherwise. -/
theorem hook2_iff {f : Sym} {a b : Term} {r : Option GroundTerm} (hc : c.isCtor f = false)
    (hh : isHook f = true) (hk : silentKey f = false := by decide +kernel) :
    EvalTerm c σ (.app f [a, b]) r ↔ ∃ ra rb, EvalTerm c σ a ra ∧ EvalTerm c σ b rb ∧
      (match ra, rb with
       | some x, some y => hook f [x, y] = some r
       | _, _ => r = none) := by
  constructor
  · intro h
    obtain ⟨rs, hts, hv, hu⟩ := hook_inv hc hh hk h
    match rs, hts with
    | [ra, rb], .cons ha (.cons hb .nil) =>
      refine ⟨ra, rb, ha, hb, ?_⟩
      match ra, rb with
      | some x, some y => exact hv [x, y] rfl
      | none, _ => exact hu rfl
      | some _, none => exact hu rfl
  · rintro ⟨ra, rb, ha, hb, hr⟩
    refine EvalTerm.hook hc hh (.cons ha (.cons hb .nil)) ?_ ?_
    · intro vs hvs
      match ra, rb, hr, hvs with
      | some x, some y, hr, hvs =>
        change some [x, y] = some vs at hvs
        cases hvs; rw [Semantics.hookRes_of_notKey hk]; exact hr
      | none, _, _, hvs => change none = some vs at hvs; cases hvs
      | some _, none, _, hvs => change none = some vs at hvs; cases hvs
    · intro hn
      match ra, rb, hr, hn with
      | some x, some y, _, hn => change some [x, y] = none at hn; cases hn
      | none, _, hr, _ => exact hr
      | some _, none, hr, _ => exact hr

/-- An application whose arguments' results carry over to other arguments has the same result. -/
theorem app_congr {f : Sym} {ts ts' : List Term} {r : Option GroundTerm}
    (H : ∀ rs, EvalTerms c σ ts rs → EvalTerms c σ ts' rs) (h : EvalTerm c σ (.app f ts) r) :
    EvalTerm c σ (.app f ts') r := by
  cases h with
  | ctor h hts => exact .ctor h (H _ hts)
  | hook h hhk hts hh hund => exact .hook h hhk (H _ hts) hh hund
  | param h hhk hp hts hr => exact .param h hhk hp (H _ hts) hr
  | call h hh hts hvs hf hp => exact .call h hh (H _ hts) hvs hf hp
  | callUndef h hh hts hvs hp => exact .callUndef h hh (H _ hts) hvs hp
  | ovl h ho hts hnf => exact .ovl h ho (H _ hts) hnf
  | ovlFn h ho hts hvs hlo hcov hf => exact .ovlFn h ho (H _ hts) hvs hlo hcov hf

/-- The defined argument results of an application with a value. -/
theorem allSome_of_ne {rs : List (Option GroundTerm)} {g : List GroundTerm → GroundTerm}
    (h : (allSome rs).map g ≠ none) : ∃ vs, allSome rs = some vs := by
  cases hv : allSome rs with
  | none => rw [hv] at h; exact absurd rfl h
  | some vs => exact ⟨vs, rfl⟩

/-- An application with a value has defined arguments. -/
theorem app_args_of_ne {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (h : EvalTerm c σ (.app f ts) r) (hr : r ≠ none) :
    ∃ rs vs, EvalTerms c σ ts rs ∧ allSome rs = some vs := by
  cases h with
  | @ctor _ _ _ rs _ hts => obtain ⟨vs, hvs⟩ := allSome_of_ne hr; exact ⟨rs, vs, hts, hvs⟩
  | @hook _ _ _ rs _ _ _ hts _ hund =>
    cases hv : allSome rs with
    | none => exact absurd (hund hv) hr
    | some vs => exact ⟨rs, vs, hts, hv⟩
  | @param _ _ _ rs _ _ _ _ hts hr' =>
    cases hv : allSome rs with
    | none => rw [hr', hv] at hr; exact absurd rfl hr
    | some vs => exact ⟨rs, vs, hts, hv⟩
  | call _ _ hts hvs _ _ => exact ⟨_, _, hts, hvs⟩
  | callUndef _ _ _ _ _ => exact absurd rfl hr
  | @ovl _ _ _ rs _ _ hts => obtain ⟨vs, hvs⟩ := allSome_of_ne hr; exact ⟨rs, vs, hts, hvs⟩
  | ovlFn _ _ hts hvs => exact ⟨_, _, hts, hvs⟩

/-- An application with a value keeps it when its defined arguments' results carry over. -/
theorem app_congr_def {f : Sym} {ts ts' : List Term} {r : Option GroundTerm}
    (H : ∀ rs vs, EvalTerms c σ ts rs → allSome rs = some vs → EvalTerms c σ ts' rs)
    (h : EvalTerm c σ (.app f ts) r) (hr : r ≠ none) : EvalTerm c σ (.app f ts') r := by
  cases h with
  | @ctor _ _ _ rs h hts =>
    obtain ⟨vs, hvs⟩ := allSome_of_ne hr
    exact .ctor h (H _ _ hts hvs)
  | @hook _ _ _ rs _ h hhk hts hh hund =>
    cases hv : allSome rs with
    | none => exact absurd (hund hv) hr
    | some vs => exact .hook h hhk (H _ _ hts hv) hh hund
  | @param _ _ _ rs _ h hhk hp hts hr' =>
    cases hv : allSome rs with
    | none => rw [hr', hv] at hr; exact absurd rfl hr
    | some vs => exact .param h hhk hp (H _ _ hts hv) hr'
  | call h hh hts hvs hf hp => exact .call h hh (H _ _ hts hvs) hvs hf hp
  | callUndef _ _ _ _ _ => exact absurd rfl hr
  | @ovl _ _ _ rs h ho hts hnf =>
    obtain ⟨vs, hvs⟩ := allSome_of_ne hr
    exact .ovl h ho (H _ _ hts hvs) hnf
  | ovlFn h ho hts hvs hlo hcov hf => exact .ovlFn h ho (H _ _ hts hvs) hvs hlo hcov hf

/-- An application whose arguments' results give other arguments with an undefined result is
undefined with those (every evaluation rule is strict). -/
theorem app_none {f : Sym} {ts ts' : List Term} {r : Option GroundTerm}
    (H : ∀ rs, EvalTerms c σ ts rs → ∃ rs', EvalTerms c σ ts' rs' ∧ allSome rs' = none)
    (h : EvalTerm c σ (.app f ts) r) : EvalTerm c σ (.app f ts') none := by
  cases h with
  | ctor h hts =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    have := EvalTerm.ctor (σ := σ) h hts'; rwa [hn] at this
  | hook h hhk hts _ _ =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    exact .hook h hhk hts' (fun vs hv => by rw [hn] at hv; cases hv) (fun _ => rfl)
  | param h hhk hp hts _ =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    exact .param h hhk hp hts' (by rw [hn]; rfl)
  | call h hh hts _ _ hp =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    exact .callUndef h hh hts' hn hp
  | callUndef h hh hts _ hp =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    exact .callUndef h hh hts' hn hp
  | ovl h ho hts =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    have := EvalTerm.ovl (σ := σ) h ho hts' (fun vs hv => by rw [hn] at hv; cases hv); rwa [hn] at this
  | ovlFn h ho hts =>
    obtain ⟨rs', hts', hn⟩ := H _ hts
    exact .callUndef h (c.isOvl_parts ho).2.1 hts' hn (c.isOvl_parts ho).2.2.1

/-! ## The guard -/

theorem hook_elem (x y : GroundTerm) : hook mapElem [x, y] = some (some (.map Srt.map [(x, y)])) := rfl
theorem hook_lookup (es : List (GroundTerm × GroundTerm)) (k : GroundTerm) :
    hook mapLookup [.map Srt.map es, k] = some (findK k es) := rfl
theorem asBool_bool (x : Bool) : asBool (KCore.bool x) = some x := rfl

theorem hook_and (v : GroundTerm) : hook boolAnd [v, KCore.bool true] = some ((asBool v).map KCore.bool) := by
  show some (bool2 [v, KCore.bool true] (· && ·)) = _
  cases hb : asBool v <;> simp [bool2, hb, asBool_bool]

theorem eq_of_asBool {v : GroundTerm} {x : Bool} (h : asBool v = some x) : v = KCore.bool x := by
  unfold asBool at h
  split at h
  · rename_i s b
    by_cases hs : (s == Srt.bool) = true
    · rw [if_pos hs] at h; cases h; rw [beq_iff_eq.mp hs]; rfl
    · rw [if_neg hs] at h; cases h
  · cases h

/-- The key: `C andBool true` injected into KItem. -/
abbrev keyOf (rc : Option GroundTerm) : Option GroundTerm :=
  (rc.bind fun v => (asBool v).map KCore.bool).map (injNormal Srt.bool Srt.kitem)

/-- The one-entry map: t's value under the key `true`. -/
abbrev mapOf (rt : Option GroundTerm) : Option GroundTerm :=
  rt.map fun w => .map Srt.map [(injNormal Srt.bool Srt.kitem (KCore.bool true), w)]

/-- The result the guard has, from C's and t's results: t's where C's is `true`, none otherwise. -/
theorem lookup_val (rc rt : Option GroundTerm) :
    (match mapOf rt, keyOf rc with
     | some x, some y => hook mapLookup [x, y]
     | _, _ => some none) = some (if rc = some (KCore.bool true) then rt else none) := by
  cases rc with
  | none => cases rt <;> rfl
  | some v =>
    cases hb : asBool v with
    | none =>
      have hv : v ≠ KCore.bool true := fun e => by rw [e, asBool_bool] at hb; cases hb
      cases rt <;> simp [hb, hv]
    | some x =>
      have hv := eq_of_asBool hb
      subst hv
      cases rt with
      | none => simp
      | some w =>
        cases x <;> rfl

theorem isHook_lookup : isHook mapLookup = true := rfl
theorem isHook_elem : isHook mapElem = true := rfl
theorem isHook_and : isHook boolAnd = true := rfl

theorem inj_inv {a b : Srt} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ (.inj a b t) r) :
    ∃ r₀, EvalTerm c σ t r₀ ∧ r = r₀.map (injNormal a b) := by
  cases h with
  | inj h => exact ⟨_, h, rfl⟩

theorem dv_inv {s : Srt} {l : Lit} {r : Option GroundTerm} (h : EvalTerm c σ (.dv s l) r) :
    r = some (.dv s l) := by
  cases h; rfl

/-- The guard's result from the map's and the key's. -/
theorem lookup_eq {rc rt r : Option GroundTerm}
    (hr : match mapOf rt, keyOf rc with
      | some x, some y => hook mapLookup [x, y] = some r
      | _, _ => r = none) : r = if rc = some (KCore.bool true) then rt else none := by
  have hv := lookup_val rc rt
  revert hr hv
  generalize mapOf rt = ma
  generalize keyOf rc = mk
  intro hr hv
  match ma, mk, hr, hv with
  | some x, some y, hr, hv =>
    change hook mapLookup [x, y] = some r at hr
    change hook mapLookup [x, y] = _ at hv
    rw [hr] at hv; exact Option.some.inj hv
  | none, _, hr, hv =>
    change r = none at hr
    change some none = _ at hv
    rw [hr]; exact Option.some.inj hv
  | some _, none, hr, hv =>
    change r = none at hr
    change some none = _ at hv
    rw [hr]; exact Option.some.inj hv

theorem lookup_of {rc rt : Option GroundTerm} :
    match mapOf rt, keyOf rc with
      | some x, some y => hook mapLookup [x, y] = some (if rc = some (KCore.bool true) then rt else none)
      | _, _ => (if rc = some (KCore.bool true) then rt else none) = none := by
  have hv := lookup_val rc rt
  revert hv
  generalize mapOf rt = ma
  generalize keyOf rc = mk
  intro hv
  match ma, mk, hv with
  | some x, some y, hv => exact hv
  | none, _, hv => exact (Option.some.inj hv).symm
  | some _, none, hv => exact (Option.some.inj hv).symm

/-- **The guard's results.** `ensGuard C t` evaluates to r exactly when C evaluates to some rc and t
to some rt, and r is rt where rc is `true` and none otherwise. -/
theorem ensGuard_iff {cond t : Term} {r : Option GroundTerm} (hL : c.isCtor mapLookup = false)
    (hE : c.isCtor mapElem = false) (hA : c.isCtor boolAnd = false) :
    EvalTerm c σ (ensGuard cond t) r ↔ ∃ rc rt, EvalTerm c σ cond rc ∧ EvalTerm c σ t rt ∧
      r = if rc = some (KCore.bool true) then rt else none := by
  unfold ensGuard
  rw [hook2_iff hL isHook_lookup]
  constructor
  · rintro ⟨ra, rk, ha, hk, hr⟩
    obtain ⟨ri, rt, hi, ht, hra⟩ := (hook2_iff hE isHook_elem).mp ha
    obtain ⟨ri₀, hi₀, rfl⟩ := inj_inv hi
    rw [dv_inv hi₀] at hra
    obtain ⟨rb, hb, rfl⟩ := inj_inv hk
    obtain ⟨rc, rT, hc', hT, hrb⟩ := (hook2_iff hA isHook_and).mp hb
    rw [dv_inv hT] at hrb
    refine ⟨rc, rt, hc', ht, ?_⟩
    have hra' : ra = mapOf rt := by
      cases rt with
      | none => exact hra
      | some w =>
        change hook mapElem [injNormal Srt.bool Srt.kitem (KCore.bool true), w] = some ra at hra
        rw [hook_elem] at hra
        exact (Option.some.inj hra).symm
    have hrb' : rb = rc.bind fun v => (asBool v).map KCore.bool := by
      cases rc with
      | none => exact hrb
      | some v =>
        change hook boolAnd [v, KCore.bool true] = some rb at hrb
        rw [hook_and] at hrb
        exact (Option.some.inj hrb).symm
    subst hra' hrb'
    exact lookup_eq hr
  · rintro ⟨rc, rt, hc', ht, rfl⟩
    refine ⟨mapOf rt, keyOf rc, ?_, ?_, lookup_of⟩
    · rw [hook2_iff hE isHook_elem]
      refine ⟨_, rt, .inj .dv, ht, ?_⟩
      cases rt with
      | none => rfl
      | some w => exact hook_elem _ _
    · refine .inj ((hook2_iff hA isHook_and).mpr ⟨rc, _, hc', .dv, ?_⟩)
      cases rc with
      | none => rfl
      | some v => exact hook_and v

/-! ## The guard under applications and injections -/

section
variable {cond : Term} (hL : c.isCtor mapLookup = false) (hE : c.isCtor mapElem = false)
  (hA : c.isCtor boolAnd = false)
include hL hE hA

mutual
  /-- Where C evaluates to `true`, the guarded term has every result the term has. -/
  theorem first_true (hC : EvalTerm c σ cond (some (KCore.bool true))) :
      ∀ (t t' : Term), ensGuardFirst cond t = some t' → ∀ r, EvalTerm c σ t r → EvalTerm c σ t' r
    | .inj a b u, t', h, r, hr => by
      rw [ensGuardFirst] at h
      split at h
      · cases h
        exact (ensGuard_iff hL hE hA).mpr ⟨_, r, hC, hr, by simp⟩
      · cases hu : ensGuardFirst cond u with
        | none => rw [hu] at h; cases h
        | some u' =>
          rw [hu] at h; cases h
          cases hr with
          | inj hr => exact .inj (first_true hC u u' hu _ hr)
    | .app f ts, t', h, r, hr => by
      rw [ensGuardFirst] at h
      cases hl : ensGuardList cond ts with
      | none => rw [hl] at h; cases h
      | some ts' =>
        rw [hl] at h; cases h
        exact app_congr (fun rs hts => list_true hC ts ts' hl rs hts) hr
    | .var _, _, h, _, _ => by simp [ensGuardFirst] at h
    | .as _ _, _, h, _, _ => by simp [ensGuardFirst] at h
    | .dv _ _, _, h, _, _ => by simp [ensGuardFirst] at h
    termination_by structural t => t
  theorem list_true (hC : EvalTerm c σ cond (some (KCore.bool true))) :
      ∀ (ts ts' : List Term), ensGuardList cond ts = some ts' →
        ∀ rs, EvalTerms c σ ts rs → EvalTerms c σ ts' rs
    | [], _, h, _, _ => by simp [ensGuardList] at h
    | t :: ts, ts', h, rs, hts => by
      rw [ensGuardList] at h
      cases hts with
      | cons ht hts =>
        cases hf : ensGuardFirst cond t with
        | some t' => rw [hf] at h; cases h; exact .cons (first_true hC t t' hf _ ht) hts
        | none =>
          rw [hf] at h
          cases hl : ensGuardList cond ts with
          | none => rw [hl] at h; cases h
          | some ts₀ => rw [hl] at h; cases h; exact .cons ht (list_true hC ts ts₀ hl _ hts)
    termination_by structural ts => ts
end

mutual
  /-- A value of the guarded term is one where C evaluates to `true`, and a value of the term. -/
  theorem first_some :
      ∀ (t t' : Term), ensGuardFirst cond t = some t' → ∀ y, EvalTerm c σ t' (some y) →
        EvalTerm c σ cond (some (KCore.bool true)) ∧ EvalTerm c σ t (some y)
    | .inj a b u, t', h, y, hy => by
      rw [ensGuardFirst] at h
      split at h
      · cases h
        obtain ⟨rc, rt, hc', ht, he⟩ := (ensGuard_iff hL hE hA).mp hy
        by_cases hrc : rc = some (KCore.bool true)
        · rw [if_pos hrc] at he; subst hrc he; exact ⟨hc', ht⟩
        · rw [if_neg hrc] at he; cases he
      · cases hu : ensGuardFirst cond u with
        | none => rw [hu] at h; cases h
        | some u' =>
          rw [hu] at h; cases h
          obtain ⟨ru, hr, he⟩ := inj_inv hy
          cases ru with
          | none => cases he
          | some y₀ =>
            obtain ⟨hC, hu'⟩ := first_some u u' hu y₀ hr
            refine ⟨hC, ?_⟩
            rw [he]; exact .inj hu'
    | .app f ts, t', h, y, hy => by
      rw [ensGuardFirst] at h
      cases hl : ensGuardList cond ts with
      | none => rw [hl] at h; cases h
      | some ts' =>
        rw [hl] at h; cases h
        obtain ⟨rs, vs, hts, hvs⟩ := app_args_of_ne hy (by simp)
        refine ⟨(list_some ts ts' hl rs vs hts hvs).1, ?_⟩
        exact app_congr_def (fun rs vs hts hvs => (list_some ts ts' hl rs vs hts hvs).2) hy (by simp)
    | .var _, _, h, _, _ => by simp [ensGuardFirst] at h
    | .as _ _, _, h, _, _ => by simp [ensGuardFirst] at h
    | .dv _ _, _, h, _, _ => by simp [ensGuardFirst] at h
    termination_by structural t => t
  theorem list_some :
      ∀ (ts ts' : List Term), ensGuardList cond ts = some ts' →
        ∀ rs vs, EvalTerms c σ ts' rs → allSome rs = some vs →
          EvalTerm c σ cond (some (KCore.bool true)) ∧ EvalTerms c σ ts rs
    | [], _, h, _, _, _, _ => by simp [ensGuardList] at h
    | t :: ts, ts', h, rs, vs, hts, hvs => by
      rw [ensGuardList] at h
      cases hf : ensGuardFirst cond t with
      | some t' =>
        rw [hf] at h; cases h
        cases hts with
        | @cons _ _ _ r rs' ht hts =>
          cases r with
          | none => simp [allSome] at hvs
          | some v =>
            obtain ⟨hC, ht'⟩ := first_some t t' hf v ht
            exact ⟨hC, .cons ht' hts⟩
      | none =>
        rw [hf] at h
        cases hl : ensGuardList cond ts with
        | none => rw [hl] at h; cases h
        | some ts₀ =>
          rw [hl] at h; cases h
          cases hts with
          | @cons _ _ _ r rs' ht hts =>
            cases r with
            | none => simp [allSome] at hvs
            | some v =>
              cases hv' : allSome rs' with
              | none => simp [allSome, hv'] at hvs
              | some vs' =>
                obtain ⟨hC, hts'⟩ := list_some ts ts₀ hl rs' vs' hts hv'
                exact ⟨hC, .cons ht hts'⟩
    termination_by structural ts => ts
end

mutual
  /-- Where C evaluates to anything but `true`, or to no value, the guarded term evaluates to no
  value wherever the term evaluates. -/
  theorem first_none {rc : Option GroundTerm} (hC : EvalTerm c σ cond rc) (hn : rc ≠ some (KCore.bool true)) :
      ∀ (t t' : Term), ensGuardFirst cond t = some t' → ∀ r, EvalTerm c σ t r → EvalTerm c σ t' none
    | .inj a b u, t', h, r, hr => by
      rw [ensGuardFirst] at h
      split at h
      · cases h
        exact (ensGuard_iff hL hE hA).mpr ⟨rc, r, hC, hr, by rw [if_neg hn]⟩
      · cases hu : ensGuardFirst cond u with
        | none => rw [hu] at h; cases h
        | some u' =>
          rw [hu] at h; cases h
          cases hr with
          | inj hr => exact .inj (first_none hC hn u u' hu _ hr)
    | .app f ts, t', h, r, hr => by
      rw [ensGuardFirst] at h
      cases hl : ensGuardList cond ts with
      | none => rw [hl] at h; cases h
      | some ts' =>
        rw [hl] at h; cases h
        exact app_none (fun rs hts => list_none hC hn ts ts' hl rs hts) hr
    | .var _, _, h, _, _ => by simp [ensGuardFirst] at h
    | .as _ _, _, h, _, _ => by simp [ensGuardFirst] at h
    | .dv _ _, _, h, _, _ => by simp [ensGuardFirst] at h
    termination_by structural t => t
  theorem list_none {rc : Option GroundTerm} (hC : EvalTerm c σ cond rc) (hn : rc ≠ some (KCore.bool true)) :
      ∀ (ts ts' : List Term), ensGuardList cond ts = some ts' →
        ∀ rs, EvalTerms c σ ts rs → ∃ rs', EvalTerms c σ ts' rs' ∧ allSome rs' = none
    | [], _, h, _, _ => by simp [ensGuardList] at h
    | t :: ts, ts', h, rs, hts => by
      rw [ensGuardList] at h
      cases hts with
      | @cons _ _ _ r rs' ht hts =>
        cases hf : ensGuardFirst cond t with
        | some t' =>
          rw [hf] at h; cases h
          exact ⟨none :: rs', .cons (first_none hC hn t t' hf _ ht) hts, rfl⟩
        | none =>
          rw [hf] at h
          cases hl : ensGuardList cond ts with
          | none => rw [hl] at h; cases h
          | some ts₀ =>
            rw [hl] at h; cases h
            obtain ⟨rs₀, hts₀, hn₀⟩ := list_none hC hn ts ts₀ hl rs' hts
            refine ⟨r :: rs₀, .cons ht hts₀, ?_⟩
            cases r <;> simp [allSome, hn₀]
    termination_by structural ts => ts
end

end

/-! ## The two properties of the guard encoding -/

section
variable {cond R R' : Term} (hL : c.isCtor mapLookup = false) (hE : c.isCtor mapElem = false)
  (hA : c.isCtor boolAnd = false) (hg : ensGuardFirst cond R = some R')
include hL hE hA hg

/-- **First property.** Where C evaluates to `true`, the encoded right side has exactly the written
one's values. -/
theorem guard_true (hC : EvalTerm c σ cond (some (KCore.bool true))) {y : GroundTerm} :
    EvalTerm c σ R' (some y) ↔ EvalTerm c σ R (some y) :=
  ⟨fun h => (first_some hL hE hA R R' hg y h).2, first_true hL hE hA hC R R' hg _⟩

/-- Where C evaluates to `true` and the written right side is undefined, so is the encoded one. -/
theorem guard_undef (hC : EvalTerm c σ cond (some (KCore.bool true))) (h : EvalTerm c σ R none) :
    EvalTerm c σ R' none :=
  first_true hL hE hA hC R R' hg _ h

/-- A value of the encoded right side is one where C evaluates to `true`. -/
theorem guard_some {y : GroundTerm} (h : EvalTerm c σ R' (some y)) :
    EvalTerm c σ cond (some (KCore.bool true)) ∧ EvalTerm c σ R (some y) :=
  first_some hL hE hA R R' hg y h

/-- **Second property.** Where C evaluates to anything but `true`, or to no value, the encoded
right side evaluates to no value (wherever the written one evaluates at all). -/
theorem guard_none {rc r : Option GroundTerm} (hC : EvalTerm c σ cond rc) (hn : rc ≠ some (KCore.bool true))
    (h : EvalTerm c σ R r) : EvalTerm c σ R' none :=
  first_none hL hE hA hC hn R R' hg r h

/-- With C's result unique, the encoded right side has no value where C's result is not `true`. -/
theorem guard_no_value {rc : Option GroundTerm} (hu : ∀ v, EvalTerm c σ cond v → v = rc)
    (hn : rc ≠ some (KCore.bool true)) {y : GroundTerm} : ¬ EvalTerm c σ R' (some y) := fun h =>
  hn (hu _ (guard_some hL hE hA hg h).1).symm

end

end GuardEval

/-! ## The evaluation and matching of a semantics do not read its rules -/

/-- `c` with the rules `rs`. -/
abbrev withRules (c : Semantics) (rs : List Rule) : Semantics := { c with rules := rs }

kernel_rfl sortOf_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).sortOf = c.sortOf
kernel_rfl collVal_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).collVal = c.collVal
kernel_rfl norm_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).norm = c.norm
kernel_rfl fnCover_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).fnCover = c.fnCover
kernel_rfl paramVal_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).paramVal = c.paramVal
kernel_rfl hookRes_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).hookRes = c.hookRes
kernel_rfl fnRest_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).fnRest = c.fnRest

theorem wellSorted_rules {c : Semantics} {rs : List Rule} {vars : List Srt} {σ : Subst} :
    (withRules c rs).WellSorted vars σ ↔ c.WellSorted vars σ := by
  unfold Semantics.WellSorted; rw [sortOf_withRules]

/-- A configuration of `c` is one of `c` with any rules. -/
def Config.toRules {c : Semantics} (rs : List Rule) (x : Config c) : Config (withRules c rs) :=
  ⟨x.val, by rw [sortOf_withRules]; exact x.2⟩

section Transfer
variable {c : Semantics} (rs : List Rule) {σ : Subst}

theorem patVals_rules {ps : List Term} {vs : List GroundTerm} (h : PatVals c σ ps vs) :
    PatVals (withRules c rs) σ ps vs :=
  PatVals.rec (c := c) (σ := σ) (motive_1 := fun p v _ => PatVal (withRules c rs) σ p v)
    (motive_2 := fun ps vs _ => PatVals (withRules c rs) σ ps vs)
    (fun h => .var h) .dv (fun h _ ih => .ctor h ih) (fun hp _ hv ih => .hook hp ih hv)
    (fun _ ih => .inj ih) (fun hc hp _ hv ih => .coll hc hp ih (by rw [collVal_withRules]; exact hv))
    (fun _ hi ih => .as ih hi) (fun hc ho _ hv ih => .ovl hc ho ih (by rw [norm_withRules]; exact hv)) .nil (fun _ _ ih ihs => .cons ih ihs) h

theorem patVal_rules {p : Term} {v : GroundTerm} (h : PatVal c σ p v) : PatVal (withRules c rs) σ p v :=
  PatVal.rec (c := c) (σ := σ) (motive_1 := fun p v _ => PatVal (withRules c rs) σ p v)
    (motive_2 := fun ps vs _ => PatVals (withRules c rs) σ ps vs)
    (fun h => .var h) .dv (fun h _ ih => .ctor h ih) (fun hp _ hv ih => .hook hp ih hv)
    (fun _ ih => .inj ih) (fun hc hp _ hv ih => .coll hc hp ih (by rw [collVal_withRules]; exact hv))
    (fun _ hi ih => .as ih hi) (fun hc ho _ hv ih => .ovl hc ho ih (by rw [norm_withRules]; exact hv)) .nil (fun _ _ ih ihs => .cons ih ihs) h

/-- A pattern's values with the rules `rs` are those of `c`. -/
theorem patVals_rules_back {ps : List Term} {vs : List GroundTerm} (h : PatVals (withRules c rs) σ ps vs) :
    PatVals c σ ps vs :=
  patVals_rules (c := withRules c rs) c.rules h

theorem patVal_rules_back {p : Term} {v : GroundTerm} (h : PatVal (withRules c rs) σ p v) :
    PatVal c σ p v :=
  patVal_rules (c := withRules c rs) c.rules h

omit σ in
/-- The extensions of a substitution with the rules `rs` are those of `c`. -/
theorem extends_rules {n : Nat} {ys : List Srt} {σ σ' : Subst} :
    Extends (withRules c rs) n ys σ σ' ↔ Extends c n ys σ σ' := by
  unfold Extends; rw [sortOf_withRules]

theorem evalTerm_rules {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
    EvalTerm (withRules c rs) σ t r :=
  EvalTerm.rec (c := c) (motive_1 := fun f vs r _ => Eval (withRules c rs) f vs r)
    (motive_2 := fun vs cl _ => Fails (withRules c rs) vs cl)
    (motive_3 := fun σ cl _ => ReqFails (withRules c rs) σ cl)
    (motive_4 := fun σ t r _ => EvalTerm (withRules c rs) σ t r)
    (motive_5 := fun σ ts rs' _ => EvalTerms (withRules c rs) σ ts rs')
    (motive_6 := fun n σ p b _ => Holds (withRules c rs) n σ p b)
    (motive_7 := fun σ cl _ => InstFails (withRules c rs) σ cl)
    (motive_8 := fun σ cl r _ => InstIs (withRules c rs) σ cl r)
    (fun hfn hmem hσ hmatch _ _ _ hex _ _ _ ihreq ihpre ihprio ihrhs ihens ihpost =>
      .clause hfn hmem (wellSorted_rules.mpr hσ) (patVals_rules rs hmatch) ihreq ihpre ihprio hex ihrhs ihens ihpost)
    (fun hfn _ ihnone => by
      have := Eval.rest (c := withRules c rs) hfn ihnone
      rwa [fnRest_withRules] at this)
    (fun hfn hmem hσ hmatch _ _ _ hex ht _ hw ihreq ihpre ihprio ihe =>
      .ensFails hfn hmem (wellSorted_rules.mpr hσ) (patVals_rules rs hmatch) ihreq ihpre ihprio hex ht ihe hw)
    (fun hfn hmem hσ hmatch _ _ _ hne _ _ _ _ ihreq ihpre ihprio ihrhs ihens ihpost ihall =>
      .clauseEx hfn hmem (wellSorted_rules.mpr hσ) (patVals_rules rs hmatch) ihreq ihpre ihprio hne ihrhs ihens
        ihpost (fun σ' ha hw => ihall σ' ha (wellSorted_rules.mp hw)))
    (fun hfn hmem hne hσ hmatch _ _ _ hsome _ ihreq ihpre ihprio ihall =>
      .exNone hfn hmem hne (by unfold Semantics.WellSortedAt at hσ ⊢; rw [sortOf_withRules]; exact hσ)
        (patVals_rules rs hmatch) ihreq ihpre ihprio
        (let ⟨σ', ha, hw⟩ := hsome; ⟨σ', ha, wellSorted_rules.mpr hw⟩)
        (fun σ' ha hw => ihall σ' ha (wellSorted_rules.mp hw)))
    (fun _ ih => .intro fun σ hσ hp => ih σ (by unfold Semantics.WellSortedAt at hσ ⊢; rwa [sortOf_withRules] at hσ) (patVals_rules_back rs hp))
    (fun ht _ hr ihe => .intro ht ihe hr)
    (fun _ ih => .pre ih)
    .var .dv (fun _ ih => .inj ih) (fun hk _ ih => .ctor hk ih)
    (fun hk hhk _ hh hund ih => .hook hk hhk ih (by rw [hookRes_withRules]; exact hh) hund)
    (fun hk hhk hp _ hr ih => .param hk hhk hp ih (by rw [paramVal_withRules]; exact hr))
    (fun hk hhk _ hvs _ hp ihts ihf => .call hk hhk ihts hvs ihf hp)
    (fun hk hhk _ hvs hp ih => .callUndef hk hhk ih hvs hp)
    (fun hk ho _ hnf ih => by
      have := EvalTerm.ovl (c := withRules c rs) hk ho ih (fun vs hv => by rw [fnCover_withRules]; exact hnf vs hv)
      rwa [norm_withRules] at this)
    (fun hk ho _ hvs hlo hcov _ ihts ihf => .ovlFn hk ho ihts hvs hlo (by rw [fnCover_withRules]; exact hcov) ihf)
    .nil (fun _ _ ih1 ih2 => .cons ih1 ih2)
    .top .bot (fun _ ih => .not ih) (fun _ _ ih ih' => .and ih ih') (fun _ _ ih ih' => .or ih ih')
    (fun _ _ ih ih' => .implies ih ih') (fun _ ih => .ceil ih) (fun _ _ ih ih' => .equals ih ih')
    (fun _ _ ih ih' => .mem ih ih') (fun _ ih => .exNone ih)
    (fun g _ _ hr ih ihb =>
      .exSome g ih (fun σ' he hp => ihb σ' ((extends_rules rs).mp he) (patVal_rules_back rs hp))
        (hr.trans ⟨fun ⟨σ', he, hp, hg⟩ => ⟨σ', (extends_rules rs).mpr he, patVal_rules rs hp, hg⟩,
          fun ⟨σ', he, hp, hg⟩ => ⟨σ', (extends_rules rs).mp he, patVal_rules_back rs hp, hg⟩⟩))
    (fun g _ hr ihb =>
      .ex g (fun σ' he => ihb σ' ((extends_rules rs).mp he))
        (hr.trans ⟨fun ⟨σ', he, hg⟩ => ⟨σ', (extends_rules rs).mpr he, hg⟩,
          fun ⟨σ', he, hg⟩ => ⟨σ', (extends_rules rs).mp he, hg⟩⟩))
    (fun g _ hr ihb =>
      .all g (fun σ' he => ihb σ' ((extends_rules rs).mp he))
        (hr.trans ⟨fun H σ' he => H σ' ((extends_rules rs).mp he),
          fun H σ' he => H σ' ((extends_rules rs).mpr he)⟩))
    (fun ht _ hw ihe => .ens ht ihe hw) (fun _ ih => .post ih) (fun _ ih => .rhs ih)
    (fun _ _ ihp ih => .fails ihp ih) (fun _ _ _ ihr ihe ihp => .gives ihr ihe ihp)
    h

theorem evalTerm_rules_back {t : Term} {r : Option GroundTerm} (h : EvalTerm (withRules c rs) σ t r) :
    EvalTerm c σ t r :=
  evalTerm_rules (c := withRules c rs) c.rules h

/-- Two rules with the same variables, left side and `requires` apply at the same values, in `c`
and with any rules, where the first rule's premise predicate is `\top` and its left side binds
every variable. -/
theorem notApplies_rules {r r' : Rule} (hv : r'.vars = r.vars) (hl : r'.lhs = r.lhs) (hq : r'.req = r.req)
    (hpre : r.pre = .top) (hb : binds r.vars.length (varOccs r.lhs) = true)
    {x : GroundTerm} (h : NotApplies c r x) : NotApplies (withRules c rs) r' x := by
  intro σ hσ hp
  have hσ' : c.WellSorted r.vars σ := by
    have := Rule.wellSorted_of_at (c := withRules c rs) (r := r') (by rw [hv, hl]; exact hb) hσ
    rw [hv] at this; exact wellSorted_rules.mp this
  rw [hl] at hp
  obtain ⟨_, _, ht, he, hne⟩ := (h σ (hσ'.at _) (patVal_rules (c := withRules c rs) c.rules hp)).req_of_top hpre
  exact .intro (hq ▸ ht) (evalTerm_rules rs he) hne

theorem notApplies_rules_back {r r' : Rule} (hv : r'.vars = r.vars) (hl : r'.lhs = r.lhs) (hq : r'.req = r.req)
    (hpre : r'.pre = .top) (hb : binds r'.vars.length (varOccs r'.lhs) = true)
    {x : GroundTerm} (h : NotApplies (withRules c rs) r' x) : NotApplies c r x :=
  notApplies_rules (c := withRules c rs) c.rules hv.symm hl.symm hq.symm hpre hb h

end Transfer

/-! ## B-guard: the guard encoding gives the field's steps -/

/-- A rule with its `ensures` E written as the guard of its right side (`ensGuardFirst`) and no
`ensures`; the rule itself where it has no `ensures` or its right side no injection into KItem. -/
def guardOf (r : Rule) : Rule :=
  match r.ens with
  | some e => match ensGuardFirst e r.rhs with
    | some g => { r with rhs := g, ens := none }
    | none => r
  | none => r

/-- `c` with each rule's `ensures` read as the guard of its right side. -/
abbrev guardSem (c : Semantics) : Semantics := withRules c (c.rules.map guardOf)

theorem guardOf_cases (r : Rule) : guardOf r = r ∨
    ∃ e g, r.ens = some e ∧ ensGuardFirst e r.rhs = some g ∧ guardOf r = { r with rhs := g, ens := none } := by
  unfold guardOf
  split
  · next e he =>
    split
    · next g hg => exact Or.inr ⟨e, g, he, hg, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- The rules' predicates are `\top` and their left sides bind every variable. -/
def PlainRules (c : Semantics) : Prop :=
  ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top ∧ binds r.vars.length (varOccs r.lhs) = true

theorem guardOf_conds (r : Rule) : (guardOf r).pre = r.pre ∧ (guardOf r).post = r.post := by
  rcases guardOf_cases r with h | ⟨_, _, _, _, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

theorem guardOf_parts (r : Rule) : (guardOf r).vars = r.vars ∧ (guardOf r).lhs = r.lhs ∧
    (guardOf r).req = r.req ∧ (guardOf r).prio = r.prio := by
  rcases guardOf_cases r with h | ⟨_, _, _, _, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl, rfl, rfl⟩

section Guard
variable {c : Semantics} (hL : c.isCtor mapLookup = false) (hE : c.isCtor mapElem = false)
  (hA : c.isCtor boolAnd = false)
include hL hE hA

/-- The field's right side and `ensures` give the guarded rule's. -/
theorem guard_fwd {r : Rule} {σ : Subst} {y : GroundTerm} (he : EvalTerm c σ r.rhs (some y))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (KCore.bool true))) :
    EvalTerm c σ (guardOf r).rhs (some y) ∧ ∀ t, (guardOf r).ens = some t → EvalTerm c σ t (some (KCore.bool true)) := by
  rcases guardOf_cases r with h | ⟨e, g, hre, hg, h⟩
  · rw [h]; exact ⟨he, hens⟩
  · rw [h]
    exact ⟨(guard_true hL hE hA hg (hens e hre)).mpr he, fun t ht => by cases ht⟩

/-- The guarded rule's right side and `ensures` give the field's. -/
theorem guard_bwd {r : Rule} {σ : Subst} {y : GroundTerm} (he : EvalTerm c σ (guardOf r).rhs (some y))
    (hens : ∀ t, (guardOf r).ens = some t → EvalTerm c σ t (some (KCore.bool true))) :
    EvalTerm c σ r.rhs (some y) ∧ ∀ t, r.ens = some t → EvalTerm c σ t (some (KCore.bool true)) := by
  rcases guardOf_cases r with h | ⟨e, g, hre, hg, h⟩
  · rw [h] at he hens; exact ⟨he, hens⟩
  · rw [h] at he
    obtain ⟨hC, hR⟩ := guard_some hL hE hA hg he
    refine ⟨hR, fun t ht => ?_⟩
    rw [hre] at ht; cases ht; exact hC

/-- **B-guard, steps.** The guard encoding and the field give the same steps, where every rule's
predicates are `\top` and its left side binds every variable (`PlainRules`). -/
theorem guard_step (hrp : PlainRules c) (x y : Config c) :
    Step c x y ↔ Step (guardSem c) (Config.toRules _ x) (Config.toRules _ y) := by
  constructor
  · intro h
    cases h with
    | rule r hr σ hσ hmatch hreq _ heval hens _ hprio =>
      obtain ⟨hv, hl, hq, hp⟩ := guardOf_parts r
      obtain ⟨he', hens'⟩ := guard_fwd hL hE hA heval hens
      obtain ⟨hpre, hpost, -⟩ := hrp r hr
      refine .rule (guardOf r) (List.mem_map_of_mem hr) σ (wellSorted_rules.mpr (hv ▸ hσ))
        (hl ▸ patVal_rules _ hmatch) (fun t ht => evalTerm_rules _ (hreq t (hq ▸ ht)))
        (by rw [(guardOf_conds r).1, hpre]; exact .top)
        (evalTerm_rules _ he') (fun t ht => evalTerm_rules _ (hens' t ht))
        (by rw [(guardOf_conds r).2, hpost]; exact .top) ?_
      intro r'' hr'' hlt
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr''
      obtain ⟨hv', hl', hq', hp'⟩ := guardOf_parts r'
      exact notApplies_rules _ hv' hl' hq' (hrp r' hr').1 (hrp r' hr').2.2
        (hprio r' hr' (by rw [← hp', ← hp]; exact hlt))
  · intro h
    cases h with
    | rule r'' hr'' σ hσ hmatch hreq _ heval hens _ hprio =>
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr''
      obtain ⟨hv, hl, hq, hp⟩ := guardOf_parts r
      obtain ⟨he', hens'⟩ := guard_bwd hL hE hA (evalTerm_rules_back _ heval)
        (fun t ht => evalTerm_rules_back _ (hens t ht))
      obtain ⟨hpre, hpost, -⟩ := hrp r hr
      refine .rule r hr σ (hv ▸ wellSorted_rules.mp hσ) (patVal_rules (c := guardSem c) c.rules (hl ▸ hmatch))
        (fun t ht => evalTerm_rules_back _ (hreq t (hq.symm ▸ ht))) (hpre ▸ .top) he' hens' (hpost ▸ .top) ?_
      intro r' hr' hlt
      obtain ⟨hv', hl', hq', hp'⟩ := guardOf_parts r'
      exact notApplies_rules_back _ hv' hl' hq'
        (by rw [(guardOf_conds r').1]; exact (hrp r' hr').1) (by rw [hv', hl']; exact (hrp r' hr').2.2)
        (hprio (guardOf r') (List.mem_map_of_mem hr') (by rw [hp', hp]; exact hlt))

omit hL hE hA in
/-- **B-guard, where a rule applies.** A rule whose premise predicate is `\top` and whose left side
binds every variable and its guarded rule apply at the same values: they have one left side and one
`requires`. -/
theorem guard_notApplies (r : Rule) (hpre : r.pre = .top) (hb : binds r.vars.length (varOccs r.lhs) = true)
    (x : GroundTerm) : NotApplies c r x ↔ NotApplies (guardSem c) (guardOf r) x :=
  let ⟨hv, hl, hq, _⟩ := guardOf_parts r
  ⟨notApplies_rules _ hv hl hq hpre hb,
   notApplies_rules_back _ hv hl hq (by rw [(guardOf_conds r).1]; exact hpre) (by rw [hv, hl]; exact hb)⟩

end Guard

/-! ## B-conj: the `ensures` as a conjunct of the `requires` -/

/-- The `requires` with the `ensures` after it (`_andBool_`). -/
def conj : Option Term → Option Term → Option Term
  | q, none => q
  | none, some e => some e
  | some q, some e => some (.app boolAnd [q, e])

/-- A rule with its `ensures` conjoined to its `requires`, and no `ensures`. -/
def conjOf (r : Rule) : Rule := { r with req := conj r.req r.ens, ens := none }

/-- `c` with each rule's `ensures` read as a conjunct of its `requires`. -/
abbrev conjSem (c : Semantics) : Semantics := withRules c (c.rules.map conjOf)

/-- Each rule's `ensures` has a result wherever the rule's variables are well sorted. -/
def EnsDefinedRule (c : Semantics) (r : Rule) : Prop :=
  ∀ e, r.ens = some e → ∀ σ, c.WellSorted r.vars σ → ∃ v, EvalTerm c σ e v

def EnsDefined (c : Semantics) : Prop := ∀ r ∈ c.rules, EnsDefinedRule c r

/-- No rule with an `ensures` matches a value that a rule of a larger priority matches. -/
def Apart (c : Semantics) : Prop :=
  ∀ r ∈ c.rules, r.ens.isSome = true → ∀ r'' ∈ c.rules, r.prio < r''.prio → ∀ (v : GroundTerm) (σ σ' : Subst),
    c.WellSorted r.vars σ → PatVal c σ r.lhs v → c.WellSorted r''.vars σ' → PatVal c σ' r''.lhs v → False

theorem hook_boolAnd (x y : GroundTerm) : hook boolAnd [x, y] = some (bool2 [x, y] (· && ·)) := rfl

theorem bool_inj {a b : Bool} (h : KCore.bool a = KCore.bool b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- `x andBool y` is `true` exactly where both are `true`. -/
theorem bool2_and_true {x y : GroundTerm} :
    bool2 [x, y] (· && ·) = some (KCore.bool true) ↔ x = KCore.bool true ∧ y = KCore.bool true := by
  constructor
  · intro h
    simp only [bool2, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have := bool_inj hab
    simp only [Bool.and_eq_true] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨eq_of_asBool ha, eq_of_asBool hb⟩
  · rintro ⟨rfl, rfl⟩; rfl

section Conj
variable {c : Semantics} {σ : Subst} (hA : c.isCtor boolAnd = false)
include hA

theorem and_true {q e : Term} (hq : EvalTerm c σ q (some (KCore.bool true)))
    (he : EvalTerm c σ e (some (KCore.bool true))) :
    EvalTerm c σ (.app boolAnd [q, e]) (some (KCore.bool true)) :=
  (hook2_iff hA isHook_and).mpr ⟨_, _, hq, he, rfl⟩

theorem and_inv {q e : Term} (h : EvalTerm c σ (.app boolAnd [q, e]) (some (KCore.bool true))) :
    EvalTerm c σ q (some (KCore.bool true)) ∧ EvalTerm c σ e (some (KCore.bool true)) := by
  obtain ⟨ra, rb, ha, hb, hr⟩ := (hook2_iff hA isHook_and).mp h
  match ra, rb, ha, hb, hr with
  | some x, some y, ha, hb, hr =>
    change hook boolAnd [x, y] = _ at hr
    rw [hook_boolAnd] at hr
    obtain ⟨rfl, rfl⟩ := bool2_and_true.mp (Option.some.inj hr)
    exact ⟨ha, hb⟩
  | none, _, _, _, hr => cases hr
  | some _, none, _, _, hr => cases hr

/-- Where q's result is not `true` and e has one, `q andBool e` has a result that is not `true`. -/
theorem and_fail {q e : Term} {v w : Option GroundTerm} (hq : EvalTerm c σ q v) (hv : v ≠ some (KCore.bool true))
    (he : EvalTerm c σ e w) : ∃ u, EvalTerm c σ (.app boolAnd [q, e]) u ∧ u ≠ some (KCore.bool true) := by
  match v, w, hq, he, hv with
  | some x, some y, hq, he, hv =>
    refine ⟨bool2 [x, y] (· && ·), (hook2_iff hA isHook_and).mpr ⟨_, _, hq, he, rfl⟩, fun h => ?_⟩
    exact hv (by rw [(bool2_and_true.mp h).1])
  | none, w, hq, he, _ =>
    exact ⟨none, (hook2_iff hA isHook_and).mpr ⟨_, _, hq, he, by cases w <;> rfl⟩, by simp⟩
  | some x, none, hq, he, _ =>
    exact ⟨none, (hook2_iff hA isHook_and).mpr ⟨_, _, hq, he, rfl⟩, by simp⟩

/-- Where `q andBool e` has a result that is not `true`, q's or e's is not `true`. -/
theorem and_fail_inv {q e : Term} {u : Option GroundTerm} (h : EvalTerm c σ (.app boolAnd [q, e]) u)
    (hu : u ≠ some (KCore.bool true)) :
    (∃ v, EvalTerm c σ q v ∧ v ≠ some (KCore.bool true)) ∨ (∃ w, EvalTerm c σ e w ∧ w ≠ some (KCore.bool true)) := by
  obtain ⟨ra, rb, ha, hb, hr⟩ := (hook2_iff hA isHook_and).mp h
  match ra, rb, ha, hb, hr with
  | some x, some y, ha, hb, hr =>
    change hook boolAnd [x, y] = _ at hr
    rw [hook_boolAnd] at hr
    by_cases hx : x = KCore.bool true
    · refine Or.inr ⟨some y, hb, fun hy => hu ?_⟩
      cases hy; subst hx
      exact (Option.some.inj hr).symm.trans rfl
    · exact Or.inl ⟨some x, ha, fun h' => hx (Option.some.inj h')⟩
  | none, _, ha, _, _ => exact Or.inl ⟨none, ha, by simp⟩
  | some _, none, _, hb, _ => exact Or.inr ⟨none, hb, by simp⟩

/-- The conjunct reading's `requires` is `true` exactly where the `requires` and the `ensures` are. -/
theorem conj_req_true {r : Rule} :
    (∀ t, (conjOf r).req = some t → EvalTerm c σ t (some (KCore.bool true))) ↔
      (∀ t, r.req = some t → EvalTerm c σ t (some (KCore.bool true))) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (KCore.bool true))) := by
  unfold conjOf
  cases hq : r.req with
  | none =>
    cases he : r.ens with
    | none => simp [conj]
    | some e => simp [conj]
  | some q =>
    cases he : r.ens with
    | none => simp [conj]
    | some e =>
      simp only [conj, Option.some.injEq, forall_eq']
      exact ⟨and_inv hA, fun ⟨h1, h2⟩ => and_true hA h1 h2⟩

/-- **B-conj (3).** A rule that does not apply does not apply in the conjunct reading, where its
`ensures` has a result, its premise predicate is `\top` and its left side binds every variable. -/
theorem conj_notApplies {r : Rule} (hT : EnsDefinedRule c r) (hpre : r.pre = .top)
    (hb : binds r.vars.length (varOccs r.lhs) = true) {x : GroundTerm} (h : NotApplies c r x) :
    NotApplies (conjSem c) (conjOf r) x := by
  intro σ hσ hp
  have hσ := wellSorted_rules.mp (Rule.wellSorted_of_at (c := conjSem c) (r := conjOf r) hb hσ)
  obtain ⟨_, _, ht, he, hne⟩ := (h σ (hσ.at _) (patVal_rules (c := conjSem c) c.rules hp)).req_of_top hpre
  cases hre : r.ens with
  | none =>
    refine .intro ?_ (evalTerm_rules _ he) hne
    simp only [conjOf, conj, hre]; exact ht
  | some e =>
    obtain ⟨w, hw⟩ := hT e hre σ hσ
    obtain ⟨u, hu, hune⟩ := and_fail hA he hne hw
    refine .intro ?_ (evalTerm_rules _ hu) hune
    simp only [conjOf, conj, hre, ht]

/-- **B-conj (4).** For a rule whose premise predicate is `\top`: where the conjunct reading's rule
does not apply, at each match of the rule its `requires` fails or its `ensures` has a result that is
not `true`. -/
theorem notApplies_of_conj {r : Rule} {x : GroundTerm} (hpre : r.pre = .top)
    (h : NotApplies (conjSem c) (conjOf r) x) :
    ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      RuleReqFails c σ r ∨ ∃ t v, r.ens = some t ∧ EvalTerm c σ t v ∧ v ≠ some (KCore.bool true) := by
  intro σ hσ hp
  obtain ⟨_, _, ht, he, hne⟩ := RuleReqFails.req_of_top (r := conjOf r) hpre
    (h σ ((wellSorted_rules.mpr hσ).at _) (patVal_rules _ hp))
  have he := evalTerm_rules_back _ he
  simp only [conjOf] at ht
  cases hq : r.req with
  | none =>
    cases hre : r.ens with
    | none => rw [hq, hre] at ht; cases ht
    | some e =>
      rw [hq, hre] at ht; cases ht
      exact Or.inr ⟨_, _, rfl, he, hne⟩
  | some q =>
    cases hre : r.ens with
    | none =>
      rw [hq, hre] at ht; cases ht
      exact Or.inl (.intro hq he hne)
    | some e =>
      rw [hq, hre] at ht; cases ht
      rcases and_fail_inv hA he hne with ⟨v, hv, hvn⟩ | ⟨w, hw, hwn⟩
      · exact Or.inl (.intro hq hv hvn)
      · exact Or.inr ⟨_, _, rfl, hw, hwn⟩

/-- **B-conj (1).** Every step of the field is a step of the conjunct reading, where every rule's
`ensures` has a result, its predicates are `\top` and its left side binds every variable
(`PlainRules`). -/
theorem conj_step (hT : EnsDefined c) (hrp : PlainRules c) (x y : Config c) :
    Step c x y → Step (conjSem c) (Config.toRules _ x) (Config.toRules _ y) := by
  intro h
  cases h with
  | rule r hr σ hσ hmatch hreq _ heval hens _ hprio =>
    obtain ⟨hpre, hpost, -⟩ := hrp r hr
    refine .rule (conjOf r) (List.mem_map_of_mem hr) σ (wellSorted_rules.mpr hσ) (patVal_rules _ hmatch)
      (fun t ht => evalTerm_rules _ ((conj_req_true hA).mpr ⟨hreq, hens⟩ t ht)) (hpre ▸ .top)
      (evalTerm_rules _ heval) (fun t ht => by cases ht) (hpost ▸ .top) ?_
    intro r'' hr'' hlt
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr''
    exact conj_notApplies hA (hT r' hr') (hrp r' hr').1 (hrp r' hr').2.2 (hprio r' hr' hlt)

/-- **B-conj (2).** Every step of the conjunct reading is a step of the field, where no rule with an
`ensures` matches a value that a rule of a larger priority matches and every rule's predicates are
`\top` and its left side binds every variable (`PlainRules`). -/
theorem step_of_conj (hap : Apart c) (hrp : PlainRules c) (x y : Config c) :
    Step (conjSem c) (Config.toRules _ x) (Config.toRules _ y) → Step c x y := by
  intro h
  cases h with
  | rule r'' hr'' σ hσ hmatch hreq _ heval hens _ hprio =>
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr''
    have hσ := wellSorted_rules.mp hσ
    have hmatch' : PatVal c σ r.lhs x.val := patVal_rules (c := conjSem c) c.rules hmatch
    obtain ⟨hreq', hens'⟩ := (conj_req_true hA).mp (fun t ht => evalTerm_rules_back _ (hreq t ht))
    obtain ⟨hpre, hpost, -⟩ := hrp r hr
    refine .rule r hr σ hσ hmatch' hreq' (hpre ▸ .top) (evalTerm_rules_back _ heval) hens' (hpost ▸ .top) ?_
    intro r' hr' hlt
    cases hre : r'.ens with
    | some e =>
      intro σ' hσ' hp'
      exact (hap r' hr' (by rw [hre]; rfl) r hr hlt x.val σ'
        σ (Rule.wellSorted_of_at (hrp r' hr').2.2 hσ') hp' hσ hmatch').elim
    | none =>
      have hq : (conjOf r').req = r'.req := by simp only [conjOf, conj, hre]
      exact notApplies_rules_back (c.rules.map conjOf) (r := r') (r' := conjOf r') rfl rfl hq
        (hrp r' hr').1 (hrp r' hr').2.2 (hprio (conjOf r') (List.mem_map_of_mem hr') hlt)

end Conj

/-! ## B-conj (1) needs the `ensures` to have a result

`r1`: any configuration `=> ` the counter 1 `requires false ensures F(0)`, priority 50, where `F` has
the one equation `F(X) = F(0)`, so `F(0)` has no result (`EvalTerm` has no derivation for it);
`r2`: the same left side `=>` the counter 2, priority 60. With the field, `r1` does not apply (its
`requires` is false) and `r2` steps. In the conjunct reading `r1`'s `requires` is `false andBool
F(0)`, which has no result either, so `r1` is not shown not to apply and `r2` does not step. -/

namespace NeedsDefined

open KCore.Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

def F : Sym := 9019
def fApp : Term := .app F [.dv Srt.int (.int 0)]

def fnF : Fn :=
  { label := F, args := [Srt.int], result := Srt.bool,
    clauses := [{ vars := [Srt.int], pats := [.var 0], req := none, rhs := fApp, ens := none }] }

def lhs : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]
def rhsAt (n : Int) : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.dv Srt.int (.int n)]]

def r1 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := lhs, req := some (.dv Srt.bool (.bool false)), rhs := rhsAt 1,
    ens := some fApp, prio := 50 }
def r2 : Rule := { vars := [Srt.k, Srt.int], lhs := lhs, req := none, rhs := rhsAt 2, ens := none, prio := 60 }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fnF]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [r1, r2] }

kernel_rfl lookupFn_F : c.lookupFn F = some fnF

theorem F_flags : c.isCtor F = false ∧ isHook F = false ∧ c.isParam F = false ∧ c.isOvl F = false ∧
    c.lookupFn F = some fnF := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, lookupFn_F⟩

/-- `F(0)` has no result: a derivation would need a shorter one of `F(0)` (`F`'s one equation
applies at 0, whose right side is `F(0)`), and `F`'s equation always applies at 0. -/
theorem no_result {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm c σ fApp r := by
  obtain ⟨hk, hh, hp, ho, hfn⟩ := F_flags
  intro h
  have key : fApp ≠ fApp :=
    EvalTerm.rec (motive_1 := fun f vs _ _ => f ≠ F ∨ vs ≠ [int 0]) (motive_2 := fun _ _ _ => True)
      (motive_3 := fun _ _ _ => True) (motive_4 := fun _ t _ _ => t ≠ fApp) (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ _ => True) (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
      (fun {f fn vs cl _ _} hfn' hmem _ _ _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => by
        refine Or.inl fun hf => ?_
        subst hf
        rw [hfn] at hfn'; cases hfn'
        simp only [fnF, List.mem_singleton] at hmem
        subst hmem
        exact ihrhs rfl)
      (fun {f fn vs} hfn' hnone _ => by
        refine Classical.byCases (p := f = F ∧ vs = [int 0]) (fun ⟨hf, hv⟩ => ?_)
          (fun hn => by
            by_cases hf : f = F
            · exact Or.inr fun hv => hn ⟨hf, hv⟩
            · exact Or.inl hf)
        subst hf hv
        rw [hfn] at hfn'; cases hfn'
        obtain ⟨hf⟩ := hnone _ (List.mem_singleton.mpr rfl)
        cases hf [(0, int 0)]
          (fun i _ s h => by
            match i, h with
            | 0, h => cases h; exact ⟨_, rfl, by decide +kernel⟩)
          (.cons (.var rfl) .nil) with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd (Holds.top_eq hp) (by simp))
      (fun {f fn vs cl _ _ _} hfn' hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => by
        refine Or.inl fun hf => ?_
        subst hf
        rw [hfn] at hfn'; cases hfn'
        simp only [fnF, List.mem_singleton] at hmem
        subst hmem
        cases ht)
      (fun {f fn vs cl _ _} hfn' hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => by
        refine Or.inl fun hf => ?_
        subst hf
        rw [hfn] at hfn'; cases hfn'
        simp only [fnF, List.mem_singleton] at hmem
        subst hmem
        exact hne rfl)
      (fun {f fn vs cl _} hfn' hmem hne _ _ _ _ _ _ _ _ _ _ _ => by
        refine Or.inl fun hf => ?_
        subst hf
        rw [hfn] at hfn'; cases hfn'
        simp only [fnF, List.mem_singleton] at hmem
        subst hmem
        exact hne rfl)
      (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
      (fun h => by simp [fApp] at h) (fun h => by simp [fApp] at h) (fun _ _ h => by simp [fApp] at h)
      (fun {_ f _ _} hk' _ _ h => by
        simp only [fApp, Term.app.injEq] at h; rw [h.1, hk] at hk'; cases hk')
      (fun {_ f _ _ _} _ hhk _ _ _ _ h => by
        simp only [fApp, Term.app.injEq] at h; rw [h.1, hh] at hhk; cases hhk)
      (fun {_ f _ _ _} _ _ hp' _ _ _ h => by
        simp only [fApp, Term.app.injEq] at h; rw [h.1, hp] at hp'; cases hp')
      (fun {_ f ts rs vs _} _ _ hts hvs _ _ _ ihf h => by
        simp only [fApp, Term.app.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases hts with
        | cons h1 h2 =>
          cases h1; cases h2
          simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
          subst hvs
          rcases ihf with h | h
          · exact h rfl
          · exact h rfl)
      (fun {_ f ts rs} _ _ hts hvs _ _ h => by
        simp only [fApp, Term.app.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases hts with
        | cons h1 h2 => cases h1; cases h2; simp [allSome] at hvs)
      (fun {_ f _ _} _ ho' _ _ _ h => by
        simp only [fApp, Term.app.injEq] at h; rw [h.1, ho] at ho'; cases ho')
      (fun {_ f _ _ _ _ _ _} _ ho' _ _ _ _ _ _ _ h => by
        simp only [fApp, Term.app.injEq] at h; rw [h.1, ho] at ho'; cases ho')
      trivial (fun _ _ _ _ => trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
      h
  exact key rfl

def cfg (n : Int) : GroundTerm := .ctor topLabel [.ctor kIds.label [.ctor dotk []], .ctor counterLabel [int n]]

theorem cfg_sort0 : c.sortOf (cfg 0) = some topCellSort := by decide +kernel
theorem cfg_sort2 : c.sortOf (cfg 2) = some topCellSort := by decide +kernel

def σ₀ : Subst := [(0, .ctor dotk []), (1, int 0)]

theorem hσ (d : Semantics) (hk : d.sortOf (.ctor dotk []) = some Srt.k) (hi : d.sortOf (int 0) = some Srt.int) :
    d.WellSorted [Srt.k, Srt.int] σ₀ := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, hk⟩
  | 1, h => cases h; exact ⟨_, rfl, hi⟩

theorem hmatch (d : Semantics) (hc1 : d.isCtor topLabel = true) (hc2 : d.isCtor kIds.label = true)
    (hc3 : d.isCtor counterLabel = true) : PatVal d σ₀ lhs (cfg 0) :=
  .ctor hc1 (.cons (.ctor hc2 (.cons (.var rfl) .nil)) (.cons (.ctor hc3 (.cons (.var rfl) .nil)) .nil))

theorem andCtor : c.isCtor boolAnd = false := by decide +kernel

def A : Config c := ⟨cfg 0, cfg_sort0⟩
def B : Config c := ⟨cfg 2, cfg_sort2⟩

/-- With the field, `r2` steps: `r1`'s `requires` is false. -/
theorem field_steps : Step c A B :=
  .rule r2 (by simp [c]) σ₀ (hσ c (by decide +kernel) (by decide +kernel))
    (hmatch c (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (fun t h => by cases h) .top
    (.ctor (by decide +kernel)
      (.cons (.ctor (by decide +kernel) (.cons (.var (i := 0)) .nil))
        (.cons (.ctor (by decide +kernel) (.cons .dv .nil)) .nil)))
    (fun t h => by cases h) .top
    (fun r' h hlt => by
      simp only [c, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · intro σ _ _
        exact .intro rfl .dv (by decide)
      · exact absurd hlt (by decide))

/-- `false andBool F(0)` has no result. -/
theorem conj_no_result {d : Semantics} (hd : d = conjSem c) {σ : Subst} {u : Option GroundTerm} :
    ¬ EvalTerm d σ (.app boolAnd [.dv Srt.bool (.bool false), fApp]) u := by
  subst hd
  intro h
  obtain ⟨_, rb, _, hb, _⟩ := (hook2_iff (c := conjSem c) andCtor isHook_and).mp h
  exact no_result (evalTerm_rules_back _ hb)

/-- **B-conj (1) fails without `EnsDefined`**: the field steps from A to B, the conjunct reading
does not. -/
theorem conj_step_needs_defined :
    Step c A B ∧ ¬ Step (conjSem c) (Config.toRules _ A) (Config.toRules _ B) := by
  refine ⟨field_steps, fun h => ?_⟩
  cases h with
  | rule r mem σ _ _ hreq _ _ _ _ hprio =>
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp mem
    simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact conj_no_result rfl (hreq _ rfl)
    · obtain ⟨_, _, ht, he, -⟩ := (hprio (conjOf r1) (List.mem_map_of_mem (by simp [c])) (by decide) σ₀
        ((hσ _ (by decide +kernel) (by decide +kernel)).at _)
        (hmatch _ (by decide +kernel) (by decide +kernel) (by decide +kernel))).req_of_top rfl
      simp only [conjOf, conj, r1, Option.some.injEq] at ht
      subst ht
      exact conj_no_result rfl he

end NeedsDefined

end EnsBridge

#print axioms EnsBridge.guard_true
#print axioms EnsBridge.guard_some
#print axioms EnsBridge.guard_none
#print axioms EnsBridge.guard_no_value
#print axioms EnsBridge.guard_step
#print axioms EnsBridge.guard_notApplies
#print axioms EnsBridge.conj_step
#print axioms EnsBridge.step_of_conj
#print axioms EnsBridge.conj_notApplies
#print axioms EnsBridge.notApplies_of_conj
#print axioms EnsBridge.NeedsDefined.conj_step_needs_defined
