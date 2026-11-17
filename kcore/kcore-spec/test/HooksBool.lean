/-
  The supported hook rows of BOOL (10), KEQUAL (3) and KVAR (1) of test/constructs/rows.toml, each
  with its three statements (DONE-0 C2, evidence of a `supported` hook): one in-domain value; for each
  region the builtin prose excludes or leaves unstated, that Γ over all interpretations entails
  neither ⊥ nor a value at a point of it; and that the hook's silent predicate in `silentTable` is
  that region, or why the prose covers every argument list. Run from the package root:
  `lake env lean test/HooksBool.lean`.

  The expected side is the builtin prose: `domains.md:LINE` is K 7.1.337's
  k-distribution/include/kframework/builtin/domains.md, `substitution.md:LINE` the file beside it.
  No value here is taken from a run.

  None of the fourteen rows has a region the prose excludes or leaves unstated, so none has the
  second statement, and none is a key of `silentTable` (`no_key`). Per row, why:

  | row | prose | every argument list |
  |---|---|---|
  | `BOOL.Bool` (sort) | domains.md:1084 "The boolean values are `true` and `false`"; 1088, 1093-1094 | the sort's values are the two literals (`bool_values`, `bool_only`) |
  | `BOOL.not` | 1106 "Negate a boolean value"; `total` 1120; equations 1138-1139 | the two equations are the two values |
  | `BOOL.and` | 1107; `total` 1121; equations 1141, 1143 | 1141 at a first argument `true`, 1143 at `false` |
  | `BOOL.andThen` | 1107, 1115; `total` 1122; equations 1146, 1148 | as `and` |
  | `BOOL.xor` | 1108; `total` 1123; equations 1151, 1153 | 1151 at a first argument `false`, 1153 at (`true`, `true`); (`true`, `false`) by 1108's "XOR" and by 1152, which is a `[simplification]` |
  | `BOOL.or` | 1109; `total` 1124; equations 1155, 1157 | 1155 at a first argument `true`, 1157 at `false` |
  | `BOOL.orElse` | 1109, 1115; `total` 1125; equations 1160, 1162 | as `or` |
  | `BOOL.implies` | 1110-1111 "the same as `notBool P orBool Q`"; `total` 1126; equations 1165, 1166 | 1165 at a first argument `true`, 1166 at `false` |
  | `BOOL.eq` | 1112 "Check equality of two boolean values"; `total` 1128 | no equation: 1112 at each of the four pairs of 1084's two values |
  | `BOOL.ne` | 1113; `total` 1129; equation 1170 | 1170 at every pair, through `==Bool` and `notBool` |
  | `KEQUAL.eq` | 2312-2313 "Returns `true` if they are equal and `false` if they are not equal"; `total` 2325 | two terms are equal or not (`kEq_all`) |
  | `KEQUAL.ne` | `total` 2326; equation 2355 | 2355 at every pair (`kNe_all`) |
  | `KEQUAL.ite` | 2314-2316; `total` 2330; equations 2357, 2358 | 2357 at a condition `true`, 2358 at `false` (`kIte_all`) |
  | `KVAR.KVar` (sort) | substitution.md:44 `syntax KVar [token, hook(KVAR.KVar)]` | a token sort: every token literal is a value (`kvar_values`); no symbol, so no silent predicate |

  Statements:
  - **(1) values.** `vals`: the whole truth table of the nine BOOL symbols (34 points), each value
    written from the equation or sentence named beside it. For every semantics and every
    interpretation the result is that value and Γ states it (`vals_gamma`). `==K`, `=/=K` and `ite`
    at points of a semantics with Bool below KItem (`kvals`, `kvals_gamma`), and at every argument
    list for every interpretation (`kEq_all`, `kNe_all`, `kIte_all`). The two sorts: `bool_values`,
    `kvar_values`.
  - **(2) no excluded or unstated region**, so no undetermined point (table above).
  - **(3) every argument list.** `no_key`: none of the twelve symbols is a key of `silentTable` and
    none is among `partialHooks`. `vals_complete`: in a semantics with `shapesOK`, every argument list
    of a BOOL symbol's argument sorts is a point of `vals`, so the table is all of the symbol.
    `covered`: each of the twelve has a value at every argument list of its sorts, for every
    interpretation (the library's `hook_total`), so Γ's ⊥ item for a point without a value is at no
    argument list of theirs.

  Readings, marked:
  - `andThenBool`, `orElseBool`: "only `andThenBool` and `orElseBool` are short-circuiting"
    (1115-1117) speaks of whether an argument is evaluated. An argument list here is of values, where
    the equations 1146, 1148, 1160, 1162 are `andBool`'s and `orBool`'s 1141, 1143, 1155, 1157. What
    an argument without a value gives is not a statement of this file.
  - `ite` is declared at every sort (`{Sort}`, 2330); `hookSigs` holds its signature at KItem, and
    `kIte_all` is stated at every pair of terms.
  - `KVAR.KVar`: substitution.md:38-40 gives the syntax of KVar tokens in a program
    (`[A-Za-z_][A-Za-z0-9_]*`, `#LowerId`, `#UpperId`), and 50 declares `String2KVar(String)` `total`.
    The carrier of a token sort is every string (`kvar_values` at `"1x"`), which is no region of a
    hook: the row is a sort.
    Finding: the row `hook:KVAR.KVar:SortKVar` of rows.toml has status `supported`, and the reader
    refuses the sentence: test/constructs/fixtures/e2-binder/account.txt lists
    `hooked-sort SortKVar{} [hasDomainValues{}(), hook{}("KVAR.KVar"), …, token{}()]` under
    `refused builtinText` (the row's evidence says "extend to this hooked sort"). `kvar_values` and
    `kvar_at` are about a token sort of a semantics (`Lib.tokenSorts`), the carrier the row names;
    nothing here ties them to KVar as read from a kompiled text.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HooksBoolTest

open KCore ML Faithful

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, nofun, rfl⟩)))))

/-! ## BOOL's nine symbols -/

/-- A point of a BOOL symbol: its Bool arguments and its value. -/
structure BPt where
  f : Sym
  bs : List Bool
  r : Bool
  deriving DecidableEq

/-- The truth table of each symbol, from the prose (domains.md):
`notBool` 1138, 1139; `andBool` 1141 (`true andBool B => B`), 1143 (`false andBool _ => false`);
`andThenBool` 1146, 1148; `xorBool` 1151 (`false xorBool B => B`), 1153 (`B xorBool B => false`),
and (`true`, `false`) by 1108 ("XOR") and the simplification 1152 (`B xorBool false => B`);
`orBool` 1155 (`true orBool _ => true`), 1157 (`false orBool B => B`); `orElseBool` 1160, 1162;
`impliesBool` 1165 (`true impliesBool B => B`), 1166 (`false impliesBool _ => true`);
`==Bool` 1112 (equality of the two values); `=/=Bool` 1170 (`notBool (B1 ==Bool B2)`). -/
def vals : List BPt :=
  [⟨boolNot, [true], false⟩, ⟨boolNot, [false], true⟩,
   ⟨boolAnd, [true, true], true⟩, ⟨boolAnd, [true, false], false⟩,
   ⟨boolAnd, [false, true], false⟩, ⟨boolAnd, [false, false], false⟩,
   ⟨boolAndThen, [true, true], true⟩, ⟨boolAndThen, [true, false], false⟩,
   ⟨boolAndThen, [false, true], false⟩, ⟨boolAndThen, [false, false], false⟩,
   ⟨boolXor, [true, true], false⟩, ⟨boolXor, [true, false], true⟩,
   ⟨boolXor, [false, true], true⟩, ⟨boolXor, [false, false], false⟩,
   ⟨boolOr, [true, true], true⟩, ⟨boolOr, [true, false], true⟩,
   ⟨boolOr, [false, true], true⟩, ⟨boolOr, [false, false], false⟩,
   ⟨boolOrElse, [true, true], true⟩, ⟨boolOrElse, [true, false], true⟩,
   ⟨boolOrElse, [false, true], true⟩, ⟨boolOrElse, [false, false], false⟩,
   ⟨boolImplies, [true, true], true⟩, ⟨boolImplies, [true, false], false⟩,
   ⟨boolImplies, [false, true], true⟩, ⟨boolImplies, [false, false], true⟩,
   ⟨boolEq, [true, true], true⟩, ⟨boolEq, [true, false], false⟩,
   ⟨boolEq, [false, true], false⟩, ⟨boolEq, [false, false], true⟩,
   ⟨boolNe, [true, true], false⟩, ⟨boolNe, [true, false], true⟩,
   ⟨boolNe, [false, true], true⟩, ⟨boolNe, [false, false], false⟩]

def unary : List Sym := [boolNot]
def binary : List Sym := [boolAnd, boolAndThen, boolXor, boolOr, boolOrElse, boolImplies, boolEq, boolNe]
def kSyms : List Sym := [kEq, kNe, kIte]

/-- The twelve supported operation rows: the symbol and its `hook` attribute in the prose's
productions (domains.md:1120-1129 `BOOL.not`, `and`, `andThen`, `xor`, `or`, `orElse`, `implies`,
`eq`, `ne`; 2325 `KEQUAL.eq`, 2326 `KEQUAL.ne`, 2330 `KEQUAL.ite`). The other two rows are sorts
(`BOOL.Bool`, 1088; `KVAR.KVar`, substitution.md:44). -/
def rows : List (Sym × String) :=
  [(boolNot, "BOOL.not"), (boolAnd, "BOOL.and"), (boolAndThen, "BOOL.andThen"), (boolXor, "BOOL.xor"),
   (boolOr, "BOOL.or"), (boolOrElse, "BOOL.orElse"), (boolImplies, "BOOL.implies"),
   (boolEq, "BOOL.eq"), (boolNe, "BOOL.ne"),
   (kEq, "KEQUAL.eq"), (kNe, "KEQUAL.ne"), (kIte, "KEQUAL.ite")]

/-- The rows are the registry's entries with a `BOOL.` or `KEQUAL.` hook (no entry has a `KVAR.`
hook), and their symbols are `unary ++ binary ++ kSyms`. -/
theorem rows_registry :
    ((regHookNames.filter (fun e => e.2.toList.take 5 == "BOOL.".toList ||
        e.2.toList.take 7 == "KEQUAL.".toList)).all rows.contains &&
    rows.all regHookNames.contains &&
    decide (rows.map (·.1) = unary ++ binary ++ kSyms) &&
    !regHookNames.any (fun e => e.2.toList.take 5 == "KVAR.".toList)) = true := by
  decide +kernel

/-- Each point: the symbol's signature, as many Bool arguments as it has argument sorts, all Bool,
and `hook`'s value the table's. -/
theorem vals_ok : vals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.bs.map (fun _ => Srt.bool) &&
    hook p.f (p.bs.map bool) == some (some (bool p.r))) = true := by
  decide +kernel

theorem bools_sorts (c : Semantics) (bs : List Bool) :
    c.sortsOf (bs.map bool) = some (bs.map fun _ => Srt.bool) := by
  have h := sortsOf_const (c := c) (es := bs.map bool) (s := Srt.bool) (by
    intro e he
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp he
    exact sortOf_bool b)
  rw [h, List.map_map]; rfl

/-- **(1) Each point of the truth tables, for every semantics and every interpretation**: the result
is the table's value, and Γ states it. -/
theorem vals_gamma : ∀ p ∈ vals, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.bs.map bool) = some (some (bool p.r)) ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.bs.map bool) ≡ den (c.withHooks H) (bool p.r)) := by
  intro p hp c H
  have h := List.all_eq_true.mp vals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hargs⟩, hh⟩ := h
  refine ⟨Semantics.hookRes_of_value hh, ?_⟩
  exact gamma_val (c.withHooks H) hk (by rw [hargs]; exact bools_sorts _ _) (by rw [hname]; exact hh)

/-- The tables hold every list of Bool arguments of each symbol's length. -/
theorem vals_all :
    ((unary.all fun f => [true, false].all fun a => vals.any fun p => p.f == f && p.bs == [a]) &&
    (binary.all fun f => [true, false].all fun a => [true, false].all fun b =>
      vals.any fun p => p.f == f && p.bs == [a, b])) = true := by
  decide +kernel

theorem sigs_ok : ((unary.all fun f => (sig f).args == [Srt.bool]) &&
    (binary.all fun f => (sig f).args == [Srt.bool, Srt.bool])) = true := by
  decide +kernel

theorem args1 {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (h : c.sortsOf vs = some [Srt.bool]) : ∃ a, vs = [bool a] := by
  match vs, h with
  | [], h => simp [Semantics.sortsOf] at h
  | [v], h =>
    obtain ⟨s, ss, hv, -, he⟩ := sortsOf_cons.mp h
    cases he
    obtain ⟨a, rfl⟩ := shape_bool hs hv
    exact ⟨a, rfl⟩
  | v :: w :: ws, h =>
    obtain ⟨s, ss, -, h2, he⟩ := sortsOf_cons.mp h
    cases he
    obtain ⟨s', ss', -, -, he'⟩ := sortsOf_cons.mp h2
    cases he'

theorem args2 {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (h : c.sortsOf vs = some [Srt.bool, Srt.bool]) : ∃ a b, vs = [bool a, bool b] := by
  match vs, h with
  | [], h => simp [Semantics.sortsOf] at h
  | v :: ws, h =>
    obtain ⟨s, ss, hv, h2, he⟩ := sortsOf_cons.mp h
    cases he
    obtain ⟨a, rfl⟩ := shape_bool hs hv
    obtain ⟨b, rfl⟩ := args1 hs h2
    exact ⟨a, b, rfl⟩

/-- **(3) The truth tables are all of each symbol**: in a semantics with `shapesOK` (a value of sort
Bool is one of the two literals, domains.md:1084), under every interpretation, every argument list of
a BOOL symbol's argument sorts is a point of `vals`. -/
theorem vals_complete (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true) {f : Sym}
    (hf : f ∈ unary ++ binary) {vs : List GroundTerm}
    (hvs : (c.withHooks H).sortsOf vs = some (sig f).args) : ∃ p ∈ vals, p.f = f ∧ vs = p.bs.map bool := by
  have hall := vals_all
  have hsig := sigs_ok
  simp only [Bool.and_eq_true] at hall hsig
  rcases List.mem_append.mp hf with hu | hb
  · have ha := List.all_eq_true.mp hsig.1 f hu
    rw [beq_iff_eq] at ha
    rw [ha] at hvs
    obtain ⟨a, rfl⟩ := args1 hs hvs
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hall.1 f hu) a (by cases a <;> simp)
    obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp h1
    simp only [Bool.and_eq_true, beq_iff_eq] at hpe
    exact ⟨p, hp, hpe.1, by rw [hpe.2]; rfl⟩
  · have ha := List.all_eq_true.mp hsig.2 f hb
    rw [beq_iff_eq] at ha
    rw [ha] at hvs
    obtain ⟨a, b, rfl⟩ := args2 hs hvs
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hall.2 f hb) a (by cases a <;> simp))
      b (by cases b <;> simp)
    obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp h1
    simp only [Bool.and_eq_true, beq_iff_eq] at hpe
    exact ⟨p, hp, hpe.1, by rw [hpe.2]; rfl⟩

/-! ## No silent key, and a value at every argument list -/

/-- **(3) None of the twelve symbols is a key of `silentTable`**, none is among `partialHooks`, and
each has its signature in `hookSigs`. -/
theorem no_key : (unary ++ binary ++ kSyms).all (fun f => !silentKey f && !partialHooks.contains f &&
    decide (sig f ∈ hookSigs) && (sig f).name == f) = true := by
  decide +kernel

/-- **(3) Each of the twelve has a value at every argument list of its sorts, whatever the
interpretation** (`hook_total`): Γ's ⊥ item is at no argument list of theirs. -/
theorem covered (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true) {f : Sym}
    (hf : f ∈ unary ++ binary ++ kSyms) {vs : List GroundTerm}
    (hvs : (c.withHooks H).sortsOf vs = some (sig f).args) :
    ∃ v, (c.withHooks H).hookRes f vs = some (some v) := by
  have h := List.all_eq_true.mp no_key f hf
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨-, hp⟩, hk⟩, hname⟩ := h
  obtain ⟨v, hv⟩ := hook_total hs (sig f) hk (by rw [hname]; exact hp) vs hvs
  rw [hname] at hv
  exact ⟨v, Semantics.hookRes_of_value hv⟩

/-! ## KEQUAL's three symbols -/

/-- `==K` at every pair of terms: `true` if they are equal and `false` if they are not
(domains.md:2312-2313). -/
theorem kEq_hook (a b : GroundTerm) : hook kEq [a, b] = some (some (bool (decide (a = b)))) := by
  rw [hook_eq]
  have hf : hookTable.find? (·.1 == kEq) = some (kEq, fun vs => match vs with
      | [a, b] => some (bool (GroundTerm.cmp a b == .eq)) | _ => none) := rfl
  rw [hf]
  have hc : (GroundTerm.cmp a b == .eq) = decide (a = b) := by
    by_cases h : a = b
    · subst h; simp [GroundTerm.cmp_refl]
    · have hne : GroundTerm.cmp a b ≠ .eq := fun h' => h (cmp_eq_iff.mp h')
      simp [h, hne]
  simp only [Option.map_some, hc]

/-- `=/=K` at every pair of terms: `notBool (K1 ==K K2)` (domains.md:2355). -/
theorem kNe_hook (a b : GroundTerm) : hook kNe [a, b] = some (some (bool (!decide (a = b)))) := by
  rw [hook_eq]
  have hf : hookTable.find? (·.1 == kNe) = some (kNe, fun vs => match vs with
      | [a, b] => some (bool (GroundTerm.cmp a b != .eq)) | _ => none) := rfl
  rw [hf]
  have hc : (GroundTerm.cmp a b != .eq) = !decide (a = b) := by
    by_cases h : a = b
    · subst h; simp [GroundTerm.cmp_refl]
    · have hne : GroundTerm.cmp a b ≠ .eq := fun h' => h (cmp_eq_iff.mp h')
      simp [h, hne]
  simp only [Option.map_some, hc]

/-- `#if C #then B1 #else B2 #fi` at every condition and pair of terms: `B1` at `true` (domains.md:2357),
`B2` at `false` (2358). -/
theorem kIte_hook (b : Bool) (x y : GroundTerm) :
    hook kIte [bool b, x, y] = some (some (if b then x else y)) := by
  rw [hook_eq]
  have hf : hookTable.find? (·.1 == kIte) = some (kIte, fun vs => match vs with
      | [c, x, y] => (asBool c).map fun b => if b then x else y | _ => none) := rfl
  rw [hf]
  cases b <;> rfl

/-- **(1), (3) `==K` for every semantics, interpretation and pair of terms.** -/
theorem kEq_all (c : Semantics) (H : HookParams) (a b : GroundTerm) :
    (c.withHooks H).hookRes kEq [a, b] = some (some (bool (decide (a = b)))) :=
  Semantics.hookRes_of_value (kEq_hook a b)

/-- **(1), (3) `=/=K` likewise.** -/
theorem kNe_all (c : Semantics) (H : HookParams) (a b : GroundTerm) :
    (c.withHooks H).hookRes kNe [a, b] = some (some (bool (!decide (a = b)))) :=
  Semantics.hookRes_of_value (kNe_hook a b)

/-- **(1), (3) `ite` likewise**, at every condition and pair of terms. -/
theorem kIte_all (c : Semantics) (H : HookParams) (b : Bool) (x y : GroundTerm) :
    (c.withHooks H).hookRes kIte [bool b, x, y] = some (some (if b then x else y)) :=
  Semantics.hookRes_of_value (kIte_hook b x y)

/-- A semantics with Int, String and Bool below KItem and nothing of its own. -/
def sem : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.string, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

theorem sem_noRaw : ∀ k ∈ sem.params, k.raw = false := by decide +kernel

/-- A Bool as a KItem, and as a K. -/
def kb (b : Bool) : GroundTerm := .inj Srt.bool Srt.kitem (bool b)
def kk (b : Bool) : GroundTerm := .ctor kseq [kb b, .ctor dotk []]

structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm
  deriving DecidableEq

/-- `true ==K true` and `true ==K false` (2312-2313), `=/=K` at the same (2355), `ite` at `true`
(2357) and at `false` (2358). -/
def kvals : List Pt :=
  [⟨kEq, [kk true, kk true], bool true⟩, ⟨kEq, [kk true, kk false], bool false⟩,
   ⟨kNe, [kk true, kk true], bool false⟩, ⟨kNe, [kk true, kk false], bool true⟩,
   ⟨kIte, [bool true, kb true, kb false], kb true⟩, ⟨kIte, [bool false, kb true, kb false], kb false⟩]

theorem kvals_ok : kvals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    sem.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- **(1) Γ states each of `kvals`, for every interpretation.** -/
theorem kvals_gamma : ∀ p ∈ kvals, ∀ H : HookParams,
    (sem.withHooks H).hookRes p.f p.vs = some (some p.v) ∧
    Γ (sem.withHooks H) (appP (sem.withHooks H) (sig p.f) p.vs ≡ den (sem.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp kvals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  refine ⟨Semantics.hookRes_of_value hh, ?_⟩
  exact gamma_val (sem.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ sem_noRaw]; exact hvs)
    (by rw [hname]; exact hh)

/-! ## The two sorts -/

/-- **`BOOL.Bool` (1)**: `true` and `false` are values of sort Bool (domains.md:1084), in every
semantics under every interpretation. -/
theorem bool_values (c : Semantics) (H : HookParams) (b : Bool) :
    (c.withHooks H).sortOf (bool b) = some Srt.bool := sortOf_bool b

/-- **`BOOL.Bool` (3)**: and they are its only values ("The boolean values are `true` and `false`"),
in a semantics with `shapesOK`. -/
theorem bool_only (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true) {v : GroundTerm}
    (hv : (c.withHooks H).sortOf v = some Srt.bool) : v = bool true ∨ v = bool false := by
  obtain ⟨b, rfl⟩ := shape_bool hs hv
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **`KVAR.KVar` (1), (3)**: at a token sort `s` of the semantics (substitution.md:44: `KVar` is
declared `token`), every token literal is a value of `s`, under every interpretation; no symbol is
involved, so there is no silent predicate. -/
theorem kvar_values (c : Semantics) (H : HookParams) {s : Srt} (hc : (c.withHooks H).lib.carrier s = s)
    (ht : (c.withHooks H).lib.tokenSorts.contains s = true) (t : String) :
    (c.withHooks H).sortOf (.dv s (.tok t)) = some s :=
  sortOf_dv.mpr ⟨by simp only [dvOK, hc, ht, Bool.or_true, Bool.true_or], rfl⟩

/-- `sem` with one token sort, the first sort number after the registry's. -/
def semK : Semantics :=
  { sem with lib := { sortsBelowKItem := [Srt.int, Srt.string, Srt.bool], tokenSorts := [nRegSorts] } }

theorem semK_lit : dvOK semK.lib nRegSorts (.bool true) = false ∧ dvOK semK.lib nRegSorts (.int 0) = false := by
  decide +kernel

/-- At `semK`: `x` and `1x` are values of the token sort, under every interpretation; a Bool and
an Int literal written at that sort are not. -/
theorem kvar_at (H : HookParams) :
    (semK.withHooks H).sortOf (.dv nRegSorts (.tok "x")) = some nRegSorts ∧
    (semK.withHooks H).sortOf (.dv nRegSorts (.tok "1x")) = some nRegSorts ∧
    (semK.withHooks H).sortOf (.dv nRegSorts (.bool true)) = none ∧
    (semK.withHooks H).sortOf (.dv nRegSorts (.int 0)) = none := by
  have hc : (semK.withHooks H).lib.carrier nRegSorts = nRegSorts := by
    show semK.lib.carrier nRegSorts = nRegSorts
    decide +kernel
  have ht : (semK.withHooks H).lib.tokenSorts.contains nRegSorts = true := by
    show semK.lib.tokenSorts.contains nRegSorts = true
    decide +kernel
  refine ⟨kvar_values semK H hc ht _, kvar_values semK H hc ht _, ?_, ?_⟩
  · cases h : (semK.withHooks H).sortOf (.dv nRegSorts (.bool true)) with
    | none => rfl
    | some t => exact absurd (sortOf_dv.mp h).1 (by show ¬ dvOK semK.lib _ _ = true; rw [semK_lit.1]; decide)
  · cases h : (semK.withHooks H).sortOf (.dv nRegSorts (.int 0)) with
    | none => rfl
    | some t => exact absurd (sortOf_dv.mp h).1 (by show ¬ dvOK semK.lib _ _ = true; rw [semK_lit.2]; decide)

#print axioms vals_gamma
#print axioms vals_complete
#print axioms no_key
#print axioms covered
#print axioms kEq_all
#print axioms kNe_all
#print axioms kIte_all
#print axioms kvals_gamma
#print axioms bool_values
#print axioms bool_only
#print axioms kvar_values
#print axioms kvar_at

end KCore.HooksBoolTest
