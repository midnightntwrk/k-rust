/-
  KCore. `lawHooks c H`: an interpretation of the parameters that satisfies the laws the text
  writes for its open generators (`OpenLaws`): the free one at an open generator with one law, the
  first-occurrence form at one with both (below). It is H at
  every parameter that is no open generator; at an open generator f (a `raw` parameter) it gives
  the application of f itself, read up to the laws the text writes for f: where f is associative
  (`assoc`) the arguments are flattened (an argument that applies f is replaced by its own
  arguments) and the result is nested to the right; where f is idempotent (`idem`) alone, equal
  adjacent arguments are merged, and an application left with one argument is that argument; where f
  is both, each flattened argument is kept at its first occurrence only (`Band.nf`) and the result
  nested to the right, a single argument being that argument.

  It is the witness that the interpretations satisfying `OpenLaws` are not empty, not the meaning of
  the generator: the text says nothing of an open generator beyond its laws. With one law it is the
  free interpretation of that law; with both it is not (`x | y | x` and `x | y` are one value, which
  the two laws do not state), but it adds no commutativity (`x | y` and `y | x` are two values).
  Merging equal adjacent arguments would not do with both laws: `(x | y) | (x | y)` flattens to
  `x y x y`, which has no equal neighbours, while idempotence makes it `x | y`; the first-occurrence
  form makes it `x y` at every word (`Band.nf_idem`), and its form does not depend on the grouping
  (`Band.nf_left`, `Band.nf_right`).

  The list lemmas its theorems rest on: flattening a right nesting gives the flattened parts
  (`lawFlat_lawNest`), so flattening is idempotent (`lawFlat_lawNest_lawFlat`); a nesting of the
  flattening of a right nesting of atoms is that nesting (`lawNest_lawFlat`); the merge of equal
  adjacent elements is idempotent (`lawMerge_idem`).
-/
import KcoreSpec.Obligations
import KcoreSpec.Band
import KcoreSpec.Collections

set_option autoImplicit false

namespace KCore

/-- The arguments of `t` read through the associative symbol f: the leaves of the binary f-nodes
at its top, left to right. A term that applies no f at its top is its own one leaf. -/
def lawFlat (f : Sym) : GroundTerm → List GroundTerm
  | .ctor g [a, b] => if g == f then lawFlat f a ++ lawFlat f b else [.ctor g [a, b]]
  | t => [t]

/-- The right nesting of a list of terms under the binary symbol f: `f(t₁, f(t₂, … tₙ))`, a single
term itself; the empty list (no argument list of a binary symbol) is `f()`. -/
def lawNest (f : Sym) : List GroundTerm → GroundTerm
  | [] => .ctor f []
  | [t] => t
  | t :: ts => .ctor f [t, lawNest f ts]

/-- Equal adjacent elements merged into one. -/
def lawMerge : List GroundTerm → List GroundTerm
  | [] => []
  | [t] => [t]
  | t :: u :: ts => if Exec.same t u then lawMerge (u :: ts) else t :: lawMerge (u :: ts)

/-- The value of the open generator k at the arguments `vs`: the arguments flattened where `assoc`;
where `assoc` and `idem`, each kept at its first occurrence (`Band.nf`); where `idem` alone, equal
adjacent ones merged; nested to the right where `assoc`; an application merged to one argument is
that argument; otherwise the application itself. -/
def lawApp (k : ParamSig) (vs : List GroundTerm) : GroundTerm :=
  let f := k.sig.name
  let xs := if k.assoc then vs.flatMap (lawFlat f) else vs
  let ys := if k.assoc && k.idem then Band.nf xs else if k.idem then lawMerge xs else xs
  if k.assoc then lawNest f ys
  else if k.idem then (match ys with
    | [y] => y
    | _ => .ctor f ys)
  else .ctor f vs

/-- **`lawHooks c H`**: H everywhere except at the open generators of c (its `raw` parameters),
where it is `lawApp`: the right-nested application of the flattened arguments where `assoc`, each
at its first occurrence where also `idem`, equal adjacent arguments merged where `idem` alone. -/
def lawHooks (c : Semantics) (H : HookParams) : HookParams :=
  ⟨fun f vs => match c.params.find? (fun k => k.raw && k.sig.name == f) with
    | some k => some (lawApp k vs)
    | none => H.app f vs⟩

/-! ## The list lemmas -/

/-- A term is never flattened to nothing. -/
theorem lawFlat_ne_nil (f : Sym) : ∀ t, lawFlat f t ≠ []
  | .ctor g [a, b] => by
    unfold lawFlat
    split
    · intro h; exact lawFlat_ne_nil f a (List.append_eq_nil_iff.mp h).1
    · exact List.cons_ne_nil _ _
  | .ctor _ [] | .ctor _ [_] | .ctor _ (_ :: _ :: _ :: _) | .inj _ _ _ | .dv _ _ | .map _ _ | .set _ _
  | .list _ _ => by simp [lawFlat]

/-- Each leaf of a flattening is its own one leaf. -/
theorem lawFlat_leaf (f : Sym) : ∀ t, ∀ x ∈ lawFlat f t, lawFlat f x = [x]
  | .ctor g [a, b], x, hx => by
    unfold lawFlat at hx
    split at hx
    · rcases List.mem_append.mp hx with h | h
      · exact lawFlat_leaf f a x h
      · exact lawFlat_leaf f b x h
    · rename_i hg
      rw [List.mem_singleton] at hx; subst hx
      simp [lawFlat, hg]
  | .ctor _ [], x, hx | .ctor _ [_], x, hx | .ctor _ (_ :: _ :: _ :: _), x, hx | .inj _ _ _, x, hx
  | .dv _ _, x, hx | .map _ _, x, hx | .set _ _, x, hx | .list _ _, x, hx => by
    simp only [lawFlat, List.mem_singleton] at hx; subst hx; simp [lawFlat]

/-- **Flattening a nesting** gives the flattened parts, at a nonempty list. -/
theorem lawFlat_lawNest (f : Sym) : ∀ ts : List GroundTerm, ts ≠ [] →
    lawFlat f (lawNest f ts) = ts.flatMap (lawFlat f)
  | [], h => absurd rfl h
  | [t], _ => by simp [lawNest]
  | t :: u :: ts, _ => by
    rw [show lawNest f (t :: u :: ts) = .ctor f [t, lawNest f (u :: ts)] from rfl]
    simp only [lawFlat, beq_self_eq_true, ↓reduceIte]
    rw [lawFlat_lawNest f (u :: ts) (List.cons_ne_nil _ _)]
    simp [List.flatMap_cons]

/-- Flattening the nesting of a flattening gives the flattening back. -/
theorem lawFlat_lawNest_lawFlat (f : Sym) (t : GroundTerm) :
    lawFlat f (lawNest f (lawFlat f t)) = lawFlat f t := by
  rw [lawFlat_lawNest f _ (lawFlat_ne_nil f t)]
  have : ∀ xs : List GroundTerm, (∀ x ∈ xs, lawFlat f x = [x]) → xs.flatMap (lawFlat f) = xs := by
    intro xs h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons, h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
      rfl
  exact this _ (lawFlat_leaf f t)

/-- **The nesting of a flattening**: the right nesting of a nonempty list of leaves (terms that are
their own one leaf) flattens to that list, so nesting its flattening gives it back. -/
theorem lawNest_lawFlat (f : Sym) (ts : List GroundTerm) (hne : ts ≠ [])
    (hl : ∀ t ∈ ts, lawFlat f t = [t]) : lawNest f (lawFlat f (lawNest f ts)) = lawNest f ts := by
  rw [lawFlat_lawNest f ts hne]
  congr 1
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, hl t (List.mem_cons_self ..)]
    cases ts with
    | nil => rfl
    | cons u us =>
      rw [ih (List.cons_ne_nil _ _) fun x hx => hl x (List.mem_cons_of_mem _ hx)]
      rfl

/-- The merge keeps the first element. -/
theorem lawMerge_head : ∀ (t : GroundTerm) (ts : List GroundTerm), ∃ rest, lawMerge (t :: ts) = t :: rest
  | t, [] => ⟨[], rfl⟩
  | t, u :: ts => by
    obtain ⟨rest, hr⟩ := lawMerge_head u ts
    unfold lawMerge
    split
    · rename_i h
      rw [Exec.same_iff] at h; subst h
      exact ⟨rest, hr⟩
    · exact ⟨_, rfl⟩

/-- After the merge no two adjacent elements are equal. -/
def lawNoAdj : List GroundTerm → Prop
  | t :: u :: ts => Exec.same t u = false ∧ lawNoAdj (u :: ts)
  | _ => True

theorem lawMerge_noAdj : ∀ ts : List GroundTerm, lawNoAdj (lawMerge ts)
  | [] => trivial
  | [_] => trivial
  | t :: u :: ts => by
    have ih := lawMerge_noAdj (u :: ts)
    unfold lawMerge
    split
    · exact ih
    · rename_i h
      obtain ⟨rest, hr⟩ := lawMerge_head u ts
      rw [hr] at ih ⊢
      exact ⟨by simpa using h, ih⟩

/-- A list with no two equal adjacent elements is its own merge. -/
theorem lawMerge_of_noAdj : ∀ ts : List GroundTerm, lawNoAdj ts → lawMerge ts = ts
  | [], _ => rfl
  | [_], _ => rfl
  | t :: u :: ts, ⟨h, hr⟩ => by
    unfold lawMerge
    rw [h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lawMerge_of_noAdj (u :: ts) hr]

/-- **The merge is idempotent.** -/
theorem lawMerge_idem (ts : List GroundTerm) : lawMerge (lawMerge ts) = lawMerge ts :=
  lawMerge_of_noAdj _ (lawMerge_noAdj ts)

/-! ## The interpretation -/

/-- `lawHooks` is H off the open generators. -/
theorem lawHooks_app_of_find_none {c : Semantics} {H : HookParams} {f : Sym} {vs : List GroundTerm}
    (h : c.params.find? (fun k => k.raw && k.sig.name == f) = none) : (lawHooks c H).app f vs = H.app f vs := by
  simp [lawHooks, h]

/-- At an open generator, `lawHooks` gives the free application of its laws. -/
theorem lawHooks_app_of_find {c : Semantics} {H : HookParams} {f : Sym} {vs : List GroundTerm} {k : ParamSig}
    (h : c.params.find? (fun k => k.raw && k.sig.name == f) = some k) :
    (lawHooks c H).app f vs = some (lawApp k vs) := by
  simp [lawHooks, h]

/-! ## The laws at `lawHooks`

`OpenLaws` and `OpenTotal` hold at `lawHooks c H` for every H, for a semantics whose raw parameters
are each the parameter and the open generator their name finds, with no registry hook, named apart
from the constructors and the overloading symbols, of two arguments of their result sort where they
have a law (`LawShape`), and none with both laws. An application of the open generator at values is
then a value exactly where `lawApp` gives it back (`law_sortOf_iff`): the right nesting of leaves of
its sort (`law_nest_sorted`), whose flattening is those leaves (`lawFlat_lawNest`); so `lawApp` at
values of the sort is a value of it (`law_assoc_val`), and the associativity sentence holds at
values because both groupings flatten to the same leaves. -/

/-- What the theorems on `lawHooks` read of a raw parameter k: k is the parameter and the open
generator its name finds, with no registry hook, its name no constructor's and no overloading
symbol's, and where it has a law its two arguments are of its result sort. -/
def LawShape (c : Semantics) (k : ParamSig) : Prop :=
  c.lookupParam k.sig.name = some k ∧ c.lookupOpen k.sig.name = some k ∧ k.impl = none ∧
    lookupSig c.ctorSigs k.sig.name = none ∧ c.lookupOvl k.sig.name = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result])

instance (c : Semantics) (k : ParamSig) : Decidable (LawShape c k) := by
  unfold LawShape; infer_instance

/-- Leaves are their own flattening. -/
theorem lawFlat_flatMap_leaves (f : Sym) : ∀ xs : List GroundTerm, (∀ x ∈ xs, lawFlat f x = [x]) →
    xs.flatMap (lawFlat f) = xs
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatMap_cons, h x (List.mem_cons_self ..),
      lawFlat_flatMap_leaves f xs fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem lawApp_assoc {k : ParamSig} (ha : k.assoc = true) (hi : k.idem = false) (vs : List GroundTerm) :
    lawApp k vs = lawNest k.sig.name (vs.flatMap (lawFlat k.sig.name)) := by
  simp [lawApp, ha, hi]

theorem lawApp_plain {k : ParamSig} (ha : k.assoc = false) (hi : k.idem = false) (vs : List GroundTerm) :
    lawApp k vs = .ctor k.sig.name vs := by
  simp [lawApp, ha, hi]

section
variable {c : Semantics} {H : HookParams} {k : ParamSig}

/-- At its own name, `lawHooks` gives `lawApp k`. -/
theorem lawHooks_app_self (hs : LawShape c k) (vs : List GroundTerm) :
    (lawHooks c H).app k.sig.name vs = some (lawApp k vs) := by
  apply lawHooks_app_of_find
  have h := hs.2.1
  unfold Semantics.lookupOpen at h
  split at h
  · exact h
  · cases h

/-- **An application of the open generator is a value at `lawHooks`** exactly where its arguments
are values of its argument sorts and `lawApp` gives it back; it is then of the result sort. -/
theorem law_sortOf_iff (hs : LawShape c k) {ts : List GroundTerm} {s : Srt} :
    (c.withHooks (lawHooks c H)).sortOf (.ctor k.sig.name ts) = some s ↔
      (c.withHooks (lawHooks c H)).sortsOf ts = some k.sig.args ∧ lawApp k ts = .ctor k.sig.name ts ∧
        s = k.sig.result := by
  rw [Semantics.sortOf_open_iff (c := c.withHooks (lawHooks c H)) hs.2.1 hs.2.2.2.1 hs.2.2.2.2.1]
  have hk : (c.withHooks (lawHooks c H)).keepsRaw k.sig.name ts = true ↔ lawApp k ts = .ctor k.sig.name ts := by
    unfold Semantics.keepsRaw
    rw [show (c.withHooks (lawHooks c H)).hooks.app k.sig.name ts = some (lawApp k ts) from lawHooks_app_self hs ts]
    simp [cmp_eq_iff]
  rw [hk]

/-- **The open generator's value at `lawHooks`**: `lawApp k`, where that has the result sort. -/
theorem law_paramVal (hs : LawShape c k) (hr : k.raw = true) {vs : List GroundTerm} {v : GroundTerm} :
    (c.withHooks (lawHooks c H)).paramVal k.sig.name vs = some v ↔
      v = lawApp k vs ∧ (c.withHooks (lawHooks c H)).sortOf v = some k.sig.result := by
  rw [paramVal_raw_sorted (c := c.withHooks (lawHooks c H)) hs.1 hr hs.2.2.1,
    show (c.withHooks (lawHooks c H)).hooks.app k.sig.name vs = some (lawApp k vs) from lawHooks_app_self hs vs]
  rfl

/-- The leaves of a value of the result sort are values of it. -/
theorem law_leaves_sorted (hs : LawShape c k) (hb : k.sig.args = [k.sig.result, k.sig.result]) :
    ∀ a, (c.withHooks (lawHooks c H)).sortOf a = some k.sig.result →
      ∀ x ∈ lawFlat k.sig.name a, (c.withHooks (lawHooks c H)).sortOf x = some k.sig.result
  | .ctor g [p, q], ha, x, hx => by
    unfold lawFlat at hx
    split at hx
    · rename_i hg
      have hg' : g = k.sig.name := by simpa using hg
      rw [hg'] at ha
      obtain ⟨hpq, -, -⟩ := (law_sortOf_iff hs).mp ha
      rw [hb] at hpq
      obtain ⟨sp, ss, hp, hss, he⟩ := sortsOf_cons.mp hpq
      obtain ⟨sq, ss', hq, -, he'⟩ := sortsOf_cons.mp hss
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [List.cons.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      rcases List.mem_append.mp hx with h1 | h1
      · exact law_leaves_sorted hs hb p hp x h1
      · exact law_leaves_sorted hs hb q hq x h1
    · rw [List.mem_singleton.mp hx]; exact ha
  | .ctor _ [], ha, x, hx | .ctor _ [_], ha, x, hx | .ctor _ (_ :: _ :: _ :: _), ha, x, hx
  | .inj _ _ _, ha, x, hx | .dv _ _, ha, x, hx | .map _ _, ha, x, hx | .set _ _, ha, x, hx
  | .list _ _, ha, x, hx => by
    simp only [lawFlat, List.mem_singleton] at hx; subst hx; exact ha

/-- **The right nesting of leaves of the result sort is a value of it**, for an associative open
generator without idempotence: `lawApp` gives each of its nodes back. -/
theorem law_nest_sorted (hs : LawShape c k) (hb : k.sig.args = [k.sig.result, k.sig.result])
    (ha : k.assoc = true) (hi : k.idem = false) :
    ∀ ts : List GroundTerm, ts ≠ [] →
      (∀ t ∈ ts, lawFlat k.sig.name t = [t] ∧ (c.withHooks (lawHooks c H)).sortOf t = some k.sig.result) →
      (c.withHooks (lawHooks c H)).sortOf (lawNest k.sig.name ts) = some k.sig.result
  | [], h, _ => absurd rfl h
  | [t], _, h => (h t (List.mem_singleton_self _)).2
  | t :: u :: ts, _, h => by
    have ih := law_nest_sorted hs hb ha hi (u :: ts) (List.cons_ne_nil _ _)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ht := h t (List.mem_cons_self ..)
    rw [show lawNest k.sig.name (t :: u :: ts) = .ctor k.sig.name [t, lawNest k.sig.name (u :: ts)] from rfl]
    refine (law_sortOf_iff hs).mpr ⟨?_, ?_, rfl⟩
    · rw [hb]
      exact sortsOf_cons.mpr ⟨_, _, ht.2, sortsOf_cons.mpr ⟨_, _, ih, sortsOf_nil, rfl⟩, rfl⟩
    · rw [lawApp_assoc ha hi, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, ht.1,
        lawFlat_lawNest _ _ (List.cons_ne_nil _ _),
        lawFlat_flatMap_leaves _ _ fun x hx => (h x (List.mem_cons_of_mem _ hx)).1]
      rfl

/-- **An associative open generator at two values of its sort, at `lawHooks`**: the right nesting
of their leaves. -/
theorem law_assoc_val (hs : LawShape c k) (hr : k.raw = true) (hb : k.sig.args = [k.sig.result, k.sig.result])
    (ha : k.assoc = true) (hi : k.idem = false) {x y : GroundTerm}
    (hx : (c.withHooks (lawHooks c H)).sortOf x = some k.sig.result)
    (hy : (c.withHooks (lawHooks c H)).sortOf y = some k.sig.result) :
    (c.withHooks (lawHooks c H)).paramVal k.sig.name [x, y] =
      some (lawNest k.sig.name (lawFlat k.sig.name x ++ lawFlat k.sig.name y)) := by
  refine (law_paramVal hs hr).mpr ⟨by rw [lawApp_assoc ha hi]; simp, ?_⟩
  refine law_nest_sorted hs hb ha hi _ (by simp [lawFlat_ne_nil]) fun t ht => ?_
  rcases List.mem_append.mp ht with h | h
  · exact ⟨lawFlat_leaf _ x t h, law_leaves_sorted hs hb x hx t h⟩
  · exact ⟨lawFlat_leaf _ y t h, law_leaves_sorted hs hb y hy t h⟩

/-- The flattening of the value `law_assoc_val` gives: the leaves of both arguments. -/
theorem law_flat_val (x y : GroundTerm) (f : Sym) :
    lawFlat f (lawNest f (lawFlat f x ++ lawFlat f y)) = lawFlat f x ++ lawFlat f y := by
  rw [lawFlat_lawNest _ _ (by simp [lawFlat_ne_nil])]
  exact lawFlat_flatMap_leaves _ _ fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact lawFlat_leaf _ x t h
    · exact lawFlat_leaf _ y t h

theorem sorts3 {c : Semantics} {a b d : GroundTerm} {s : Srt} (h : c.sortsOf [a, b, d] = some [s, s, s]) :
    c.sortOf a = some s ∧ c.sortOf b = some s ∧ c.sortOf d = some s := by
  obtain ⟨sa, ss, ha, hss, he⟩ := sortsOf_cons.mp h
  obtain ⟨sb, ss', hb, hss', he'⟩ := sortsOf_cons.mp hss
  obtain ⟨sd, ss'', hd, -, he''⟩ := sortsOf_cons.mp hss'
  simp only [List.cons.injEq] at he he' he''
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨rfl, rfl⟩ := he'
  obtain ⟨rfl, -⟩ := he''
  exact ⟨ha, hb, hd⟩

theorem sorts2 {c : Semantics} {vs : List GroundTerm} {s s' : Srt} (h : c.sortsOf vs = some [s, s']) :
    ∃ a b, vs = [a, b] ∧ c.sortOf a = some s ∧ c.sortOf b = some s' := by
  match vs, h with
  | [], h => simp [sortsOf_nil] at h
  | a :: rest, h =>
    obtain ⟨sa, ss, ha, hss, he⟩ := sortsOf_cons.mp h
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    match rest, hss with
    | [], h' => simp [sortsOf_nil] at h'
    | b :: rest', h' =>
      obtain ⟨sb, ss', hb, hr, he'⟩ := sortsOf_cons.mp h'
      simp only [List.cons.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      match rest', hr with
      | [], _ => exact ⟨a, b, rfl, ha, hb⟩
      | _ :: _, h'' =>
        obtain ⟨_, _, _, _, he''⟩ := sortsOf_cons.mp h''
        cases he''

end

/-- **`lawHooks` satisfies the laws**, for every H, where each raw parameter has `LawShape` and
none has both laws: associativity because both groupings of three values nest the same leaves,
idempotence because equal adjacent arguments merge. -/
theorem openLaws_of_lawShape {c : Semantics} (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false)
    (hs : ∀ k ∈ c.params, k.raw = true → LawShape c k) (H : HookParams) :
    OpenLaws (c.withHooks (lawHooks c H)) := by
  intro k hk hr
  have hsk := hs k hk hr
  have hboth : k.assoc = true → k.idem = true → False := fun ha hi => by
    have := hl k hk; simp [hr, ha, hi] at this
  refine ⟨fun ha => ?_, fun hi => ?_⟩
  · have hi : k.idem = false := by
      cases h : k.idem
      · rfl
      · exact (hboth ha h).elim
    have hb := hsk.2.2.2.2.2 (by simp [ha])
    intro a b d hsorts
    obtain ⟨hsa, hsb, hsd⟩ := sorts3 hsorts
    have hab := law_assoc_val hsk hr hb ha hi hsa hsb
    have hbd := law_assoc_val hsk hr hb ha hi hsb hsd
    rw [hab, hbd, Option.bind_some, Option.bind_some,
      law_assoc_val hsk hr hb ha hi ((law_paramVal hsk hr).mp hab).2 hsd,
      law_assoc_val hsk hr hb ha hi hsa ((law_paramVal hsk hr).mp hbd).2,
      law_flat_val, law_flat_val, List.append_assoc]
  · have ha : k.assoc = false := by
      cases h : k.assoc
      · rfl
      · exact (hboth h hi).elim
    intro a hsa
    refine (law_paramVal hsk hr).mpr ⟨?_, hsa⟩
    have hm : lawMerge [a, a] = [a] := by simp [lawMerge, (Exec.same_iff).mpr rfl]
    simp [lawApp, ha, hi, hm]


/-- What `coreOK` gives of each raw parameter for the theorems on `lawHooks`. Under `coreOK` no
parameter is raw (`paramsPlain`), so this is where `openLaws_lawHooks` and `openTotal_lawHooks`
take that fact; once `paramsPlain` is V8's body it is to be re-proved from its `raw` branch (no
registry hook; two arguments of the result sort where there is a law), `genWf`'s flat conjunct
(no constructor or overloading symbol of the name) and a fact that `lookupParam` and `lookupOpen`
find the raw parameter itself (`NamesApartK` gives equal signatures only), as for
`Semantics.raw_open_core`. -/
theorem Semantics.lawShape_core {c : Semantics} (h : c.coreOK = true) :
    ∀ k ∈ c.params, k.raw = true → LawShape c k :=
  fun k hk hr => absurd hr (by simp [Semantics.params_raw_of_core h k hk])

/-- **`lawHooks` satisfies the laws** (CN-4 §4.7 item 2): for every H, at a semantics `coreOK`
accepts with no raw parameter that has both laws. -/
theorem openLaws_lawHooks (c : Semantics) (h : c.coreOK = true)
    (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false) (H : HookParams) :
    OpenLaws (c.withHooks (lawHooks c H)) :=
  openLaws_of_lawShape hl (Semantics.lawShape_core h) H

/-- **`lawHooks` gives each open generator a value at every argument list of its sorts**, for every
H, where each raw parameter has `LawShape` and none has both laws: the application itself where it
has no law, the nesting of the leaves where it is associative, the merged arguments where it is
idempotent. -/
theorem openTotal_of_lawShape {c : Semantics} (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false)
    (hs : ∀ k ∈ c.params, k.raw = true → LawShape c k) (H : HookParams) :
    OpenTotal (c.withHooks (lawHooks c H)) := by
  intro k hk hr vs hvs
  have hsk := hs k hk hr
  have hboth : k.assoc = true → k.idem = true → False := fun ha hi => by
    have := hl k hk; simp [hr, ha, hi] at this
  cases ha : k.assoc <;> cases hi : k.idem
  · -- no law: the application itself
    have hv : (c.withHooks (lawHooks c H)).paramVal k.sig.name vs = some (.ctor k.sig.name vs) :=
      (law_paramVal hsk hr).mpr ⟨(lawApp_plain ha hi vs).symm,
        (law_sortOf_iff hsk).mpr ⟨hvs, lawApp_plain ha hi vs, rfl⟩⟩
    rw [hv]; rfl
  · -- idempotent alone: the merged arguments
    have hb := hsk.2.2.2.2.2 (by simp [hi])
    rw [hb] at hvs
    obtain ⟨a, b, rfl, hsa, hsb⟩ := sorts2 hvs
    by_cases hab : Exec.same a b = true
    · have hm : lawMerge [a, b] = [b] := by simp [lawMerge, hab]
      have hv : (c.withHooks (lawHooks c H)).paramVal k.sig.name [a, b] = some b :=
        (law_paramVal hsk hr).mpr ⟨by simp [lawApp, ha, hi, hm], hsb⟩
      rw [hv]; rfl
    · have hm : lawMerge [a, b] = [a, b] := by simp [lawMerge, hab]
      have happ : lawApp k [a, b] = .ctor k.sig.name [a, b] := by simp [lawApp, ha, hi, hm]
      have hv : (c.withHooks (lawHooks c H)).paramVal k.sig.name [a, b] = some (.ctor k.sig.name [a, b]) :=
        (law_paramVal hsk hr).mpr ⟨happ.symm, (law_sortOf_iff hsk).mpr ⟨by rw [hb]; exact hvs, happ, rfl⟩⟩
      rw [hv]; rfl
  · -- associative alone: the nesting of the leaves
    have hb := hsk.2.2.2.2.2 (by simp [ha])
    rw [hb] at hvs
    obtain ⟨a, b, rfl, hsa, hsb⟩ := sorts2 hvs
    rw [law_assoc_val hsk hr hb ha hi hsa hsb]; rfl
  · exact (hboth ha hi).elim

/-- **`lawHooks` gives each open generator a value at every argument list of its sorts** (CN-4
§3.4 V1): for every H, at a semantics `coreOK` accepts with no raw parameter that has both laws. -/
theorem openTotal_lawHooks (c : Semantics) (h : c.coreOK = true)
    (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false) (H : HookParams) :
    OpenTotal (c.withHooks (lawHooks c H)) :=
  openTotal_of_lawShape hl (Semantics.lawShape_core h) H

end KCore
