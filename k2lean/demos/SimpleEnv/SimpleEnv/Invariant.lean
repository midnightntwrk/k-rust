import KSimple.Rules
import KPrelude.InvColl

/-!
# Every thread's environment maps into the store (kind 2 layout: `Invariant.lean`)

HAND-WRITTEN. A kind 2 invariant of SIMPLE, relating two parts of the
configuration: every value of every thread's `<env>`, and of `<genv>`, is a location of
`<store>` (a key of the store map).

**Why it is strengthened.** That statement alone is not inductive. Three rules set a thread's
`<env>` from elsewhere: `setEnv(Env)` from an item of the thread's `<k>` (pushed by the block rule
`{ S } => S ~> setEnv(Env)`), `return` and `throw` from a stack frame of `<fstack>` or
`<xstack>`, and a function call from `<genv>`. A configuration whose `<k>` holds `setEnv(E)` with
an `E` outside the store satisfies the plain statement and steps to one that does not. So the
invariant says the same of every environment the thread holds: the `setEnv(E)` items of its
computation, and the environment of every stack frame, together with the frame's saved
computation and control, recursively (`envsI`, `envsK`, `envsL`, `envsC`).

Only the items of a computation are read, not terms inside them: no rule of SIMPLE moves a
`setEnv` item from inside a term (a frozen expression, an `lvalue(K)`, a lambda body in the store)
to the top of a computation, and the proof below checks that for every rule.

**The store only grows.** No rule removes a location, so a location stays one; the cases of the
five rules that add or overwrite a store binding (`var X;`, `var X[N];`, `function F(Xs) S`,
`++ loc(L)`, `loc(L) = V`) are hand cases in `Cases.lean`, through `threadOk_mono`.
-/

namespace SimpleEnv

open KPrelude KSimple

/-- `v` is a location of the store `S`: a key of the store map. -/
def InStore (S : SortMap) (v : SortKItem) : Prop := ∃ w, (v, w) ∈ ListIso.toList S

/-- Every value of the environment `E` is a location of `S`. -/
def EnvIn (S : SortMap) (E : SortMap) : Prop := MapHook.EntriesOn (fun p => InStore S p.2) E

mutual
/-- The environments a computation item holds: the one of `setEnv(E)`, and a stack frame's own
and those of its saved computation and control. -/
def envsI : SortKItem → List SortMap
  | .inj_KItem (.«setEnv(_)» E) => [E]
  | .inj_KItem (.«(_,_,_)» E K C) => E :: (envsK K ++ envsC C)
  | .inj_KItem (.«(_,_,_,_,_)» _ _ K E C) => E :: (envsK K ++ envsC C)
  | _ => []
/-- The environments of the items of a computation. -/
def envsK : SortK → List SortMap
  | .dotk => []
  | .kseq x k => envsI x ++ envsK k
/-- The environments of the elements of a list (a stack). -/
def envsL : SortList → List SortMap
  | .nil => []
  | .cons x l => envsI x ++ envsL l
/-- The environments of the stacks of a control fragment (a frame's saved control). -/
def envsC : SortControlCellFragment → List SortMap
  | .«<control>-fragment» fs xs =>
    (match fs with
     | .inj_FstackCell (.«<fstack>» l) => envsL l
     | _ => []) ++
    (match xs with
     | .inj_XstackCell (.«<xstack>» l) => envsL l
     | _ => [])
end

/-- Every environment of a list of environments maps into `S`. -/
def AllIn (S : SortMap) (l : List SortMap) : Prop := ∀ E ∈ l, EnvIn S E

/-! ## Reading the configuration, one cell per level -/

def topT : SortGeneratedTopCell → SortTCell | .«<generatedTop>» t _ => t
def tThreads : SortTCell → SortThreadsCell | .«<T>» x _ _ _ _ _ _ _ => x
def tGenv : SortTCell → SortGenvCell | .«<T>» _ x _ _ _ _ _ _ => x
def tStore : SortTCell → SortStoreCell | .«<T>» _ _ x _ _ _ _ _ => x
def threadsOf : SortThreadsCell → SortThreadCellMap | .«<threads>» x => x
def genvOf : SortGenvCell → SortMap | .«<genv>» x => x
def storeOf : SortStoreCell → SortMap | .«<store>» x => x
def thK : SortThreadCell → SortKCell | .«<thread>» _ x _ _ _ => x
def thCtl : SortThreadCell → SortControlCell | .«<thread>» _ _ x _ _ => x
def thEnv : SortThreadCell → SortEnvCell | .«<thread>» _ _ _ x _ => x
def kOf : SortKCell → SortK | .«<k>» x => x
def envOf : SortEnvCell → SortMap | .«<env>» x => x
def ctlF : SortControlCell → SortFstackCell | .«<control>» x _ => x
def ctlX : SortControlCell → SortXstackCell | .«<control>» _ x => x
def fsOf : SortFstackCell → SortList | .«<fstack>» x => x
def xsOf : SortXstackCell → SortList | .«<xstack>» x => x

/-- The environments of the stacks of a control fragment, read by the projections. -/
def envsFO : SortFstackCellOpt → List SortMap
  | .inj_FstackCell c => envsL (fsOf c)
  | _ => []
def envsXO : SortXstackCellOpt → List SortMap
  | .inj_XstackCell c => envsL (xsOf c)
  | _ => []

/-- One thread keeps its environments in `S`: its `<env>`, and those of its computation and of its
two stacks. -/
def ThreadOk (S : SortMap) (p : SortIdCell × SortThreadCell) : Prop :=
  EnvIn S (envOf (thEnv p.2)) ∧ AllIn S (envsK (kOf (thK p.2))) ∧
    AllIn S (envsL (fsOf (ctlF (thCtl p.2)))) ∧ AllIn S (envsL (xsOf (ctlX (thCtl p.2))))

/-- The invariant: every thread and `<genv>` keep their environments in the store. -/
def Invariant (c : SortGeneratedTopCell) : Prop :=
  MapHook.EntriesOn (ThreadOk (storeOf (tStore (topT c)))) (threadsOf (tThreads (topT c))) ∧
    EnvIn (storeOf (tStore (topT c))) (genvOf (tGenv (topT c)))

/-! ## How it computes (the unfolding set of `k2l_preserve` in `Cases.lean`) -/

theorem allIn_nil (S : SortMap) : AllIn S [] = True := by simp [AllIn]
theorem allIn_cons (S E : SortMap) (l : List SortMap) : AllIn S (E :: l) = (EnvIn S E ∧ AllIn S l) := by
  simp [AllIn]
theorem allIn_append (S : SortMap) (a b : List SortMap) : AllIn S (a ++ b) = (AllIn S a ∧ AllIn S b) := by
  simp only [AllIn, List.mem_append, eq_iff_iff]
  exact ⟨fun h => ⟨fun E hE => h E (.inl hE), fun E hE => h E (.inr hE)⟩,
    fun ⟨ha, hb⟩ E hE => hE.elim (ha E) (hb E)⟩

/-- A frame's control, read by the projections. -/
theorem envsC_eq (fs : SortFstackCellOpt) (xs : SortXstackCellOpt) :
    envsC (.«<control>-fragment» fs xs) = envsFO fs ++ envsXO xs := by
  cases fs with
  | inj_FstackCell c => cases c; cases xs with
    | inj_XstackCell d => cases d; rfl
    | inj_XstackCellOpt _ => rfl
  | inj_FstackCellOpt _ => cases xs with
    | inj_XstackCell d => cases d; rfl
    | inj_XstackCellOpt _ => rfl

/-- The environments of a list are those of its elements, in order. -/
theorem envsL_eq : ∀ l : SortList, envsL l = (ListIso.toList l).flatMap envsI
  | .nil => rfl
  | .cons x l => by
    show envsI x ++ envsL l = (x :: SortList.toList l).flatMap envsI
    rw [List.flatMap_cons, envsL_eq l]
    rfl

theorem envsL_unit : envsL (ListHook.unit : SortList) = [] := by
  simp [envsL_eq, ListHook.unit, ListIso.toList_ofList]
theorem envsL_element (x : SortKItem) : envsL (ListHook.element x : SortList) = envsI x := by
  simp [envsL_eq, ListHook.element, ListIso.toList_ofList]
theorem envsL_concat (a b : SortList) :
    envsL (ListHook.concat a b : SortList) = envsL a ++ envsL b := by
  simp [envsL_eq, ListHook.concat, ListIso.toList_ofList]

/-! The injections into `KItem` hold no environment. -/
theorem envsI_inj_Exp (e : SortExp) : envsI (inj_Exp_KItem e) = [] := by cases e <;> rfl
theorem envsI_inj_Exps (e : SortExps) : envsI (inj_Exps_KItem e) = [] := by cases e <;> rfl
theorem envsI_inj_Ids (e : SortIds) : envsI (inj_Ids_KItem e) = [] := by cases e <;> rfl
theorem envsI_inj_Stmt (e : SortStmt) : envsI (inj_Stmt_KItem e) = [] := by cases e <;> rfl
theorem envsI_inj_Val (e : SortVal) : envsI (inj_Val_KItem e) = [] := by cases e <;> rfl
theorem envsI_inj_Vals (e : SortVals) : envsI (inj_Vals_KItem e) = [] := by cases e <;> rfl
theorem envsI_inj_IOInt (e : SortIOInt) : envsI (inj_IOInt_KItem e) = [] := by cases e <;> rfl

/-! ## The store only grows -/

theorem envIn_mono {S S' : SortMap} (h : ∀ v, InStore S v → InStore S' v) {E : SortMap}
    (hE : EnvIn S E) : EnvIn S' E := fun p hp => h _ (hE p hp)

theorem allIn_mono {S S' : SortMap} (h : ∀ v, InStore S v → InStore S' v) {l : List SortMap}
    (hl : AllIn S l) : AllIn S' l := fun E hE => envIn_mono h (hl E hE)

theorem threadOk_mono {S S' : SortMap} (h : ∀ v, InStore S v → InStore S' v)
    {p : SortIdCell × SortThreadCell} (hp : ThreadOk S p) : ThreadOk S' p :=
  ⟨envIn_mono h hp.1, allIn_mono h hp.2.1, allIn_mono h hp.2.2.1, allIn_mono h hp.2.2.2⟩

theorem threadsOk_mono {S S' : SortMap} (h : ∀ v, InStore S v → InStore S' v)
    {m : SortThreadCellMap} (hm : MapHook.EntriesOn (ThreadOk S) m) :
    MapHook.EntriesOn (ThreadOk S') m := fun p hp => threadOk_mono h (hm p hp)

/-- A location of an operand of a defined `M₁ M₂` is a location of the result, and conversely. -/
theorem inStore_concat {a b m : SortMap} (hc : MapHook.concat a b = some m) (v : SortKItem) :
    InStore m v ↔ InStore a v ∨ InStore b v := by
  simp only [InStore, MapHook.mem_toList_of_concat hc]
  exact ⟨fun ⟨w, hw⟩ => hw.elim (fun h => .inl ⟨w, h⟩) (fun h => .inr ⟨w, h⟩),
    fun h => h.elim (fun ⟨w, hw⟩ => ⟨w, .inl hw⟩) (fun ⟨w, hw⟩ => ⟨w, .inr hw⟩)⟩

theorem inStore_element (k w v : SortKItem) : InStore (MapHook.element k w) v ↔ v = k := by
  simp [InStore, MapHook.element, ListIso.toList_ofList]

/-- A store extended by `M₁ M₂` keeps the locations of `M₂`. -/
theorem grow_right {a b m : SortMap} (hc : MapHook.concat a b = some m) :
    ∀ v, InStore b v → InStore m v := fun v hv => (inStore_concat hc v).2 (.inr hv)

/-- The bound key of `K |-> V REST` is a location. -/
theorem inStore_left_element {k w : SortKItem} {b m : SortMap}
    (hc : MapHook.concat (MapHook.element k w) b = some m) : InStore m k :=
  (inStore_concat hc k).2 (.inl ((inStore_element k w k).2 rfl))

/-- Overwriting the value at a location keeps the locations. -/
theorem grow_overwrite {k w w' : SortKItem} {b m m' : SortMap}
    (h : MapHook.concat (MapHook.element k w) b = some m)
    (h' : MapHook.concat (MapHook.element k w') b = some m') : ∀ v, InStore m v → InStore m' v := by
  intro v hv
  rcases (inStore_concat h v).1 hv with hv | hv
  · exact (inStore_concat h' v).2 (.inl ((inStore_element k w' v).2 ((inStore_element k w v).1 hv)))
  · exact (inStore_concat h' v).2 (.inr hv)

end SimpleEnv
