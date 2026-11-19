/-
  A sort of the definition below a library sort whose values are constructor terms, read from
  kompile's own KORE (`f2-examples/libsub.k`, `libsub.kompile.kore`): `Acct < JSON`, as KEVM's
  `Account < JSON`, and `Int < JSONKey` between two library sorts, as KEVM's. Run from the package
  root: `lake env lean test/LibrarySubsort.lean`.
  - Both subsorts are the definition's declared pairs, their upper sorts are the library's (not the
    definition's) and are sorts of constructor terms (`libConsSorts`); `coreOK` holds.
  - An account injected into JSON is a value of JSON.
  - The rule `wrap(acct(N)) => done(N : acct(N))` steps from `wrap(inj{Acct,JSON}(acct(5)))` to
    `done(JSONEntry(inj{Int,JSONKey}(5), inj{Acct,JSON}(acct(5))))`: its left side matches through
    the injection into JSON, and its right side builds both injections.
  Every fact is a kernel decision; the step goes through `Exec.step_iff_of_ok`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace LibSub

definition_of defn from "f2-examples/libsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the facts name, by number: the definition's own (`symNames` from
`nRegSyms`, `sortNames` from `nRegSorts`) and the library's (`regSymNames`, `regSortNames`). -/
def kCell : Sym := 384
def acct : Sym := 386
def done : Sym := 387
def wrap : Sym := 388
def jsonEntry : Sym := 351
def cmdS : Srt := 32
def acctS : Srt := 33
def json : Srt := 24
def jsonKey : Srt := 25

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName acct = "Lblacct" ∧ c.symName done = "Lbldone" ∧
    c.symName wrap = "Lblwrap" ∧ c.symName jsonEntry = "LblJSONEntry" ∧ c.sortName cmdS = "Cmd" ∧
    c.sortName acctS = "Acct" ∧ c.sortName json = "JSON" ∧ c.sortName jsonKey = "JSONKey" := by
  decide +kernel

tables_of T from "f2-examples/libsub.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

theorem acct_json : c.userSubsorts.contains (acctS, json) = true := by decide +kernel
theorem int_jsonKey : c.userSubsorts.contains (Srt.int, jsonKey) = true := by decide +kernel
theorem json_library : (c.userSorts.contains json || c.userSorts.contains jsonKey) = false ∧
    c.libConsSorts.contains json = true ∧ c.libConsSorts.contains jsonKey = true := by
  decide +kernel

theorem subsortsOK : c.subsortsOK = true := subsortsOK_of_T (by rw [← T_eq]; decide +kernel)

-- `faithCoreOK` by `decide_cheap`: each conjunct apart, the names on their codes
set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `acct(5)`, and it injected into JSON. -/
def acct5 : GroundTerm := .ctor acct [.dv Srt.int (.int 5)]
def acct5J : GroundTerm := .inj acctS json acct5

theorem acct5J_sort : c.sortOf acct5J = some json := sortOf_of_T T_eq (by decide +kernel)

/-- The configuration with `st` of sort `Cmd` in the k cell and the counter at 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def x : GroundTerm := cfg (.ctor wrap [acct5J])
def y : GroundTerm :=
  cfg (.ctor done [.ctor jsonEntry [.inj Srt.int jsonKey (.dv Srt.int (.int 5)), acct5J]])

def X : Config c := ⟨x, sortOf_of_T T_eq (by decide +kernel)⟩
def Y : Config c := ⟨y, sortOf_of_T T_eq (by decide +kernel)⟩

theorem ok : c.ok = true := ok_of_T T_eq (by decide +kernel)
theorem srReady : c.srReady = true := srReady_of_T T_eq (by decide +kernel)
theorem matchReady : c.matchReady = true := matchReady_of_T T_eq (by decide +kernel)
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (agreeObligations_of_T T_eq (by decide +kernel))

/-- **The step**: the rule matches through `inj{Acct,JSON}` and builds `N : acct(N)`. -/
theorem step : Step c X Y :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent X Y).mpr ⟨100, by decide +kernel⟩

end LibSub

#print axioms LibSub.step
#print axioms LibSub.coreOK
