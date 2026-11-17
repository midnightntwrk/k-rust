/-
  `wf defn = true` (C14, layer 1) on kimp's text as kompile wrote it
  (`examples/ref-kimp/RefKimp/definition.kore`), on the literal `defn`. Nothing here reads
  `Parse.parse`. Run from the package root:
  `lake env lean test/TieKimpWf.lean`.

  One kernel decision of `wf defn` exceeds 12 GiB. It is decided conjunct by conjunct
  (`wf_of_parts`), as the generated package does (`RefKimp.Wf`), here on this file's literal:
  - the names declared once, by their codes (`sorts_distinct`, `syms_distinct`), and the rest of
    `namesOK` (`names_rest`);
  - `ok`, on the definition's tables (`T`, checked equal to `tables c`): declarations, subsorts
    and functions (`okHead`), the 79 rules (`okRules0`);
  - the certificate, the presentation, the parameters, the overloading symbols, one decision each;
  - `faithOK`, one decision a conjunct; `itesApart` on the names' codes (`itesApart_of_codes`:
    decided directly it takes 9.4 GiB, on codes 2.6 GiB).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimp

open KCore KCore.Faithful KCore.Faithful.Model

definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"
tables_of T from "examples/ref-kimp/RefKimp/definition.kore"

noncomputable abbrev c : Semantics := defn.sem

/-! ## The names -/

theorem sorts_distinct : KoreAML.Distinct.codesDistinct 5 (defn.emit.sortDecls.map (·.name)) = true := by
  decide +kernel
theorem syms_distinct :
    KoreAML.Distinct.codesDistinct 8 (defn.emit.symbolDecls.map (·.name) ++ defn.emit.aliasNames) = true := by
  decide +kernel
theorem names_rest : (c.hooksApart && c.predsApart && c.idsOK) = true := by decide +kernel

/-! ## The core -/

theorem T_eq : T = tables c := by decide +kernel
theorem okHead : c.okHeadT T = true := by decide +kernel
theorem okRules0 : c.ruleRowsT T 0 79 = true := by decide +kernel
theorem rules_length : c.rules.length = 79 := by decide +kernel
theorem ok : c.ok = true := ok_of_T T_eq (okT_of_rows okHead (ruleRowsT_all rules_length okRules0))

/-! ## The certificate, the presentation, the parameters, the overloading symbols -/

theorem cert_ok : defn.cert.ok c = true := by decide +kernel
theorem pres_ok : defn.pres.ok c = true := by decide +kernel
theorem params_ok : defn.paramsOK = true := by decide +kernel
theorem overloads_ok : c.overloadsOK = true := by decide +kernel

/-! ## The theory's conditions -/

theorem faith_namesNumbered : namesNumbered c = true := by decide +kernel
theorem faith_genWf : genWf c = true := by decide +kernel
theorem faith_collSortsOK : collSortsOK c = true := by decide +kernel
theorem faith_collsOK : collsOK c = true := by decide +kernel
theorem faith_patHeadsOK : patHeadsOK c = true := by decide +kernel
theorem faith_namesApartFast : namesApartFast c = true := by decide +kernel
theorem faith_LitsApart : LitsApart c = true := by decide +kernel
theorem faith_sortsNumbered : sortsNumbered c = true := by decide +kernel
theorem faith_collsNotCtors : collsNotCtors c = true := by decide +kernel
theorem faith_itesApart : itesApart c = true := itesApart_of_codes rfl rfl rfl (by decide +kernel)
theorem faith_kindsApart : kindsApart c = true := by decide +kernel
theorem faith_ctorsOnce : ctorsOnce c = true := by decide +kernel
theorem faith_fnsApart : fnsApart c = true := by decide +kernel

theorem faith_ok : c.faithOK = true :=
  Semantics.faithOK_of_parts faith_namesNumbered faith_genWf faith_collSortsOK faith_collsOK faith_patHeadsOK
    faith_namesApartFast faith_LitsApart faith_sortsNumbered faith_collsNotCtors faith_itesApart faith_kindsApart
    faith_ctorsOnce faith_fnsApart

/-- **The definition is well formed.** -/
theorem wf_defn : wf defn = true :=
  wf_of_parts sorts_distinct syms_distinct names_rest ok cert_ok pres_ok params_ok faith_ok overloads_ok

end KCore.TieKimp

#check (KCore.TieKimp.wf_defn : KCore.wf KCore.TieKimp.defn = true)
#print axioms KCore.TieKimp.wf_defn
