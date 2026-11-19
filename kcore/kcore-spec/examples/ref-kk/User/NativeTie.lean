/-
  The embeddings `kcore kk-native` runs (`KCore.KK.Native`, KcoreSpec/KKNative.lean) are this
  package's (User.Emb): each is equal to the one of the same name here, so the native check
  evaluates `succs` at `[embD E, emb (enc x)]` with the `embD`, `emb` and `embSt` of `KCore.KK.sig`.
  The table of KORE names it checks against the text it reads is the one `emb_names` states.
-/
import User.Sig
import KcoreSpec.KKNative

set_option autoImplicit false

namespace KCore.KK

theorem native_embK_eq : Native.embK = embK := by
  funext k; cases k <;> rfl

/-- The list step of `native_emb_eq`. -/
theorem native_embTs_of_knt {ts : List T} (h : ∀ t ∈ ts, Native.emb t = emb t) :
    Native.embTs ts = embTs ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [Native.embTs, embTs, h t (List.mem_cons_self ..),
      ih fun u hu => h u (List.mem_cons_of_mem _ hu)]

theorem native_emb_eq : Native.emb = emb := by
  funext t
  induction t using tInd_kkc with
  | hap f as ih => rw [Native.emb, emb, native_embTs_of_knt ih]
  | hiv i => rfl
  | hbv b => rfl
  | htk s x => rfl
  | hij a b t ih => rw [Native.emb, emb, ih]
  | hvr i => rfl
  | has p i ih => rw [Native.emb, emb, ih]
  | hhk o as ih => rw [Native.emb, emb, native_embTs_of_knt ih]
  | hbot => rfl
  | hcb k c ps ih => rw [Native.emb, emb, native_embTs_of_knt ih, native_embK_eq]
  | hco k c es ih => rw [Native.emb, emb, native_embTs_of_knt ih, native_embK_eq]
  | hen t e iht ihe => rw [Native.emb, emb, iht, ihe]
  | hkv a v iha ihv => rw [Native.emb, emb, iha, ihv]
  | hel x ih => rw [Native.emb, emb, ih]

theorem native_embTs_eq : Native.embTs = embTs := by
  funext ts; exact native_embTs_of_knt fun t _ => congrFun native_emb_eq t

theorem native_embS_eq : Native.embS = embS := by
  funext ss
  induction ss with
  | nil => rfl
  | cons p r ih => obtain ⟨a, b⟩ := p; rw [Native.embS, embS, ih]

theorem native_embCls_eq : Native.embCls = embCls := by
  funext cs
  induction cs with
  | nil => rfl
  | cons cl r ih =>
    rw [Native.embCls, embCls, ih, Native.embCl, embCl, native_embTs_eq, native_emb_eq]

theorem native_embFns_eq : Native.embFns = embFns := by
  funext fs
  induction fs with
  | nil => rfl
  | cons p r ih => obtain ⟨g, cs⟩ := p; rw [Native.embFns, embFns, ih, native_embCls_eq]

theorem native_embRls_eq : Native.embRls = embRls := by
  funext rs
  induction rs with
  | nil => rfl
  | cons rl r ih => rw [Native.embRls, embRls, ih, Native.embRl, embRl, native_emb_eq]

theorem native_embD_eq : Native.embD = embD := by
  funext E
  rw [Native.embD, embD, native_embS_eq, native_embFns_eq, native_embRls_eq]

theorem native_embSt_eq : Native.embSt = embSt := by
  funext s; cases s with
  | stuck => rfl
  | next ss => rw [Native.embSt, embSt, native_embTs_eq]

/-- The native check's embeddings are `sig`'s. -/
theorem native_sig_knt : sig.emb = Native.emb ∧ sig.embD = Native.embD ∧ sig.embSt = Native.embSt ∧
    sig.succs = 510 :=
  ⟨native_emb_eq.symm, native_embD_eq.symm, native_embSt_eq.symm, rfl⟩

/-- The table of names the native check reads is the one of `emb_names`, at `RefKk.defn`. -/
theorem native_embNames_knt : Native.embNamesWrong RefKk.defn.sem = [] := by
  decide +kernel

/-- The symbol the native check evaluates, found by its KORE name, is `sig.succs`. -/
theorem native_succs_knt : Native.symOf RefKk.defn.sem Native.succsName = some sig.succs := by
  decide +kernel

end KCore.KK
