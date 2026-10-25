import Lean

/-- Definitions that the claim tactics unfold to reach arithmetic: hooks, injections,
projections, generated predicates. -/
register_simp_attr kc_simp

/-- Report the number of configurations, rule steps, splits and claim applications of each
`kc_auto` run. -/
register_option kc.stats : Bool := {
  defValue := false
  descr := "kc_auto: log exploration statistics"
}

/-- The unfolding set of a claim package's assumed invariant (`k2lean claims --assume-invariant`):
the definitions and equations that turn the invariant at a configuration into facts about its
parts, which `kc_auto … inv […]` uses when no rule applies. -/
register_simp_attr kc_inv

/-- The definitions of the functions an assumed invariant calls (non-recursive ones), unfolded
after `kc_inv` to expose what the invariant says about each part (`proj_A_B x = some _`). -/
register_simp_attr kc_inv_fns
