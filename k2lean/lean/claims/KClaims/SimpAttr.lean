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
