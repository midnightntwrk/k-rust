# kink's IMP corpus (K tutorial `lesson_4/imp.k`)

Origin: the KINK-16/2 measurement of how kink's searches grow, run on kink's `examples/imp/` at k-in-k2 `905bddc`.
kink's `imp.k` is K's `pl-tutorial/1_k/2_imp/lesson_4/imp.k` unchanged, and its `sum`, `primes` and `collatz` programs are the lesson's programs with smaller bounds; the workloads read the definition from the K checkout and carry the programs as ladder templates in `registry/imp-scaling.toml`, with the bound as the ladder parameter.
`gen-wide.py W R` reproduces the synthetic `wide<W>r<R>.imp` programs of that measurement byte for byte (checked against that measurement's copies for W = 2, 4, 8 and R = 1, 16, 128).

kink compares the set of final configurations, so these programs run under `krun --search-final`, which explores every evaluation order of the strict `+`, `/` and `<=`.
They stress how the explored states grow with a loop bound or with the number of strict expressions, and whether equal states rejoin.
