# FUN scaling programs

Origin: the measurement of FUN's tail-recursion slowdown at `bac3841`, which ran the two program families below at growing N; the fix is `af43672`, which keeps terms across path replacement.
`e-tr-nN` is K's `tail-recursion.fun` on one line with `ref N`: FUN's tail-recursion rule is commented out, so each iteration leaves a `setEnv` item behind the head of `<k>`.
Before `af43672` its wall time and constructed terms grew quadratically with N (`tail-recursion.fun`, N = 1000, took 123.7 s).
`e-loop-nN` is a `callcc` loop with `@n < N`, whose continuation restores `<k>` on every jump: the constant-state control.
Both are ladder templates in `registry/fun-scaling.toml`; the result is 0 for the first and N for the second.
`constructor-bst-sorting.fun` and `tail-recursion.fun` are read from the K checkout (`pl-tutorial/2_languages/3_fun/programs/`).
