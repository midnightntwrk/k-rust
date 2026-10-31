// The K tutorial's IMP++ proof tests/proofs/sum-spec.k (pl-tutorial 1_k/4_imp++/lesson_7), its two
// claims read from that file as it is: the loop `while (!(n <= 0)) { sum = sum + n; n = n + -1; }`
// over framed <env> and <store> (by its own circularity), and the program that declares `n` and
// `sum` and runs it (by the loop's claim). The file itself names no definition (the tutorial's
// harness supplies it), so this one requires IMP++'s before it.
requires "imp.k"
requires "tests/proofs/sum-spec.k"
