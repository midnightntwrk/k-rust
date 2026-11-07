# Import diamonds

Origin: the `import-diamonds` reproducer of the 2026-10 open-issues round's performance follow-ups ("Modules are visited once per import path"); at `934d29e7` load instructions grew about 4 times per two diamonds.
`gen.py D` prints D import diamonds above module `MAIN` and a module `TOP`, which a prepare step appends to the compiled `main.k` definition; the axioms are the same for every D, only the number of import paths (2^D) grows.
`pattern.kore` is `f(1)`, which simplifies to `2` through `TOP`.
The workload stresses loading a KORE definition whose import graph has exponentially many paths.
