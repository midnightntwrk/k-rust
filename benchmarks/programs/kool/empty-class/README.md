# KOOL empty class

Origin: the `kool-load-and-typing` reproducer of the 2026-10 open-issues round's performance follow-ups, which ran this program to measure loading the KOOL definition (1.03e9 instructions at `934d29e7`).
`empty.kool` is the reproducer's program: a main class with an empty constructor, so the run is almost all definition loading.
