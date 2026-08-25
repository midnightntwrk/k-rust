# M1 external oracle

`tools/verify.py` is the single entry point for the M1 real-Rust authoring
gate. The positive workspace contains two semantic packages whose only KRS
implementation dependency is the renamed `language-host` facade. A separate
tooling binary exercises real Cargo metadata, collector planning, linked host
registration, protocol-v4 collection, and compiler-owned open-sort analysis.

The `blanket_coherence` negative case deliberately produces Rust E0119 at a
multi-parent diamond. Its failure proves why KRS computes sort closure in its
semantic model instead of synthesizing transitive Rust blanket impls.

Build output is confined to temporary target directories. The verifier never
deletes source files or treats a nonzero command alone as sufficient evidence
for an expected failure.

