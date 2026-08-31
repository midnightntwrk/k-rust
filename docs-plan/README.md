# KRS language-tour plan

This directory is the planning source for a comprehensive KRS language tour.
The corresponding Vocs site lives in `docs-site/`.

The plan has five artifacts:

- [`tour.toml`](tour.toml) is the machine-readable curriculum and feature-status ledger.
- [`roadmap.md`](roadmap.md) defines the teaching order, content contract, build phases, and Vocs integration.
- [`review.md`](review.md) records the adversarial coverage review and the changes made in response.
- [`check.py`](check.py) enforces the ledger's identities, dependencies, classifications, evidence paths, and synthesis gloss requirements.
- [`check-pages.py`](check-pages.py) enforces canonical pages, concept declarations, navigation order, complete routes and anchors, synthesis publication state, and reviewed public-surface reference coverage.

Validate the coverage contract after changing it:

```sh
python3 docs-plan/check.py
python3 docs-plan/check-pages.py
taplo check docs-plan/tour.toml
```

## Authority

The tour must select authority by claim rather than applying one document globally:

1. `crates/krs-macros`, `crates/krs-syntax`, `crates/krs-cli`, and their current tests decide what is accepted and supported;
2. `draft/readability/spec/imp.rs` decides idiomatic layer-1 spelling for the implemented IMP surface;
3. `tests/m4/rust-definition/` decides executable IMP, static-semantics, and proof behavior;
4. `draft/readability/spec/decisions.md` supplies design rationale only where it agrees with current public API and tests;
5. `semantics/coverage.toml` and the canonical KWasm, KMIR, and KEVM ports decide qualification status for language-scale examples.

Any conflict between these sources must be reported and resolved explicitly.
The tour must not interpret around it.

`draft/readability/result/` is design history.
Its own README says its specimens do not compile and were superseded by `draft/readability/spec/`.
The tour may cite it only when explaining design rationale.

## Scope rule

“Comprehensive” means every current author-facing construct and every important observable semantic distinction appears either in the narrative tour, the reference appendix, or the limitations page.
It does not mean documenting planned syntax as though it exists.

Every published example must be labeled as one of:

- idiomatic layer 1;
- explicit/reference layer 2;
- future or unsupported.

The status ledger in `tour.toml` is the review checklist for that promise.

Chapter routes in the ledger are the canonical destinations for concept links.
Synthesis pages such as the five-minute theory declare their previewed concepts separately and may be published only after their generated glosses, destinations, page annotations, and navigation state pass the same gate.
