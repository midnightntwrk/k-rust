# KRS language-tour plan

This directory is the planning source for a comprehensive KRS language tour.
The corresponding Vocs site lives in `docs-site/`.

The plan has four artifacts:

- [`tour.toml`](tour.toml) is the machine-readable curriculum and feature-status ledger.
- [`authoring-spec/`](authoring-spec/README.md) is the normative readable-authoring specification: the IMP specimen, the decision register, and the open questions.
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
2. `docs-plan/authoring-spec/imp.rs` decides idiomatic layer-1 spelling for the implemented IMP surface;
3. `tests/imp/rust-definition/` decides executable IMP, static-semantics, and proof behavior;
4. `docs-plan/authoring-spec/decisions.md` supplies design rationale only where it agrees with current public API and tests;
5. `semantics/coverage.toml` and the canonical KWasm, KMIR, and KEVM ports decide qualification status for language-scale examples.

Any conflict between these sources must be reported and resolved explicitly.
The tour must not interpret around it.

Earlier readability specimens are design history, do not compile, and are not part of this repository.
The tour must not source idiomatic syntax from them.

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
