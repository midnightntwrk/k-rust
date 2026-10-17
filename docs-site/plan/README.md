# Tour curriculum ledger

This directory is the planning source for the site's language tour.

- [`tour.toml`](tour.toml) is the machine-readable curriculum and feature-status ledger.
  Its evidence, fixture, and seed paths are relative to `../../krs/`.
- [`check.py`](check.py) enforces the ledger's identities, dependencies, classifications, evidence paths, and synthesis gloss requirements.
- [`check-pages.py`](check-pages.py) enforces canonical pages, concept declarations, navigation order, complete routes and anchors, synthesis publication state, and reviewed public-surface reference coverage.

`bun run check` runs both checks. To run them alone, from `docs-site/`:

```sh
python3 plan/check.py
python3 plan/check-pages.py
```

The rules for what the tour may claim and which sources decide it are in [`../../krs/docs-plan/README.md`](../../krs/docs-plan/README.md) ("Authority" and "Scope rule").
