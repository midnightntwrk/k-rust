# Tour curriculum ledger

This directory is the planning source for the site's language tour.

- [`tour.toml`](tour.toml) is the machine-readable curriculum and feature-status ledger.
  Its evidence, fixture, and seed paths are relative to `../../krs/`.
- [`ledger.py`](ledger.py) loads it for the checks and decides each topic's destination.

The ledger has five kinds of rows:

- a part groups lessons in the sidebar, in reading order;
- a lesson has a route under `/tour/` (or `/krs/` for the KRS side track), a status from `planned` to `accepted`, and the K concepts it teaches;
- a concept is one of the 44 K concepts of the tour's order, taught by exactly one lesson;
- a page predates that order; it names the lessons that replace it and is retired only after all of them are accepted;
- a topic is one implemented construct or semantic distinction: the checklist that makes the tour comprehensive.
  It belongs to a concept, a side-track lesson, or (for reference and limitation topics) a kept page.

A topic's destination, where pages link for it, is its lesson's route once the lesson is accepted, and its `page` until then.
Every published page and written lesson declares exactly the topics whose destination it is in a `tour-concepts` marker.
- [`check.py`](check.py) enforces the ledger's identities, dependencies, classifications, and evidence paths.
- [`check-pages.py`](check-pages.py) enforces canonical pages, concept declarations, navigation order, complete routes and anchors, and reviewed public-surface reference coverage.

`bun run check` runs both checks. To run them alone, from `docs-site/`:

```sh
python3 plan/check.py
python3 plan/check-pages.py
```

The rules for what the tour may claim and which sources decide it are in [`../../krs/docs-plan/README.md`](../../krs/docs-plan/README.md) ("Authority" and "Scope rule").
