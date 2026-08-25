# BAG-07: mutation edit-origin provenance

Status: integrated backend-agnostic closure packet.

## Objective

Make every generated patch edit traceable to the selected structural site(s)
and the operator's pinned patch template. Campaign origins and patch edits are
currently validated independently; lineage coincidence alone does not prove
which selected site authorized an edit.

This packet closes report provenance. It does not reimplement or validate the
semantics of a K-authored patch template in the host.

## Normative model

For each retained origin instance, record a canonical template-application
receipt for every produced edit. Each receipt binds:

- the produced `editId`;
- the operator and `patchTemplateDigest`;
- one or more source `siteId` values from that origin's discovery tuples;
- the source selector role(s);
- the source per-tuple bindings; and
- a stable template role/anchor name.

Receipts cover the candidate patch edits exactly: no missing, extra, duplicate,
or dangling edit ID. Source sites must belong to the origin, roles and bindings
must equal the resolved site registry, and affected/anchor lineage must be
authorized by the declared sources. Receipt order follows patch edit order.
The receipt and instance identities cover this evidence.

The portable verifier checks this graph and its canonical identity, but does
not claim that the K template computed the right replacement term. Native
template evaluation and differential evidence remain future Rust-stack work.

### Resolved v1 receipt surface

Do not leave the template role as an unchecked string. The operator declaration
must expose a closed, canonically ordered `patchTemplateRoles` interface. Each
role declaration has a unique nonempty `name`, one patch `operation`, and a
nonempty ordered `sourceSelectorRoles` list whose values resolve exactly to the
operator selector clauses. This is metadata for the digest-pinned template,
not a host implementation of it.

Replace each origin's bare `producedEditIds` with one ordered `editReceipts`
entry per candidate patch edit. Receipt order is exactly patch edit order. A
receipt contains:

- `editId`;
- the exact campaign operator ID, version, and digest;
- the operator's exact `patchTemplateDigest`;
- one declared `templateRole`; and
- a nonempty canonical `sources` array.

Each source contains a zero-based `discoveryTupleIndex`, a `siteId`, its exact
registry `selectorRole`, and the complete `tupleBindings` copied from that
origin's indexed discovery tuple. The site must occur in that indexed tuple.
Source order is `(discoveryTupleIndex, position of siteId in that discovery
tuple)`, with no duplicates. The source roles must equal the chosen template
role's declared `sourceSelectorRoles` in that declaration order; a declaration
may therefore express a one-source or multi-source edit. One source may appear
in receipts for multiple distinct edits.

The receipt's declared operation must equal its referenced edit's operation.
For replacement/removal/attribute/condition edits, at least one cited source
site's sentence lineage must equal `targetLineage`. For `insert-sentence`, the
position must be `before-lineage` or `after-lineage` and at least one cited
source lineage must equal `position.anchorLineage`. Module-boundary insertions
have no selected-site anchor and are not provenance-complete campaign edits in
v1; the general patch schema may still represent them outside this campaign
surface.

`instanceId` keeps its existing payload and additionally covers the complete
ordered `editReceipts`. There is no receipt ID separate from the instance: the
instance digest is the receipt-set identity. `candidateId`, `patchId`, and
`editId` remain unchanged, so identical-patch deduplication can retain multiple
distinct origin/receipt instances without changing the patch artifact.

Also reconcile the portable mutation-selector surface while touching this
boundary:

- selector `label` is nullable, with null meaning no label restriction;
- `siteId` identity includes `termPath` everywhere, including prose and ID
  vectors; and
- a permanent same-lineage/different-path case proves non-collision.

## Required evidence

- the coupled two-role fixture maps each edit to its correct source role/site;
- a single source may authorize multiple edits without duplicate receipts;
- a multi-source edit is representable and has canonical source order;
- identical-patch dedup retains distinct, complete receipts for every origin;
- insertions use their anchor lineage and replacements/removals use their
  target lineage for authorization; and
- label-free discovery and same-lineage/different-path site identities pass
  the real registry schema/validator.

Mandatory adversaries must reject missing/extra/reordered receipts, a receipt
for another origin's site, tuple-index/site mismatch, noncanonical or duplicate
sources, undeclared/duplicate/noncanonical template roles, operation drift,
source-role drift, role/binding/template/operator drift, dangling edit IDs,
unauthorized target or anchor lineage, a module-boundary insertion receipt,
same-path collision, and an old site-ID payload that omits `termPath`.

## Ownership

The worker may modify mutation selector/site-registry/campaign schemas,
operator/site/campaign fixtures, mutation vectors, contracts, artifact catalog
roles if a typed receipt artifact is chosen, refresh helper, verifier, and Rust
handoff provenance notes. Integrate after BAG-02 and BAG-06 because those share
campaign artifacts. Do not interpret the K patch template, alter selection
policy, observation/canonicalization/profile semantics, edit goals/D1/roadmap,
or run backend code.

## Acceptance

- every patch edit has exact, canonical, resolvable origin/template evidence;
- edit authorization derives from selected sites rather than sentence-text or
  self-asserted lineage;
- nullable-label and `termPath` site identity are consistent across schema,
  contract, vectors, and verifier;
- all adversaries reject through schema or the campaign semantic validator;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

## Stop rule

Stop rather than interpreting template semantics, accepting an opaque receipt,
authorizing edits from unselected sites, or claiming Rust patch correctness.
