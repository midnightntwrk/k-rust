# k2lean's product: what it is for, and where work belongs

This note holds the product decisions that steer k2lean's work.
They are Sebastien's unless a line says otherwise, and they grow as the project learns: a decision is dated and changed in place, not appended to.
What a generated library promises, and what an optimization loop may change in it, is [`contract.md`](contract.md); what each generator states from K, and what a user writes, is `design.md` §3, "What a generator knows".

## Where work belongs (2026-10-28)

Heuristics, not rules: apply them with judgement, and say on the ticket when a case does not fit.
They decide what gets built where; correctness from first principles (the repository's agent notes) decides how it is justified.

**Which project.**
- k2lean (in k-rust) when K's meaning justifies the feature and a second definition tests it.
- Example material (a demo, a checker, a fixture, a sidecar, an invariant's statement, a divergence proof) when it is a fact of one semantics.
- A project of its own (for KEVM, the EVM work: conformance runs, equivalence with another EVM model) when its purpose is a claim about one semantics.
  A generator feature such a project needs that is general in form but has no consumer outside it is recorded there, and built when a second definition needs it (KEVM's `<wordStack>` statement).

**Inside k2lean: generators know K constructs, not language features.**
A language feature (variables, scopes, functions, exceptions, objects, threads) is a use of K constructs plus facts about how one language uses them.
- The generator handles each K construct from what it means in K: cells, nesting and cell collections, `<k>` with strictness and `KResult`, priorities and `owise`, side conditions, rules that read several cells or several collection elements, hooked sorts (`Map`, `List`, `Set`, `Int`), fresh values, `stream` cells, functions and their partiality.
- The language's facts are written by the user, in K, as functions of a definition: a kind 1 invariant, a type checker, a relation between the checker's typing and the runtime state. The generator proves things about them.
- Hand-written Lean is for proof cases the tactics do not close, not for stating a language's facts.
- To apply it: when a feature's description names a language concept (variable, store, location, frame, scope), find the K constructs under it. They are the generator's; what is left is the user's.
  Example: variables are a typing context the checker threads along `<k>`, `Map` cells, rules that read `<env>` then `<store>`, and fresh locations (K constructs), plus "the environment and the store realize the typing context" (the user's, a K function).
- Warning sign: an option or mechanism named after one definition's shape (`--store-cell`, `--env-item`) or after a language concept is a place where the boundary was crossed. Keep it as a stopgap only until a second definition shows the general form, then replace it.
- Not every K definition fits a generator's input. Say so in `design.md` and refuse with a message rather than stretch a generator. For example, `soundness` reads a checker written as functions, not one written as rewrite rules.
