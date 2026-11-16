# CC-0: cell collections, clause-less functions, macro symbols

State: design decisions, written 2026-11-12 by Fable from the KEVM measurement (`findings/RD-2-kompile-kore.md` §10) and a read of `f2-examples/colls.kore` and KEVM's KORE.
They concern the reader only. No kernel definition (`Core`, `Value`, `Evaluation`, `Step`, `Faithful`) changes.

## 1. What the texts say about a cell collection

For `<acct multiplicity="*" type="Map">` inside `<accts>` the KORE declares:

- a hooked sort `AcctCellMap` (`MAP.Map`) with unit `.AcctCellMap`, element `AcctCellMapItem(IdCell, AcctCell)`, concat `_AcctCellMap_`;
- the cell constructor `<acct>(IdCell, BalCell) : AcctCell`;
- a subsort `AcctCell < AcctCellMap`, with a no-junk axiom saying every `AcctCellMap` is `inj(cell)`;
- `AcctCellMapKey(AcctCell) : IdCell`, a function with one equation; initializers `initAcctCell`, `initIdCell`, `initBalCell`;
- fragment and optional constructors: `<acct>-fragment(IdCellOpt, BalCellOpt)`, `<accts>-fragment(AcctCellMap)`, `noIdCell`, `noBalCell`, with their injectivity and no-junk axioms.

In rules (colls: 1; KEVM: 83 element occurrences) a collection is always `_XCellMap_(XCellMapItem(key, <x>(key, …)), Rest)`, a map variable, or the unit.
The injection `inj{XCell, XCellMap}`, fragments, `noXCell` and `…CellOpt` occur in no rule and no user equation of either text.

## 2. Decisions

**D1. The subsort of a cell into its collection sort is not read.**
Read as a subsort it gives a second value, `inj(cell)`, for what the collection already denotes as a one-entry map, and the text's no-junk axiom for it ("every `XCellMap` is an injected cell") is false of the empty map and of two-entry maps. The kernel's collection sort holds maps and nothing else.
The subsort declaration, its subsort axiom and that no-junk axiom are classified in the account under a class of their own (`cellCollectionInjection`): stated by the text, deliberately not part of the reading. They are not called inert, because they state something.
Any read sentence that applies `inj{XCell, XCellMap}` is refused with that reason. None exists in colls or KEVM.
If a definition ever needs it, its meaning is the one-entry map keyed by `XCellMapKey(cell)`; that is a later reading, not this one.

**D2. A declared constructor is read as a constructor, whatever its origin.**
`<x>-fragment`, `noXCell` of a collection cell's children, and their sorts are constructors with `constructor`, `functional`, `injective` like any other. The reader drops them today because they have no source location and no `cell` attribute, which is not a reason. Reading them gives the fragment sorts their values, makes their injectivity and no-junk axioms the induced ones, and accounts for their declarations.

**D3. A declared function with equations is read as a function, whatever its origin.**
`XCellMapKey` and the initializers of cells outside the cell tree (`initAcctCell`, `initIdCell`, `initBalCell`) are functions with equations. They are read as functions; the account accepts them.

**D4. Nothing ties an entry's key to the cell's key child, and the reading does not add it.**
`XCellMapItem(k, c)` with `k` different from `c`'s key child is a value. The text states no axiom against it. That every reachable configuration has consistent keys is an invariant of a definition's rules (they always write the same key twice), to be proved by whoever needs it, not a condition of well-formedness.

**D5. A function symbol with no equation that some read sentence applies is a parameter.**
The text gives it no meaning. Reading it as a function that is undefined everywhere (which is what the closure axiom says of a function without clauses) adds a statement the text does not make. As a parameter, every theorem about the definition holds for every interpretation of it, which is what "the text says nothing" means.
(KEVM, kompile's text: 14 `KRYPTO` functions declared without a hook.)
If the parameter mechanism cannot express a declared `total`/`functional` on such a symbol, stop and report.

**D6. A macro symbol that no read sentence applies is not part of the reading; one that is applied stays refused.**
Classified in the account as `macroUnused`. (KEVM: 237 / 241 declarations.)

## 3. What should follow

- `f2-examples/colls.kore` reads with nothing unaccounted, `wf` true, and becomes a package: the first with a cell map.
- On KEVM: `inhabited` loses the fragment sorts, `genWf` holds, the inert mismatches of fragment and optional constructors disappear, the macro refusals become `macroUnused` or stay refused with the applying sentence named.
- What then remains failing on KEVM is listed one by one: the rules and clauses that fail `ruleOKAll` / `fnsOKAll`, the sorts still without a value in kompile's text (`Contract`, `ContractAccess`), the two overload axioms, the equation with a condition on its right side.
