#!/usr/bin/env python3
"""tiegen.py: the tie (C14) of a construct fixture's kompiled text, written as a Lean test.

Usage (from anywhere; the library and `kcore` built first):
  python3 -I test/constructs/tiegen.py FIXTURE [--sig-chunk N] [--decl-chunk N] [--chunk N]
                                               [--hand consistency=FILE] [--hand ovlfn=FILE]
                                               [--at-values N,...] [--reads-h N,...]
                                               [--cons-head] [--wf-parts]
                                               [--split] [--account-sorted] [--heads-literal] [--heads-codes]
                                               [--attrs-parts] [--attrs-blocks N] [--decl-parts] [--fn-blocks N]
                                               [--absent-file] [--builtin-decls] [--decl-syms-literal] [--nojunk-eq]
                                               [--nojunk-blocks N] [--lists-by-class] [--heads-plain] [--sig-positions]
                                               [--fnfun-chunk N] [--decl-positions] [--fn-readings] [--out DIR] [--print]
  (the probe, a run of the Lean definitions on the text, is stopped after $TIEGEN_PROBE_TIMEOUT seconds, 900 by default)
  python3 -I test/constructs/tiegen.py --self-test   (the law search below, on three fixtures)

For FIXTURE (a directory of test/constructs/fixtures with a kompiled text), it writes
  f2-examples/FIXTURE.kompile.kore   the kompiled text kompile.txt records (from the cache kfix.py
                                     keeps), K's builtin directory restored for BUILTIN/ and the
                                     fixture's directory, relative to kcore-spec's parent, for FIXTURE/;
  test/Tie<Fixture>.lean             the tie on that text, on the literals `kore` and `defn`, for
                                     every interpretation H.
With --out DIR it writes the test into DIR and leaves f2-examples alone. --chunk N cuts the
decisions over the whole user module (`account_absent`) and over the constructor sentences
(`cons_checked`, `cons_trS`) into ranges of N, each its own kernel decision (default: one each).
--cons-head decides the constructor sentences with `tchConsB` (KcoreSpec/TieConsHd.lean), in the
probe and in the test (`cons_checked_hd`, and `cons_checked` from it by `tchConsB_all`), in place of
`tieConsB`, whose search over pairs of generators and scans of `consItemsK` are quadratic in a sort's
generators: for a text with a sort of many generators (KItem over the cell sorts of a deep
configuration). It accepts only what `tieConsB` accepts (`tchConsB_sound`); a sentence `tieConsB`
accepts and it does not is left to the classes the probe gives otherwise.
--wf-parts states `wf_defn` from its conjuncts (`wf_of_parts_all`), each a decision of its own, the
names' distinctness by their codes (`KoreAML.Distinct`): `namesOK`'s `nodup` over the emitted
declarations compares every pair of names, which for a text of many symbols exceeds a 12 GiB scope.
--split writes the tie as test/Tie<Fixture>.lean and one file per heavy section, in the same
namespace: Tie<Fixture>Attrs (`attrs_agree`), Sig (`sig_origin`), Decls (`decl_counts`,
`decls_entailed`), Fns (the function equations), Rules, NoJunk, Cons; the first file keeps the
literals, the names, `wf`, the account, the consistency and the later sections. The declarations
are the ones the single file states, word for word, in its order. A test file imports no test file,
so each file repeats the literals and the definitions and facts it reads (`c`, `cH`, `trS`,
`classes`, `coreOK`, ...); a decision of a section other than the first file's head and consistency
is never repeated: a declaration of the later sections goes to the file of the decisions it reads,
and sections that read each other's decisions share one file (the rules with the functions where
the converse over Γ reads both, `gamma_origin`). `--print` lists the files, the merges and what each
file repeats. Without --split the output is the single file.
--account-sorted proves the account from the class lists sorted (`KoreAML.Distinct.msort`, as
`tacAccount_of_msort` reads it) where the user module's indices, in text order, are a range
a, ..., a+n-1 (`indices_eq`, `classes_sorted`), in place of the decisions of `isPerm` and `Nodup`,
which compare every pair of sentences; a text whose indices are no range is refused.
--heads-literal (with --chunk) writes Γ's heads as a literal (`gHeads`, `gHeads_eq : gammaHeads c =
gHeads`) and decides `account_absent`'s ranges on it (`absentPL`, equal to `absentP` by `gHeads_eq`),
so that no range recomputes Γ's heads.
--heads-codes (with --heads-literal) also writes Γ's heads with each name as its code
(`KoreAML.Distinct.strCode`, `gCodes`, `gCodes_eq : gHeads.map … = gCodes`) and decides the ranges
on a membership that compares a sentence's head name with Γ's by their codes, numbers, and the sort
arguments only where the codes are equal (`absentPC`, equal to `absentPL` by `strCode_inj`): a String
comparison runs over the names' characters, and a sentence of many heads compares each with all of Γ's.
--heads-plain (with --chunk; in place of --heads-literal and --heads-codes) decides `account_absent`'s
ranges on two literals of codes, each with one equation: Γ's symbol names (`gSymCodes`, as
--decl-syms-literal writes it, `symCodesOf c`) and its subsort pairs, each sort as the code of the
identifier `KoreAML.srt` writes (`gInjCodes`, `injCodesOf c`), read by `hasHeadCoded` (`absentPH`,
equal to `absentP` by `gammaHasHead_coded`, KcoreSpec/TieCodes.lean, with `gSymCodes_noInst`: no
code holds the byte of `{`). It builds no list of Γ's heads and decodes no name: a head is compared
with Γ's names (or, for `inj`, its subsort pairs) by numbers. Refused where a name of Γ's symbols
holds `{` (today's --heads-literal path is kept for such a text). It also decides `absent_proj_below`'s
first conjunct (the no-direction sentences that are equations of a projection, mapped, are
`absentProj` mapped) by the same ranges of the user module, `absProjE_a` each its own decision with
the members of `absentProj` in its range, joined by `tieFilterMap_range` (KcoreSpec/TieChunks.lean):
in one decision `(classOf "no direction").contains` scans the class once per sentence of the text,
all in one reduction (rcd's Absent file: 7.5 GiB with the one decision, 2.8 GiB by ranges of 50).
--attrs-parts states `attrs_agree` from its five conjuncts (`attrs_ctors`, `attrs_fns`, `attrs_hooks`,
`attrs_colls`, `attrs_prios`), each a decision of its own.
--attrs-blocks N (implies --attrs-parts) decides `attrs_ctors`, `attrs_fns` and `attrs_hooks` over the
symbol declarations (`AttrsAgree.symDeclsAt`) by blocks of N, and `attrs_prios` conjunct by conjunct
with each list by blocks of N (`decide_cheap N`): each conjunct compares every declaration with the
semantics' symbols, which in one decision exceeds a 12 GiB scope on a text of many symbols.
--decl-parts states `decl_counts` from six theorems, one per component of its tuple, each a decision of
its own; with --split they and `decl_counts` are in a file of their own, Tie<Fixture>DeclCounts.
--absent-file (with --split) puts the absent section (`absentP`, the heads' literals, the ranges,
`account_absent`, `absent_closed`, `absent_proj_below`) in a file of its own, Tie<Fixture>Absent.
--fn-blocks N decides `fn_shape` by `decide_map_blocks N K`, K = (Γ's equations) / N: K blocks of N
equations and the rest, each a decision of its own; refused for a text whose equations are aligned
up to a renaming (`fn_shape_but_owise`) or that states no `fn_shape`.
--decl-syms-literal writes Γ's symbol names as a literal of their codes (`gSymCodes`, `gSymCodes_eq :
(kernelSyms c).map (strCode ∘ c.symName ∘ name) = gSymCodes`) and decides `decl_counts` and the
`declsE` ranges on `hasSymL`, `plainSymsL` and `declItemsL`, which read it and are equal to `hasSym`,
`plainSyms` and `declItems` (`strCode_inj`): `hasSym` otherwise computes Γ's symbols once per symbol
declaration of the text. With --split the literal's decision is repeated in each file that reads it.
--nojunk-eq proves `nojunk_items` from the equation of each sentence's translation to Γ's no-junk
item of its sort over `Semantics.gens` (`njEq`, `njEqB`, `tnjItem_any_of_eq`), so that no decision
scans `consItemsK c`; the probe names each sentence's sort, and a sentence it names none for is
refused. With --chunk N the equations are decided by ranges of N sentences.
--nojunk-blocks N proves `nojunk_kitem_order`, and `nojunk_<sort>_order` of a sort with more than N
generators, from the translations of the sentence's disjuncts and of the item's, compared by ranges
of N (`tieEq_range`, `njTrOr_pat`): the text names the variable of each injection's disjunct `Val`
whatever its sort, where `noJunkDisjuncts` numbers a name it has given at another sort, so the
disjuncts agree only up to their translation. Both flags state the text's alias names once
(`aliasLit`, `aliasLit_eq`).
--lists-by-class proves `lists_in_account` (each sentence of `unmapped` and `uncovered` is in its class)
from `lists_classes` (each listed class is a class of the account) and `lists_sub` (for each class, the
listed sentences of it, in their order, are a sublist of its indices), joined by `tieAll_of_groups`:
deciding the statement directly computes `classOf` and scans it once per listed sentence, which over
some thousand sentences exceeds a 12 GiB scope; `lists_sub` reads each class's list once. A text whose
listed sentences of a class are not in the order of the class's indices is refused.
--sig-positions writes the origin of each item of `sigItems c` as a literal (`sigPos`): its position in
the text's signature, or, for an item the text's signature does not state, the registry sort or the
position in `hookSigs` of the hooked symbol whose surplus item it is, or next's arity; the `sigE` ranges
are decided on `sigFromAt`, which compares each item with the one item its origin names, and
`sig_origin` follows (`sigFromAt_sound`, `tieSigPos_all`), its statement unchanged. Otherwise each item
is searched for in the whole of the text's signature and then in each disjunct of `surplusItem`, each of
which scans the text's declarations.
--decl-positions writes the position in `sigItems c` of each item of `declItems` as a literal
(`declPos`); the `declsE` ranges are decided on `inSigItemsAt`, which compares each item with the one
item of `sigItems c` at its position, and `decls_in_sig` follows (`inSigItemsAt_sound`,
`tieDeclPos_all`, `decl_sizes`), its statement unchanged. Otherwise each item is searched for in
`sigItems c` up to its own position.
--fnfun-chunk N decides `fnFun_checked` and `fnFun_trS` (the function functional sentences as sort
predicates' `functional` sentences) by ranges of N sentences, each its own kernel decision
(`tieAll_range`): `fnFunOK` searches the sort predicates for each sentence's.
--builtin-decls also states, after `decls_entailed`, that Γ entails the G-arity item of each symbol
declaration of the text with a K builtin file's `Source`, without a `hook` attribute and without sort
parameters, of a symbol Γ has (`builtinDeclNames`, a literal list of names; `builtinDeclNames_has`;
`builtin_decls_entailed`, in the form `∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈
builtinDeclNames → Γ (cH H) ⊧ (arityItem sd).pat` that test/constructs/e6map.py reads as tying those
declarations' rows); refused where the text has no such declaration.
--hand ovlfn=FILE puts FILE in place of the section on what the sentences of a function-overloaded
symbol (`ovlFnApart`, below) say at the arguments an overload covers, required for a text with such a
sentence and refused for another. For each sentence i of `ovlFnApart`, FILE states exactly one of:
`ovlfn_at_values_<i>` (the sentence at values, for every H); `ovlfn_refuted_<i>` with i in
`def ovlFnRefuted : List Nat := [...]` (no model of Γ satisfies it, for every H; the list in text
order, holding only such sentences, and `ovlfn_refuted_sub` states it a sublist of `ovlFnApart`); or
`OvlFnHyp<i>` (a hypothesis on H), `ovlfn_hyp_at_values_<i>` (under it, the sentence at values),
`ovlfn_hyp_holds_<i>` and `ovlfn_hyp_fails_<i>` (an H at which it holds, one at which it fails). tiegen
reads only the names; their statements are the section's.
--hand consistency=FILE puts FILE in place of the consistency section, for a text that owes an
agreement, a clause's match independence, or a rule's or clause's condition (`owed_rules`,
`owed_clauses`): FILE proves the owed facts and states `consistent` for every H, with `facts` for an
agreement, and `owed_rules`, `owed_clauses` and `openDecidedH` (`OpenDecided` for every H) otherwise.
It also takes a text that owes a held-named function's fact (`Held`, `HeldOwed`) or the totality of a
`[total]` function (`total_named` not empty), beside any of those: FILE then states
`theorem consistent (H : HookParams) : Consistent (cH H)` (refused otherwise), with `held_named` or
`total_named`, and `fnHypH` (`FnHyp` for every H) where its route is `FnHyp`. Where it is not (a
held-named function's fact false, so `FnHyp` fails), the header and the summary say that the
function functional sentences, owed as `FnHyp`, are not shown by the tie, unless FILE states them at
values in every model of `Γc` from the sort predicates' own results (`theorem fnFun_at_values (H :
HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat`, LibEvSortPred.lean), which
they then say, with `not_fnHypH` where FILE states `FnHyp` false for every H.
A text one of whose clauses has a predicate other than `\\top` (`Semantics.clausesPreTop` false), of which
`kcore gen --core` states no `Obl` and whose package takes `FnHyp` itself as the hypothesis of its
statements (`clausesPreTop_false`), is taken only under --hand consistency, as one that owes `FnHyp`:
FILE states `theorem consistent (H : HookParams) : Consistent (cH H)` and either `fnHypH` or
`not_fnHypH` (refused otherwise), beside the facts it owes (`owed_rules`, `owed_clauses`, `match_named`
and the others above). The function functional sentences are then not stated at values (both routes
read `clausesPreTop`): the header says they are owed as `FnHyp`.
Where each sentence of the class function functional is, as written, a sort predicate's `functional`
sentence (`LibEv.funPat`), the clauses' predicates are `\\top`, no clause binds a variable by
`\\exists` and no clause's condition reads a variable its patterns leave open, the tie states those
sentences at values in every model of `Γc` for every H from the sort predicates' own results
(`fnFun_at_values`, by `LibEv.sortPredFun_evC_withHooks`), whatever FILE states, unless FILE states
them itself.
Otherwise, where the tie states `FnHyp` for every H (`fnHypH`, without a hypothesis on H), each
sentence of the class is, as written, a sort predicate's `functional` sentence or that of a function
of the text declared total (`LibEv.predFunRegS`: its sorts any sorts of the text), the clauses'
predicates are `\\top` and no clause binds a variable by `\\exists`, the tie states them at values in
every model of `Γc` for every H from `FnHyp`, which gives such a function its values and decides the
clauses' conditions where `needsWitness` holds (`fnFun_at_values`, by `LibEv.fnFun_evC_withHooks`).
--fn-readings ties the function equations where Γ's items are not the text's sentences one for one
and neither the narrowed nor the reordered pairs (`fn_pairs`) cover them: each of Γ's items is its
sentence as written (`shape`), or the narrowed or reordered pair as there, or (`rd<j>_*`) the item
whose right side `\\and{s'}(x, y)` the sentence writes with an alternative beside x that holds nothing,
`\\bottom{S}()` or an application with such an argument (the reading `orBottom`, `Parse.dropEmptyAlts`:
`TieRhs.orEmptyIn`, `TieRhs.orEmptyOK_iff`, the same models of definedness), or (`cut<j>_*`) the item
whose premise Γ writes through a cut of the clause's `requires`, the sentence being the premise as the
text writes it (`andUnderAppCut`, `notAsCondition`: `TieCutEq.textItem`, up to the names of the
variables; each direction over what it reads, definedness, the constructors' facts of a model of the
theory, and for `notAsCondition` the closure of Bool, `boolClosed`, a premise the theorems name and the
summary's `owed` lists), or (`un<j>_differs`) an item no reading here ties, whose sentence is
`uncovered` and which `fns_entailed` and `fns_from_text` leave out; on a text that reads a confined
sort too (its statements over Γ, which `Γc` holds). The probe then also writes, per item, whether the
empty-alternative reading ties it (`WR` lines) and the cuts that tie it (`WC` lines).
Without the flag the output is unchanged.
--at-values N,... names the user lemmas (by `AxiomDecl.index`) that are of the class `user lemma at
values` in place of `user lemma`; an index that is no user lemma of the text is refused.
--reads-h N,... names the user lemmas (by `AxiomDecl.index`) that are of the class `parameter lemma`
in place of `user lemma` though they apply no parameter symbol without `impl`: lemmas whose truth at
values reads a value the interpretation gives, by a function of the semantics at argument lists none
of its clauses decides (Γ states the function's rest from H) or by a hook at a point its text leaves
open. No shape of the sentence decides that (it depends on where the clauses and the hook's text
decide); the author names the index, and the tie decides of it the necessary condition
`appliesHRead` (KcoreSpec/TieParamLemma.lean; `paramlemma_reads_h`): it applies, at a head Γ has, a
symbol through which evaluation may read the interpretation (`Parse.lawReadsFL`). Refused: an index
that is no user lemma of the text (a parameter lemma by its shape among them), one `--at-values`
names as well, and one whose sentence fails `appliesHRead` (it reads nothing H gives).

It refuses, with the reason, a fixture without a kompiled text, a text whose `kcore account` is not
the fixture's account.txt, a text the reader refuses, a text whose obligations `kcore gen --core`
states in a form not in OBL_FORMS, or which owes termination, or, without --hand consistency,
totality, a held-named function's fact, a match independence or a rule's or clause's condition;
a text whose `attrsAgree` fails; a law of the reader or a law item of Γ that is not one sentence as
written; a text with a law of a function that the probe refutes at values (Function laws, below).

Function laws. A law of a function (`Definition.laws`) is owed as `FnLaws`: `LawAt` for each law,
under every well-sorted substitution its two sides have the same `EvalTerm` results. Where it fails
at every H the tie, which takes it as a hypothesis, states nothing, and the text is not tied: by the
owed-sentence rule (test/constructs/rows-header.toml, items 3 and 4) a fixture of it is a test of
the check (DONE-0 C8). That it fails at every H is not decidable from the text in general: `LawAt`
quantifies over all values of the law's variables (infinitely many of Int), so no finite evaluation
settles that it holds, and where it fails one valuation witnesses it, which a search can find but
whose absence it cannot show. What tiegen decides is such a witness. The probe evaluates both sides
with `Cert.evalTC` (fuel 4000) at the valuations of the law's variables drawn from 0, 1, 2, 3, -1,
-2, true, false and the nullary constructors of their sorts (4096 at most). A valuation at which both
sides have values (`some (some v)`) that differ (`Exec.same`) refutes the law at every H: `evalTC`
has no result where it would consult the interpretation, so with no open generator its result is
the one at every H (`Cert.evalTC_withHooks`) and the executable evaluation's (`Cert.evalTC_sound`),
hence the `EvalTerm` result (`Exec.evalT_sound`, from `ok`, `srReady`, `matchReady`, which no H
changes, and `lawSorted`); and `EvalTerm` is functional where `CoherentAll` holds
(`Det.coherentAll_of_nil`: `clausesFixed`, no agreement owed), so `LawAt` would give the right side
the left side's value. The search runs only where those conditions hold. Only values on both sides
count: where a side has no result `LawAt` can fail while the sentence holds (`Parse.fnLawEntry`), so
that is no witness. tiegen refuses such a text, naming the witness (test/FnLawFixtures.lean's
`Bad.not_lawAt` is the kernel's refutation for e2-fn-assoc-bad). A law the search does not refute
(no witness among those valuations, a side without a value or reading the interpretation there, or
the conditions not met) is not shown to hold: tiegen writes the tie with `FnLaws` owed (the
summary's `law_search`), and before the tie counts as a row's evidence the lane checks the law:
proves `FnLaws` at some H (as `FnLawFixtures.Assoc.fnLaws`), or refutes it at every H, which makes
the fixture a C8 test. `--self-test` runs the search on e2-fn-assoc-bad (refused, at var 2 = 1),
e2-fn-assoc and e2-fn-assoc-rest (both not refuted).

What it states where the text:
- owes an agreement (`agree_named` not empty): `facts` and `consistent` take it as a hypothesis
  (`AgreeOwed`), the proof owed (`owed` in the summary), unless `--hand consistency` gives it;
- has an open generator (`raw`; one at most): `params_raw`, `facts` and `consistent` for every H
  satisfying `OpenLaws`, at `lawHooks c H` for every H, for every H where it has no law
  (`openLaws_any`); its law sentence is Γ's law item (`openlaw_*`, the class `open generator law`),
  its functional sentence no item of Γ (`open_functional_not_item`, the class `open generator
  functional`);
- states a law of a function (`Definition.laws`): `law_text` (the sentence as written is `lawPattern`),
  `law_not_item`, `law_account` (the class `function law`);
- has a lemma applying a parameter symbol no hook implements (`isParamLemma`, or a `simplification`
  sentence of K's builtin library applying one, which the reader reads as the library's text and of
  which Γ holds no item; the class `parameter lemma`, direction hypothesis), or a user lemma
  `--reads-h` names: `paramlemma_account`, and `ParamLemmaWitnessAtValues`, one H at
  which `FnHyp` holds and every parameter lemma holds at values (`EntailsAtValues`), stated
  and owed (`owed` in the summary);
  `paramlemma_heads`: every `simplification` equation of the user module whose left side's head is
  a parameter symbol without `impl` is in that class; and, for the lemmas `--reads-h` names,
  `paramlemma_reads_h`: each applies a symbol through which evaluation may read H (`appliesHRead`);
- has a lemma of a user's file that applies no such parameter symbol (the reader's class inert
  simplification, a `Source` outside K's installation): the class `user lemma` (direction entailed),
  or `user lemma at values` (direction atValues) for the indices `--at-values` names;
  `userlemma_account`, and the Props `UserLemmaEntailed` (Γ entails each for every H) and
  `UserLemmaAtValues` (`EntailsAtValues` of each for every H), stated and owed (`owed` in the
  summary). tiegen cannot decide which of the two holds: the default is the stronger class, whose
  proof fails where the lemma holds at values only, and the author then names the index; it fails
  as well where the lemma's truth at values reads a value H gives (a function's rest, a hook's open
  point), which some H meet and others refute, and the author then names the index by `--reads-h`
  (the class `parameter lemma`). A user's
  equation of a symbol whose value the registry gives (`Parse.regLemmaEqn`, no `simplification`
  needed: the attribute does not change what an equation states) is out of Γ as well and rests on
  that symbol's graph, which Γ states at values: the class `user lemma at values` without
  `--at-values` (a parameter lemma where it applies a parameter symbol without `impl`);
- has a parameter symbol no hook implements (the H form): `total_named` and `obl_nil` at `[]`, which
  holds where no `[total]` function owes a parameter's totality; where one does, at
  `defn.totalParams` (the `[total]` functions are total under every H total on the parameters the
  text declares total), and `fnHypH` and `consistent` take `ParamsTotal c defn.totalParams H`, which
  one H meets (`paramsTotal_witness`, `consistent_witness`: `constH` at a value exhibited of the
  parameters' result sort); refused where that list is not empty, no one exhibited value is of every
  such parameter's result sort, or an open generator, agreement, match independence or condition is
  owed beside it;
- is not plain (`FnFacts`): `owed_rules`, `owed_clauses`, `openDecidedH`;
- reads a confined sort: `readsConfined_c` true, the theory `Γc`, the entailments
  over Γ restated over `Γc` (`entails_c`, the `_c` forms), `gamma_origin_c` (Bool holding only its
  literals, `Γcl` is `boolClosed`; otherwise refused);
- has `[owise]` equations whose items are their sentences up to a renaming of element variables:
  `fn_align` with test/NonExecOwiseTie.lean's `alphaB` section, `fn_shape_but_owise`,
  `owise_not_literal`, the converse up to the renaming;
- has one function equation whose item is not its sentence because Γ holds it with the premise that
  the clauses of a smaller priority that are not `aside` do not apply (`prioEquation`; the text
  neither confined nor with an open generator), every other item its sentence's translation up to a
  renaming of a free variable (`TiePair.sameB`): `fnText` by head symbol and priority
  (`TiePair.fnTextOf`), `fns_account` over the function-equation and priority-equation classes,
  `w_text` (the item without that premise is the sentence, `TiePair.minusNeg`), `w_differs`, `w1`
  (W1: the sentence entails the item), `shape`, `fns_entailed`, `fns_from_text`, `fn_prios`, and
  the converse over Γ's content `gamma_from` (`TiePair.Pre`);
- has several such items, or items that are their sentences up to the order of the operands of
  their sorted disjunctions and the names of their variables (`TieAlpha.acEqB`: an `[owise]`
  equation's exclusion, which the text writes in another order with other bound variables), every
  other item its sentence's translation up to a renaming (`TiePair.sameB`): per narrowed item j
  `prio<j>_narrowed`, `prio<j>_text`, `prio<j>_differs`, `prio<j>_w1` (W1), per such item j
  `ac<j>_same`, `ac<j>_differs`, `ac<j>_iff` (both directions, from `TieAlpha.acEqB_sat`), and
  `fns_account`, `shape`, `fns_entailed` (all but the narrowed ones), `fns_from_text`, `fn_prios`,
  `gamma_from`. The account puts a narrowed sentence without an ens counterpart in the class
  priority equation whatever its priority (one of priority 50, written or not, is narrowed beside a
  clause of a smaller priority).
  An item that is none of these is left `uncovered`;
- has a rule with rules of a smaller priority, whose item Γ holds also with the premise that none of
  them applies (`prioRuleK`: `¬ ⋁ competitors` before `⌈rhs ∧ ens⌉`), a premise its sentence states
  by its priority attribute only: the item without both premises is the sentence (`rule<j>_text`
  on `minusComp`), W1 by `item_of_minusComp`, and `rule_prios` (the priorities the sentences state
  are the rules'), so the competitors are the rules whose sentences state a smaller priority;
- has function items of Γ that no user sentence is and each one sentence of the text's prelude
  modules is, as written (KSEQ's `append`, which Γ holds where a rule or an equation applies it),
  every other item one user sentence's: `fnText` lists those sentences among the user ones (literals
  of the prelude module's axioms, `user_axioms Prelude<Module>`, which `prelude<Module>_eq` states
  are the text's), `fn_shape` as for user sentences only, and `fns_account`: `fnText`'s user-module
  sentences are the function-equation class, and its others those prelude sentences;
- has the no-junk sentence of a sort with generators other than KItem that is not Γ's item as
  written: the item over its generators in the text's order, a permutation of `Semantics.gens`
  (`<sort>TextGens`), `nojunk_<sort>_entailed` (for an open generator's sort also that it is open);
  the probe tries every permutation of a sort of at most 5 generators, and for a larger sort the
  one order the sentence's disjuncts apply the generators in (each disjunct's symbol, or `inj` from
  its sort), taken where the item over that order is the sentence;
- has an overload axiom `f(lift K̄) = lift(g(K̄))` of an overloading symbol f over g (`tieOvlEqB`), or
  a no-confusion sentence of two symbols with values of their argument sorts at which the two have
  one normal form (`tieOvlNcB`; an overloading symbol and a symbol it overloads, the values exhibited
  for g's arguments and lifted to f's): the account's classes in `tieClassesOvl`'s order (`tieClasses`
  with the class overload equation, direction entailed, before no direction); the overload axioms in
  that class with `ovleq_account` and `ovleq_entailed`; the no-confusion sentences in no class,
  listed apart in the account (`ovlRefuted`), with `ovlnc_refuted` (no model of Γ satisfies one, for
  every H). The account of a text with neither lists the classes in `tieClasses`' order;
- has KItem's no-junk sentence over KItem's generators but the injections from sorts the definition
  holds below KItem (`Parse.ReadingNote.tokKItem`; the probe decides it with `kitemOmitB` and the
  item over `kitemOmitGens`, KcoreSpec/TieTokKItem.lean): weaker under tokKItem, in no class, listed
  apart in the account (`tokKItemApart`), with the left-out sorts (`tokKItemSorts`), `tokkitem_text`,
  `tokkitem_entails_item` and `tokkitem_item_in_gamma` (the sentence entails Γ's item, which is Γ's
  for every H), `tokkitem_holds_iff_empty` (in a model of Γ it holds exactly where no left-out sort
  has an element), and, where a left-out sort has a value the reader exhibits (`Parse.exhibit?`),
  `tokkitem_refuted` (Γ with it has no model), else `tokkitem_refuted_with_nonempty` (no model of
  Γ satisfies it with the text's G-nonempty item of a left-out sort). The apartness of the images
  comes from Γ's Cons-Dist items, which Γ holds through the reading's subsort, not from the text;
  no model of the text is claimed or denied. One such sentence per text is stated;
- has the `functional`, same-constructor or different-constructors sentence of a function-overloaded
  generator (an overloading symbol one of whose overloads is a function, `Semantics.fnOvl`; the probe
  decides it with `tieOvlFnFunB`, `tieOvlFnInjB`, `tieOvlFnDistB`, KcoreSpec/TieOvlFn.lean), which Γ
  holds at the arguments no overload covers only (`funUncItem`, `injUncItem`, `distUncItem`): weaker
  under overloadFunction, in no class, listed apart in the account (`ovlFnApart`). Part 1, for every
  H: `ovlfn_text_<i>` (the sentence's kind, sort and generators), `ovlfn_item_in_gamma_<i>` (Γ's item
  at uncovered arguments) and `ovlfn_entails_item_<i>` (in a model of Γ the sentence entails it; a
  no-confusion sentence with the `functional` sentence of its function-overloaded generator, which
  the text states and `ovlFnApart` holds, or the text is refused). Part 2, what it says at covered
  arguments, is the hand section `--hand ovlfn`'s;
- has the `functional` sentence of a parameter symbol no registry hook implements that the text
  declares total (`isParamFunctional`, the class `parameter functional`, direction hypothesis):
  `total_params` (`Definition.totalParams`), `paramfunctional_account`, `paramfunctional_heads`; it is
  owed as `ParamsTotal`, the hypothesis on H the statements take. The functional sentence of a
  parameter without `impl` the text does not declare total is refused.

What the test states (each a kernel decision or a proof from one):
- layer 1: `wf defn = true` (or `coreOK` with the failing conjuncts of `wf` named); the account (the
  class lists, in `tieClasses`' order, partition the user module's sentences); `account_absent` and
  `absent_closed`; where the no-direction class holds equations of projections `project:X`,
  `absent_proj_below` (each X is K, KItem or below KItem in Γ, `GenEqs.projBelowB`, so Γ entails
  what the equation states of its constructor pattern); `attrs_agree`; `sig_origin` and
  `decls_entailed` (by ranges of the lists);
- the acceptance conditions themselves: `noRaw`, `readsConfined_c`, the four obligation lists empty,
  `consistent` for every H;
- by class, the theorems of test/TieEns.lean over the sentences they hold of: the function
  equations (`fn_shape`, `fns_entailed`, `fns_from_text`, `fn_prios`), the constructor sentences
  (`cons_entailed`), the no-junk sentences (`nojunk_trivial_entailed`, `nojunk_items`,
  `nojunk_kitem_entailed`), set idempotence (`idem_refuted`) and the library sample `I -Int 0 = I`
  (`lib166`, `lib166_at_values`) where the text holds that sentence, and `gamma_origin` where
  every premise of Γ has its origin here;
- the idempotence sentence of each other set collection (a definition's own, hooked to SET.concat):
  `own_idem_refuted_<i>` from `Faithful.setColl_idem_refuted_text`, its shape and the collection's
  key value one kernel decision (`own_idem_ok_<i>`).

The classes. A sentence whose text equals one of f2-examples/ens.kompile.kore's user module (up to
`Location`, `Source` and `UNIQUE'Unds'ID` attributes and whitespace) takes that sentence's class in
test/TieEns.lean's account. Any other sentence (`unmapped` in the test) takes its class from what a
probe evaluates of it (a run of the Lean definitions on the text: the heads it applies, each a symbol
with its sort arguments (`appHeadsOf`), against Γ's (`gammaHasHead`),
its place among Γ's function items, `tieConsB`, the constructor items; a symbol the registry interprets
is a registry hook or a parameter symbol a registry hook implements, `MtCellMap:in_keys` with
`MAP.in_keys`; an overloading symbol is a generator, and its functional sentence is of the class
constructor functional where `tieConsB` accepts it, which it does where the symbol overloads no
function) and from its form (kompile's
`// functional`, `// subsort`, `// no confusion` and `// no junk` comments, the `assoc`, `unit`, `idem`,
`priority` and `owise` attributes, set variables, a builtin `Source`); a sentence that neither gives a
class is refused by name. A mapped sentence whose probe class differs from ens's is refused too.
Whether a sentence applies a head Γ lacks is a fact of the text's Γ, not of ens's: a sentence equal
to one of ens's that is in the no-direction class in one of the two texts and not in the other (a
projection that no read sentence of ens applies and a read sentence here does) is not mapped; it
takes its class from the probe and its form.
A sentence of a class with a theorem in test/TieEns.lean that no theorem here holds of is listed in
`uncovered`, with its class, and so is each user lemma: the part of the tie that is left to write by
hand.

What the kernel checks of the classes: that the lists partition the user module (`account`), that
the no-direction class is exactly the sentences applying a head Γ lacks (`account_absent`), and,
by each class theorem, that its list (`fnText`, `ruleText`, `consText`, the no-junk lists) is what
the theorem says. It does not check the other labels: which of the classes without a theorem here
(function functional, hooked functional, collection law, library, set-variable lemma, user lemma,
user lemma at values) a sentence is in, and which of the four constructor classes a sentence of
`consText` is in, rest on ens's account (for a mapped sentence) or on the form read above (for an
unmapped one).
"""
import hashlib, json, os, re, subprocess, sys, tempfile, textwrap, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
KS = os.path.dirname(os.path.dirname(HERE))          # kcore-spec
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import kfix  # noqa: E402  (the cache of kompiled texts, kompile.txt's hashes)

FX = os.path.join(KS, "test/constructs/fixtures")
KCORE = os.environ.get("KCORE_BIN") or os.path.join(KS, ".lake/build/bin/kcore")
# K 7.1.337's builtin directory, as the f2-examples texts copied from the cache name it
BI = ("/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406"
      "/include/kframework/builtin")
ENS_TEXT = os.path.join(KS, "f2-examples/ens.kompile.kore")
ENS_TIE = os.path.join(KS, "test/TieEns.lean")
WRAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]

CLASSES = ["function equation", "rewrite rule", "priority equation", "constructor functional", "subsort",
           "injectivity", "distinctness", "no junk", "function functional", "hooked functional",
           "collection law", "library", "set idempotence", "set-variable lemma", "function law",
           "open generator law", "open generator functional", "parameter functional", "parameter lemma",
           "user lemma", "user lemma at values", "no direction"]
# the classes test/TieEns.lean states a theorem of, sentence by sentence
THEOREM_CLASSES = {"function equation", "rewrite rule", "priority equation", "constructor functional",
                   "subsort", "injectivity", "distinctness", "no junk", "set idempotence"}
CONS_CLASSES = ["constructor functional", "subsort", "injectivity", "distinctness"]
# The classes of the sentences the reader reads as laws or Γ holds for an open generator: a law of
# a function (`Definition.laws`) is no item of Γ and is owed as `FnLaws` (direction hypothesis); an
# open generator's law is Γ's law item (`lawItemsK`, direction equal); an open generator's
# functional sentence is no item of Γ and is owed at values as `OpenTotal` (direction hypothesis).
LAW_FN_CLASS = "function law"
LAW_OPEN_CLASS = "open generator law"
OPEN_FUNCTIONAL_CLASS = "open generator functional"
# The class of the `functional` sentence of a parameter symbol no registry hook interprets that the
# text declares total (`isParamFunctional`, `Definition.totalParams`): the reader reads it as that
# declaration; Γ states the parameter's graph at values from the interpretation, so the sentence holds
# at values where H gives the parameter a value at every argument list of its sorts, which the
# statements take as the hypothesis `ParamsTotal` (direction hypothesis).
PARAM_FUNCTIONAL_CLASS = "parameter functional"
# The class of a lemma the reader leaves out of Γ (or a `simplification` sentence of K's builtin
# library, of which Γ holds no item) whose truth at values reads a value the interpretation gives: by
# its shape where it applies a parameter symbol no registry hook interprets (`isParamLemma`,
# `isLibParamLemma`), or named by `--reads-h` where it applies a function at argument lists none of
# its clauses decides (Γ states the function's rest from H) or a hook at a point its text leaves open,
# the probe deciding `appliesHRead` of it. Its truth depends on the interpretation, so it is owed as a
# hypothesis on H (direction hypothesis), at values: Γ states the parameter's graph, a function's rest
# and a hook's open point at values only (`ΓDomains`, `ΓFallback`), so a model of Γ may hold an element
# of an unconfined sort that is no value's, at which no item of Γ constrains them, and the sentence at
# every valuation can fail there at every H. The tie of
# a text with one owes one H at which `FnHyp` holds and every one of them holds at the
# valuations sending its variables to values (`ParamLemmaWitnessAtValues`, `EntailsAtValues`), since
# a hypothesis no H satisfies would tie a text without a model.
PARAM_LEMMA_CLASS = "parameter lemma"
# The classes of a lemma of a user's file that the reader leaves out of Γ (inert simplification),
# that applies no parameter symbol without `impl` and that `--reads-h` does not name: owed for every
# H. `user lemma` (direction entailed): Γ entails it at every valuation; `user lemma at
# values` (direction atValues): it holds at the valuations sending its variables to values, because
# it rests on an interpreted symbol's graph, which Γ states at values. Neither has a generated
# theorem: the tie states what is owed (`UserLemmaEntailed`, `UserLemmaAtValues`), proved by hand.
USER_LEMMA_CLASS = "user lemma"
USER_LEMMA_VALUES_CLASS = "user lemma at values"
USER_LEMMA_CLASSES = (USER_LEMMA_CLASS, USER_LEMMA_VALUES_CLASS)
# the name of the projection `project:X` of a sort X is this prefix and X
PROJ_PREFIX = "Lblproject'Coln'"
# The sentences of an overloading symbol and a symbol it overloads. The overload axiom
# `f(lift K̄) = lift(g(K̄))` is the class `overload equation` (direction entailed): Γ's overload item
# states it at every element, the sentence within f's result sort, and Γ entails the sentence
# (`tieOvlEq_entailed`, where `tieOvlEqB` holds). That class is not one of `tieClasses`: the account
# of a text with such a sentence lists its classes in `tieClassesOvl`'s order (KcoreSpec/TieOvlEq.lean,
# the class before no direction), every other text's account lists `tieClasses`. The no-confusion sentence of
# two such symbols states them disjoint where the overload axiom equates them: Γ refutes it
# (`tieOvlNc_refuted`, where `tieOvlNcB` holds and `tieConsB` does not). It is in no class (a sentence
# the reader can decide contradicts what the semantics states of its symbols claims none): the account
# lists it apart (`ovlRefuted`), with the theorem that no model of Γ satisfies it.
OVL_EQ_CLASS = "overload equation"
OVL_NC = "refuted, no class"
# KItem's no-junk sentence that leaves out the injections from sorts the definition holds below KItem
# (`Parse.ReadingNote.tokKItem`; the probe's `omit`, where `kitemOmitB` holds): Γ holds the sorts
# below KItem, so its no-junk item of KItem has a generator the sentence lacks. The sentence entails
# that item (`kitemOmit_entails_item`), not conversely: in a model of Γ it holds exactly where none
# of the left-out sorts has an element (`kitemOmit_holds_iff_empty`), the elements' images being
# apart from the listed injections' by Γ's Cons-Dist items, which exist through the reading's
# subsort. It is in no class of `tieClasses`: the account lists it apart (`tokKItemApart`), with
# those theorems and, where a left-out sort has a value the reader exhibits, that Γ with it has no
# model (`kitemOmit_refuted_exhibit`), else that no model of Γ satisfies it with the text's
# G-nonempty item of a left-out sort (`kitemOmit_refuted_nonempty`).
TOK_OMIT = "weaker under tokKItem, listed apart"
# The `functional`, same-constructor and different-constructors sentences of a function-overloaded
# generator (an overloading symbol one of whose overloads is a function, `Semantics.fnOvl`; the
# probe's `ovlFn`, from `tieOvlFnFunB`, `tieOvlFnInjB`, `tieOvlFnDistB`). Γ holds each at the
# arguments no overload covers only (`funUncItem`, `injUncItem`, `distUncItem`); at a covered
# argument the sentence says what the overloaded function's values are, which Γ states only through
# that function's equations. It is in no class of `tieClasses`: the account lists it apart
# (`ovlFnApart`). Part 1, for every H: the sentence, with the `functional` sentence it is joint with,
# entails Γ's item at uncovered arguments (`tieOvlFn*_weaker_Γ`), which is Γ's. Part 2, what it says
# at covered arguments, is written by hand (`--hand ovlfn=FILE`), per sentence one of: the sentence at
# values for every H, its refutation for every H (listed in `ovlFnRefuted`), or a hypothesis on H it
# is owed under, with an H at which the hypothesis holds and one at which it fails.
OVL_FN = "weaker under overloadFunction, listed apart"


class Refused(Exception):
    pass


def nested(s):
    """`[[1], [2, 3]]` as a list of lists of numbers."""
    s = s.strip()
    if s in ("", "[]"):
        return []
    return [[int(x) for x in re.findall(r"\d+", g)] for g in re.findall(r"\[([^\[\]]*)\]", s[1:-1])]


# names a generated file defines or reads, which a name made from the text must not take
RESERVED = {"c", "cH", "kore", "defn", "U", "trS", "fn", "f", "at", "by", "do", "fun", "let", "in", "if", "then",
            "else", "have", "show", "from", "end", "def", "theorem", "match", "with", "open", "namespace", "where",
            "instance", "structure", "class", "import", "names", "classes", "consText", "fnText", "ruleText",
            "ovlEqText", "ovlNcText", "ovlRefuted", "tokKItemApart", "tokKItemSorts", "tokKItemGens",
            "ovlFnApart", "ovlFnText", "ovlFnRefuted",
            "lawText", "lawIdx", "callOrder", "Pre", "Families", "hasSym", "declItems", "plainSorts", "plainSyms",
            "fnFunIdx", "fnFunText", "fnFunOK"}


def short_sym(n):
    """A symbol's name without kompile's `Lbl` prefix, where that is a plain identifier."""
    s = n[3:] if n.startswith("Lbl") else n
    return s[:1].lower() + s[1:] if re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", s) else None


def ident(base, fallback, taken):
    """`base` where it is free, else `fallback` (made free); the name is then taken."""
    n = base if base and base not in taken else fallback
    while n in taken:
        n += "'"
    taken.add(n)
    return n


def law_what(idx, raws, sents):
    """What the law sentences state, by their attributes: `the associativity of `f``, …"""
    seen = {}
    for i in idx:
        f = short_sym(sents[i]["eh"]) or sents[i]["eh"]
        r = raws.get(i, "")
        k = "associativity" if "assoc{}()" in r else "idempotence" if "idem{}()" in r else "unit" if "unit{}()" in r else ""
        seen[(k, f)] = seen.get((k, f), 0) + 1
    out = []
    for (k, f), n in seen.items():
        if k in ("associativity", "idempotence"):
            out.append(f"the {k} of `{f}`")
        else:
            out.append(f"{'a' if n == 1 else numword(n)} {k + ' ' if k else ''}law{'' if n == 1 else 's'} of `{f}`")
    return ", ".join(out)


NUMWORDS = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]


def numword(n):
    return NUMWORDS[n] if n < len(NUMWORDS) else str(n)


# ---------------------------------------------------------------------------------------------
# The sentences of a text, as findings/FIX-core-wave-A-axmap.py reads them

def axioms(text):
    """(index, module, normalised text) of each axiom, index counted from 1 over the whole text,
    the text with whitespace runs made one space and the Location, Source and UNIQUE'Unds'ID
    attributes dropped."""
    out, cur, mod = [], None, None
    for line in text.split("\n"):
        m = re.match(r"\s*module (\S+)", line)
        if m and not line.strip().startswith("//"):
            mod = m.group(1)
        if re.match(r"\s*axiom\s*\{", line):
            if cur:
                out.append(cur)
            cur = [mod, line]
        elif cur is not None:
            if line.strip() == "" or re.match(r"\s*(sort|symbol|hooked-sort|hooked-symbol|alias|endmodule|import|//)", line):
                out.append(cur)
                cur = None
            else:
                cur.append(line)
    if cur:
        out.append(cur)
    res = []
    for i, a in enumerate(out):
        s = re.sub(r"\s+", " ", " ".join(a[1:]))
        raw = s
        s = re.sub(r"org'Stop'kframework'Stop'attributes'Stop'(Location|Source)\{\}\(\"[^\"]*\"\)(, )?", "", s)
        s = re.sub(r"UNIQUE'Unds'ID\{\}\(\"[^\"]*\"\)(, )?", "", s)
        res.append((i + 1, a[0], s, raw))
    return res


def user_axioms(text):
    ax = axioms(text)
    um = ax[-1][1]
    return um, [a for a in ax if a[1] == um]


def ens_classes():
    """test/TieEns.lean's account: index -> class."""
    t = open(ENS_TIE).read()
    body = t[t.index("def classes : List (String × List Nat) :="):]
    body = body[:body.index("/-- The indices of a class. -/")]
    out = {}
    for name, nums in re.findall(r'\("([^"]+)", \[([^\]]*)\]\)', body):
        for n in re.findall(r"\d+", nums):
            out[int(n)] = name
    return out


# ---------------------------------------------------------------------------------------------
# The text, the account and the obligations, natively

def camel(name):
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_]", name))


def restored_text(name):
    h = kfix.recorded_sha(name)
    if not h:
        raise Refused(f"{name}: kompile.txt records no kompiled text (an error fixture, a kore fixture, or not run)")
    t = kfix.recorded_text(name)
    if t is None:
        raise Refused(f"{name}: the kompiled text of sha256 {h} is neither in .lake/kfix nor in the cache "
                      f"{kfix.CACHE} (`kfix.py run {name}` or `kfix.py cache-import`)")
    rel = f"kcore-spec/test/constructs/fixtures/{name}"
    out = t.replace("BUILTIN/", BI + "/").replace("FIXTURE/", rel + "/")
    back = out.replace(BI + "/", "BUILTIN/").replace(rel + "/", "FIXTURE/")
    if hashlib.sha256(back.encode()).hexdigest() != h:
        raise Refused(f"{name}: the text with its paths restored does not write back to sha256 {h}")
    return out


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def account_check(name, path):
    a = run([KCORE, "account", path], cwd=KS)
    got = a.stdout + a.stderr
    want = open(os.path.join(FX, name, "account.txt")).read()
    cut = lambda s: [l for l in s[s.find("\nuser module"):].split("\n") if l and l != "(exit 0)"]
    if a.returncode != 0 or "\nuser module" not in "\n" + got:
        raise Refused(f"{name}: `kcore account` fails on the text: {got.strip()[-400:]}")
    if cut("\n" + got) != cut("\n" + want):
        raise Refused(f"{name}: `kcore account` of the text differs from the fixture's account.txt (stale fixture or binary)")
    m = re.search(r"^parse: ok; wf (\w+); failing: \[(.*)\]$", got, re.M)
    if not m:
        raise Refused(f"{name}: the account prints no `parse: ok` line")
    wf = m[1] == "true"
    failing = [x.strip() for x in m[2].split(",") if x.strip()]
    m2 = re.search(r"^coreOK: (\w+); failing: \[(.*)\]$", got, re.M)
    if not m2 or m2[1] != "true":
        raise Refused(f"{name}: coreOK fails ({m2[0] if m2 else 'no coreOK line'})")
    if re.search(r"^refused by the account: (\d+)$", got, re.M)[1] != "0":
        raise Refused(f"{name}: the account refuses sentences")
    return wf, failing


# The forms `kcore gen --core` states the obligations in (KcoreGen.genFnHyp): without a parameter
# symbol no hook implements, `Obl : Prop := K defn.sem callOrder []`; with one, the H form
# `Obl (H : HookParams) : Prop := K (defn.sem.withHooks H) callOrder defn.totalParams`, behind
# `OpenLaws (defn.sem.withHooks H) →` where a parameter is an open generator. K is `FnObligations`
# for a plain definition and `FnFacts` otherwise (`OpenDecided` then proved from `owed_rules` and
# `owed_clauses`).
OBL_FORMS = [
    (r"FnObligations defn\.sem callOrder \[\]", "FnObligations", False),
    (r"FnFacts defn\.sem callOrder \[\]", "FnFacts", False),
    (r"FnObligations \(defn\.sem\.withHooks H\) callOrder defn\.totalParams", "FnObligations", True),
    (r"FnFacts \(defn\.sem\.withHooks H\) callOrder defn\.totalParams", "FnFacts", True),
    (r"OpenLaws \(defn\.sem\.withHooks H\) → FnFacts \(defn\.sem\.withHooks H\) callOrder defn\.totalParams",
     "FnFacts", True),
]


def named_list(src, thm):
    """The numbers of the list a `theorem THM : … =\n    [..] :=` of `kcore gen`'s FnHyp modules
    states (its entries' comments and a type ascription dropped), or None without that theorem."""
    m = re.search(rf"^theorem {thm} : .*?=\s*(\(\[\] : [^)]*\)|\[.*?\])", src, re.M | re.S)
    if not m:
        return None
    return [] if m[1].startswith("(") else [int(x) for x in re.findall(r"\d+", re.sub(r"/-.*?-/", "", m[1]))]


def obligations(name, path, hand=False):
    """What `kcore gen --core` names of the text: the obligation form, the call order, the
    functions its agreement list names, whether it names a clause's match independence (`match`) and
    whether it owes a rule's or clause's condition (`owed`), the held-named functions (`held`,
    `held_names`) and the `[total]` functions whose totality is owed (`total`, `total_names`).
    Refused: a form not in OBL_FORMS, termination named; without `hand` (a consistency section
    written by hand that proves them), totality named, a held-named function (`Held`), a match
    independence named or an owed condition (`Owed`)."""
    with tempfile.TemporaryDirectory(prefix="tiegen-") as d:
        g = run([KCORE, "gen", path, d, "TieGenProbe", "--core"], cwd=KS)
        if g.returncode != 0:
            raise Refused(f"{name}: `kcore gen --core` fails: {(g.stdout + g.stderr).strip()[-400:]}")
        fh = open(os.path.join(d, "TieGenProbe/FnHyp.lean")).read()
        order = open(os.path.join(d, "TieGenProbe/FnHyp/Order.lean")).read()
        mods = {}
        for m in ("Term", "Total", "Agree", "Match", "Owed", "Held"):
            p = os.path.join(d, f"TieGenProbe/FnHyp/{m}.lean")
            mods[m] = open(p).read() if os.path.exists(p) else ""
    form = None
    for rx, kind, hform in OBL_FORMS:
        if re.search(rf"^abbrev Obl(?: \(H : HookParams\))? : Prop := {rx}$", fh, re.M):
            form = dict(kind=kind, hform=hform)
    if form is None and re.search(r"^theorem clausesPreTop_false : defn\.sem\.clausesPreTop = false", fh, re.M):
        if not hand:
            raise Refused(f"{name}: a clause's predicate is not \\top (`clausesPreTop_false`): `kcore gen --core` "
                          f"takes `FnHyp` itself as a hypothesis and states no `Obl`; the consistency section goes in "
                          f"--hand consistency")
        form = dict(kind="FnHyp", hform=False, prehyp=True)
    if form is None:
        m = re.search(r"^abbrev Obl.*$", fh, re.M)
        raise Refused(f"{name}: the obligations are in a form tiegen does not state ({m[0] if m else 'no Obl'})")
    form["held"] = bool(re.search(r"^abbrev Held\b", fh, re.M))
    hm = re.search(r"^theorem held_named : .*?=\s*(\[.*?\])", mods["Held"], re.M | re.S)
    form["held_names"] = re.findall(r"\d+ /- (.*?) -/", hm[1]) if hm else []
    if form["held"] and not hand:
        raise Refused(f"{name}: a held-named function (`kcore gen --core` states `Held`): its proof goes in "
                      f"--hand consistency")
    if re.search(r"^abbrev Owed\b", fh, re.M) and not hand:
        raise Refused(f"{name}: an owed condition (`kcore gen --core` states `Owed`): its proof goes in "
                      f"--hand consistency")
    lists = {k: named_list(mods[m], k) for k, m in (("term_named", "Term"), ("total_named", "Total"),
                                                   ("agree_named", "Agree"), ("match_named", "Match"))}
    if any(v is None for v in lists.values()):
        raise Refused(f"{name}: `kcore gen --core` states no list of {[k for k, v in lists.items() if v is None]}")
    others = [k for k in ("term_named",) + (() if hand else ("total_named", "match_named")) if lists[k]]
    if others:
        raise Refused(f"{name}: an owed fact other than an agreement ({', '.join(others)} not empty)"
                      + ("" if hand or not set(others) <= {"total_named", "match_named"}
                         else ": its proof goes in --hand consistency"))
    form["match"] = bool(lists["match_named"])
    form["total"] = lists["total_named"]
    tm = re.search(r"^theorem total_named : .*?=\s*(\[.*?\])", mods["Total"], re.M | re.S)
    form["total_names"] = re.findall(r"\d+ /- (.*?) -/", tm[1]) if tm else []
    form["agree"] = lists["agree_named"]
    am = re.search(r"^theorem agree_named : .*?=\s*(\[.*?\])", mods["Agree"], re.M | re.S)
    form["agree_names"] = re.findall(r"\d+ /- (.*?) -/", am[1]) if am else []
    form["owed"] = form["kind"] == "FnFacts" and (named_list(mods["Owed"], "owed_rules") != [] or
                                                  named_list(mods["Owed"], "owed_clauses") != [])
    if form.get("prehyp"):
        # `FnHyp` a hypothesis: the owed conditions are those the package's Owed module lists, if any
        form["owed"] = any(named_list(mods["Owed"], k) not in (None, []) for k in ("owed_rules", "owed_clauses"))
    if form["owed"] and not hand:
        raise Refused(f"{name}: a rule's or clause's condition is owed (owed_rules, owed_clauses): its proof goes "
                      f"in --hand consistency")
    co = re.search(r"def callOrder : List Nat := (\[[^\]]*\])", order)
    form["call_order"] = re.sub(r"/-.*?-/", "", co[1]).replace(" ", "")
    form["order_list"] = "[" + ", ".join(re.findall(r"\d+", form["call_order"])) + "]"
    return form


PROBE = r'''import KcoreSpec
open KCore ML Faithful KoreAML

def tgOrTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)
def tgRuleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none
def tgDropThird (p : Kore.Pattern) : Kore.Pattern :=
  match tgRuleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p
def tgRuleCompParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, .not _ n, x]) r => some (C, l, t, n, x, r)
  | _ => none
def tgMinusComp (p : Kore.Pattern) : P :=
  match tgRuleCompParts p with
  | some (C, l, t, _, _, r) =>
    let tb := tableOf [] p
    conjList (((freeOf [] p).eraseDups).map (guardOf tb)) ⇒
      (tr ⟨tb, []⟩ (.rewrites C (.and C [l, t]) r) ≡ inhOf (trSort tb C))
  | none => (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat
def tgVarRelB : List (EVar × EVar) → EVar → EVar → Bool
  | [], x, y => decide (x = y)
  | (a, b) :: env, x, y => if x = a then decide (y = b) else if y = b then false else tgVarRelB env x y
def tgAlphaB {𝕊 : Type} [DecidableEq 𝕊] : List (EVar × EVar) → Pattern 𝕊 → Pattern 𝕊 → Bool
  | env, .evar x, .evar y => tgVarRelB env x y
  | _, .svar X, .svar Y => decide (X = Y)
  | _, .bottom, .bottom => true
  | _, .symbol s, .symbol t => decide (s = t)
  | env, .application p q, .application p' q' => tgAlphaB env p p' && tgAlphaB env q q'
  | env, .implication p q, .implication p' q' => tgAlphaB env p p' && tgAlphaB env q q'
  | env, .existential x p, .existential y q => tgAlphaB ((x, y) :: env) p q
  | env, .mu X p, .mu Y q => decide (X = Y) && tgAlphaB env p q
  | _, _, _ => false
def tgGenLit : KCore.Gen → String
  | .ctor k => s!".ctor ⟨{k.name}, {k.args}, {k.result}⟩"
  | .inj a => s!".inj {a}"
def tgFreeEV {𝕊 : Type} : List EVar → Pattern 𝕊 → List EVar
  | bound, .evar x => if x ∈ bound then [] else [x]
  | _, .svar _ => []
  | _, .bottom => []
  | _, .symbol _ => []
  | bound, .application p q => tgFreeEV bound p ++ tgFreeEV bound q
  | bound, .implication p q => tgFreeEV bound p ++ tgFreeEV bound q
  | bound, .existential x p => tgFreeEV (x :: bound) p
  | bound, .mu _ p => tgFreeEV bound p
partial def tgPerms : List Nat → List (List Nat)
  | [] => [[]]
  | l => l.flatMap fun x => (tgPerms (l.erase x)).map (x :: ·)
def tgFnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none
def tgMinusNeg (a : Kore.Axiom) : P :=
  match TiePair.negParts a.pattern with
  | some (R, _, prem, concl) =>
    let t := tableOf a.sortVars a.pattern
    conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map (guardOf t)) ⇒
      (tr ⟨t, []⟩ (.implies R prem concl) ≡ inhOf (trSort t R))
  | none => (trAxiom [] [] ⟨0, "kernel", a⟩).pat
def tgNjBody : Kore.Pattern → Kore.Pattern
  | .exist _ _ b => tgNjBody b
  | p => p
/-- The generator a disjunct of a no-junk sentence applies: its symbol, or `inj` from its sort. -/
def tgNjIsGen (g : KoreAML.Gen) (d : Kore.Pattern) : Bool :=
  match g, tgNjBody d with
  | .ctor k, .app h _ _ => h.ident.name == k.name
  | .inj a, .app h (s0 :: _) _ => h.ident.name == "inj" && s0 == KoreAML.srt a
  | _, _ => false
/-- The positions in `gs` of the generators the disjuncts apply, in the disjuncts' order, the closing
`\bottom` dropped; none where a disjunct applies none of them. -/
def tgNjOrder (gs : List KoreAML.Gen) : List Kore.Pattern → Option (List Nat)
  | [] => some []
  | [.bottom _] => some []
  | d :: ds => do
    let j ← (List.range gs.length).find? fun j => (gs[j]?.map (tgNjIsGen · d)).getD false
    let rest ← tgNjOrder gs ds
    pure (j :: rest)

#eval show IO Unit from do
  let input ← IO.FS.readFile "@PATH@"
  let k ← match Kore.parseDefinition input with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"KORE read error {e}")
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"KCore's parse refuses it: {r.toText}")
  let c := d.sem
  let trS := fun (ad : AxiomDecl) => trAxiom k.symbolDecls k.aliasNames ad
  let fis := fnItems c
  let ks := kernelSyms c
  let ci := consItemsK c
  let has := fun (n : String) => ks.any (fun g => c.symName g.name == n)
  let gh := gammaHeads c
  let hasHead := fun (h : String × List Kore.KSort) => gh.any fun g => decide (g = h)
  let afs := c.allFns
  let css := c.ctorSigs
  let isFn := fun (n : String) => afs.any (c.symName ·.label == n)
  let isCtor := fun (n : String) => css.any (c.symName ·.name == n)
  let isHook := fun (n : String) => hookSigs.any (c.symName ·.name == n)
  let isImplParam := fun (n : String) => c.params.any fun k => c.symName k.sig.name == n && k.impl.isSome && !k.raw
  let isOvlN := fun (n : String) => c.ovlSigs.any (c.symName ·.name == n)
  let kind := fun (n : String) => if isFn n then "fn" else if isCtor n then "ctor" else if isHook n || isImplParam n then "hook" else if isOvlN n then "ovl" else if has n then "other" else "absent"
  let kg := (gensInOrder c d.pres Srt.kitem).map (Gen.toK c)
  let kitemPat := (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) kg).pat
  let tsig := (Theory.ofDefinition k).signature
  let sigFrom := fun (it : Item) => tsig.any (·.pat == it.pat) || surplusItem k it
  let hasSym := has
  let plainSyms := k.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
  let plainSorts := k.sortDecls.filter (·.params.isEmpty)
  let si := sigItems c
  let declItems := plainSorts.map sortConstantItem ++ plainSyms.map arityItem
  IO.println s!"H readsConfined {c.readsConfined}"
  IO.println s!"H plainSymNames {plainSyms.map (·.name)}"
  IO.println s!"H wf {wf d}"
  IO.println s!"H coreOK {c.coreOK}"
  IO.println s!"H attrsAgree {attrsAgree k d}"
  IO.println s!"H shapesOK {c.shapesOK}"
  IO.println s!"H rawParams {(c.params.filter (·.raw)).length}"
  IO.println s!"H nFnItems {fis.length}"
  IO.println s!"H nRuleItems {(ruleItems c).length}"
  IO.println s!"H nSig {si.length}"
  IO.println s!"H sigAll {si.all sigFrom}"
  IO.println s!"H sigBad {(si.zip (List.range si.length)).filter (!sigFrom ·.1) |>.map (·.2)}"
  let nextIt := (KoreAML.nextArityItem [] (srtOf c topCellSort)).pat
  IO.println s!"H sigBadNext {(si.filter (!sigFrom ·)).all (·.pat == nextIt)}"
  -- each item's origin (`--sig-positions`): its first position in the text's signature, else the
  -- registry sort or the hooked symbol of `hookSigs` whose surplus item it is (`surplusItem`'s
  -- disjuncts), else next's arity
  if @SIGPOS@ then
    for it in si do
      match tsig.findIdx? (·.pat == it.pat) with
      | some j => IO.println s!"SP t {j}"
      | none =>
        let rs := (List.range nRegSorts).find? fun s =>
          let n := "Sort" ++ regSortNames.getD s ""
          !(k.sortDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
            it.pat == (KoreAML.sortConstantItem ⟨n, [], false⟩).pat
        let hs := (List.range hookSigs.length).find? fun j => (hookSigs[j]?).any fun h =>
          let n := regSymNames.getD h.name ""
          !(k.symbolDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
            it.pat == (KoreAML.arityItem ⟨n, [], h.args.map regSrtK, regSrtK h.result, false, []⟩).pat
        match rs, hs with
        | some s, _ => IO.println s!"SP s {s}"
        | none, some j => IO.println s!"SP h {j}"
        | none, none => IO.println s!"SP {if it.pat == nextIt then "n" else "x"}"
  IO.println s!"H textNext {k.axiomDecls.any fun ad => !(nextSortsOf ad.ax.pattern).isEmpty}"
  IO.println s!"H nDecl {declItems.length}"
  IO.println s!"H declAll {declItems.all fun it => si.any (·.pat == it.pat)}"
  -- each declaration item's first position in Γ's signature (`--decl-positions`)
  if @DECLPOS@ then
    for it in declItems do
      IO.println s!"DP {(si.findIdx? (·.pat == it.pat)).map toString |>.getD "x"}"
  IO.println s!"H declCounts {k.sortDecls.length} {plainSorts.length} {k.symbolDecls.length} {plainSyms.length} {(k.symbolDecls.filter fun sd => !sd.params.isEmpty).length} {(k.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length}"
  IO.println s!"H kitemCons {decide (Srt.kitem ∈ consSorts c)} {(c.gens Srt.kitem).isEmpty}"
  IO.println s!"H kitemPerm {kg.isPerm ((c.gens Srt.kitem).map (Gen.toK c))} {decide ((c.gens Srt.kitem).map (Gen.toK c) ≠ kg)}"
  IO.println s!"H fnPrios {(afs.flatMap (fun f => f.clauses.map (·.prio)))}"
  let us := k.axiomDecls.filter (·.module == "@MOD@")
  let usP := us.map fun ad => let q := (trS ad).pat; (ad, q, (tgFreeEV [] q).eraseDups)
  let nmK := Parse.namesOf k
  let scK := match k.modules.getLast? with
    | some m => Parse.scan m.sentences
    | none => Parse.scan []
  let ixOf := fun (q : P) => (usP.filter fun (_, p, _) => p == q).map (·.1.index)
  IO.println s!"H hasParams {c.params.any (·.impl.isNone)}"
  IO.println s!"H totalParams {d.totalParams.map c.symName}"
  IO.println s!"H noImplParams {(c.params.filter fun p => p.impl.isNone && !p.raw).map (c.symName ·.sig.name)}"
  IO.println s!"H totalNil {decide (c.totalObligationsRP @ORDER@ [] = [])}"
  IO.println s!"H totalTp {decide (c.totalObligationsRP @ORDER@ d.totalParams = [])}"
  let tgTotV := ((c.params.find? fun k => d.totalParams.contains k.sig.name).bind fun k =>
    Parse.exhibit? c k.sig.result).getD default
  IO.println s!"H totalWit {ParamSchema.constTotal c d.totalParams tgTotV}"
  IO.println s!"H attrsParts {AttrsAgree.ctors k c} {AttrsAgree.fns k c} {AttrsAgree.hooks k c} {AttrsAgree.colls k c} {AttrsAgree.prios k d}"
  let lawIx := d.laws.map fun l => ixOf (lawPattern c l)
  IO.println s!"H lawIx {lawIx}"
  IO.println s!"H openLawIx {(lawItemsK c).map fun it => ixOf it.pat}"
  let lawGate := c.params.all (!·.raw) && c.ok && c.srReady && c.matchReady && c.clausesFixed &&
    c.agreeObligations.isEmpty
  let tgShow := fun (v : GroundTerm) => match v with
    | .dv _ (.int i) => toString i
    | .dv _ (.bool b) => toString b
    | .ctor f [] => c.symName f
    | v => reprStr v
  let tgCands := fun (s : Srt) =>
    ((([0, 1, 2, 3, -1, -2] : List Int).map fun i => GroundTerm.dv Srt.int (.int i)) ++
      [GroundTerm.dv Srt.bool (.bool true), GroundTerm.dv Srt.bool (.bool false)] ++
      (c.ctorSigs.filter (·.args.isEmpty)).map (fun g => GroundTerm.ctor g.name [])).filter (c.sortOf · == some s)
  for (l, j) in d.laws.zipIdx do
    let gate := lawGate && lawSorted c l
    let σs : List Subst := (l.vars.zipIdx.foldr (fun (s, i) acc =>
      (tgCands s).flatMap fun v => acc.map ((i, v) :: ·)) [[]]).take 4096
    let wit : Option (Subst × GroundTerm × GroundTerm) := if !gate then none else σs.findSome? fun σ =>
      if !Exec.wellSorted c l.vars σ then none else
      match Cert.evalTC c 4000 σ l.lhs, Cert.evalTC c 4000 σ l.rhs with
      | some (some v), some (some w) => if Exec.same v w then none else some (σ, v, w)
      | _, _ => none
    let ws := match wit with
      | some (σ, v, w) => s!"{", ".intercalate (σ.map fun (p : Nat × GroundTerm) => s!"var {p.1} = {tgShow p.2}")}\t{tgShow v}\t{tgShow w}"
      | none => "none"
    IO.println s!"L {j}\t{gate}\t{σs.length}\t{ws}"
  IO.println s!"H litBool {c.litSort Srt.bool}"
  IO.println s!"H owedNil {c.owedRules.isEmpty && c.owedClauses.isEmpty}"
  -- the conditions `LibEv.sortPredFun_evC` reads of the clauses, and the user sentences that are, as
  -- written, a sort predicate's `functional` sentence (`LibEv.funPat`, over the sort variable `R`)
  IO.println s!"H fnFunGate {c.clausesPreTop && (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) && (c.fns.all fun f => f.clauses.all fun cl => !cl.reqOpen)}"
  IO.println s!"H fnFunOK {(us.filter fun ad => decide (ad.ax.sortVars = [Rv]) && c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig).map (·.index)}"
  -- the clauses' conditions `LibEv.fnFun_evC` reads but the open-variable one, and the user
  -- sentences that are, as written, the `functional` sentence of a function of the text declared
  -- total (`LibEv.funPat`, over the sort variable `R`, `LibEv.predFunRegS`)
  IO.println s!"H fnFunPre {c.clausesPreTop && (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty)}"
  IO.println s!"H fnFunU {(us.filter fun ad => decide (ad.ax.sortVars = [Rv]) && c.fns.any fun fn => fn.total && decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunRegS c fn.sig).map (·.index)}"
  IO.println s!"H fnClauses {afs.map fun f => c.symName f.label ++ "=" ++ toString f.clauses.length}"
  -- Γ's heads in `gammaHeads`' order, each sort argument by its name (`?` for a sort that is no
  -- constructor without arguments), for `--heads-literal`
  for g in gh do
    IO.println s!"G {g.1}\t{"\t".intercalate (g.2.map fun s => match s with | .ctor h [] => h.ident.name | _ => "?")}"
  -- Γ's symbol names in `kernelSyms`' order (`--decl-syms-literal`) and the text's alias names
  -- (`--nojunk-eq`, `--nojunk-blocks`)
  for g in ks do
    IO.println s!"Y {c.symName g.name}"
  for a in k.aliasNames do
    IO.println s!"A {a}"
  -- KItem's name and generators, and the tables of its no-junk item and sentence, written out by
  -- `--nojunk-blocks`
  IO.println s!"H kitemName {c.sortName Srt.kitem}"
  for g in kg do
    match g with
    | .ctor k => IO.println s!"K C\t{k.name}\t{k.result}\t{"\t".intercalate k.args}"
    | .inj a => IO.println s!"K I\t{a}"
  let tgSortName := fun (s : Kore.KSort) => match s with | .ctor h [] => h.ident.name | _ => "?"
  let tgKey := fun (vk : VarKey) => match vk with
    | .sortVar n => s!"S\t{n}\t"
    | .evar n s => s!"E\t{n}\t{tgSortName s}"
    | .svar n s => s!"V\t{n}\t{tgSortName s}"
  for vk in tableOf [] (.or (srtOf c Srt.kitem) (KoreAML.noJunkDisjuncts (c.sortName Srt.kitem) [] kg)) do
    IO.println s!"TI {tgKey vk}"
  for kp in c.params.filter (·.raw) do
    IO.println s!"P {kp.sig.name}\t{c.symName kp.sig.name}\t{kp.sig.args}\t{kp.sig.result}\t{c.sortName kp.sig.result}\t{kp.assoc}\t{kp.idem}\t{c.isOpenGen (.ctor kp.sig)}"
  for (it, j) in fis.zip (List.range fis.length) do
    let fp := (tgFreeEV [] it.pat).eraseDups
    IO.println s!"F {j}\t{(usP.filter fun (_, q, fq) => tgAlphaB (fp.zip fq) it.pat q && tgAlphaB (fq.zip fp) q it.pat).map (·.1.index)}"
  -- the sentences of the text's other modules (the prelude: KSEQ, INJ) that are a function item as written
  for ad in k.axiomDecls.filter (·.module != "@MOD@") do
    let q := (trS ad).pat
    IO.println s!"Q {ad.index}\t{ad.module}\t{((fis.zip (List.range fis.length)).filter (fun (it, _) => it.pat == q)).map (·.2)}"
  let pairText := TiePair.fnTextOf c us
  let fax := tgFnAxioms c
  for (it, j) in fis.zip (List.range fis.length) do
    match pairText[j]?, fax[j]? with
    | some ad, some a =>
      let t := (trS ad).pat
      IO.println s!"W {j}\t{ad.index}\t{TiePair.sameB it.pat t}\t{(TiePair.negParts a.pattern).isSome}\t{TiePair.sameB (tgMinusNeg a) t}\t{decide (it.pat ≠ t)}\t{TieAlpha.acEqB it.pat t}"
    | _, _ => IO.println s!"W {j}\tnone\tfalse\tfalse\tfalse\tfalse\tfalse"
@READINGS@
  IO.println s!"H pairTextLen {pairText.length}"
  let njCands := ((consSorts c).filter fun s => s != Srt.kitem && !(c.gens s).isEmpty && (c.gens s).length ≤ 5).map fun s =>
    let gs := (c.gens s).map (Gen.toK c)
    (s, (KoreAML.Cons.noJunkItem (c.sortName s) ((gensInOrder c d.pres s).map (Gen.toK c))).pat,
      (tgPerms (List.range gs.length)).map fun pm => (pm, (KoreAML.Cons.noJunkItem (c.sortName s) (pm.filterMap (gs[·]?))).pat))
  for (r, j) in c.rules.zip (List.range c.rules.length) do
    let p := prioRuleK c r
    let comp := c.rules.any (·.prio < r.prio)
    let ok := if comp then (tgRuleCompParts p).isSome else (tgRuleParts p).isSome &&
      decide (tableOf [] p = tableOf [] (tgDropThird p)) &&
      decide ((freeOf [] p).eraseDups = (freeOf [] (tgDropThird p)).eraseDups)
    let tgt := if comp then tgMinusComp p else (trAxiom [] [] ⟨0, "kernel", ⟨[], tgDropThird p, []⟩⟩).pat
    let is := (usP.filter (fun (_, q, _) => q == tgt)).map (·.1.index)
    IO.println s!"R {j}\t{ok}\t{is}\t{comp}"
  for (ad, p, _) in usP do
    let absent := !(appHeadsOf ad.ax.pattern).all hasHead
    let fnJ := ((fis.zip (List.range fis.length)).filter (fun (it, _) => it.pat == p)).map (·.2)
    let cons := @CONS@ c ad.ax
    let plain := decide (p = (trAxiom [] [] ad).pat)
    let consItem := ci.any (·.pat == p)
    let triv := (k.sortDecls.filter fun sd => p == tgOrTopBot (sym (.sort sd.name))).map (·.name)
    let kitem := p == kitemPat
    let rw := AttrsAgree.isRewrite ad.ax.pattern
    let eh := (AttrsAgree.eqnHead ad.ax.pattern).getD ""
    let fh := match ad.ax.pattern with
      | .exist _ _ (.equals _ _ _ (.app h _ _)) => h.ident.name
      | _ => ""
    -- a user's equation of a symbol whose value the registry gives (`Parse.regLemmaEqn`): out of Γ,
    -- a parameter lemma where it applies a parameter symbol without `impl`, else at values
    let rl := (Parse.rawEqn? ad.ax).any (Parse.regLemmaEqn scK ·)
    -- a lemma of K's builtin library applying a parameter symbol without `impl` of the reading: the
    -- reader reads the library's text and Γ holds no item of the lemma (the class `library` is at
    -- values over symbols Γ interprets); the parameter's value is the interpretation's, so it is a
    -- parameter lemma as a user's is
    let lpl := Parse.isKBuiltin ad.ax.attributes && AttrsAgree.has ad.ax.attributes "simplification" &&
      appliesNoImplParam c ad.ax.pattern
    let pl := isParamLemma c (Parse.classify nmK (.axiom ad.ax)) (.axiom ad.ax) || (rl && appliesNoImplParam c ad.ax.pattern) || lpl
    let simp := Parse.classify nmK (.axiom ad.ax) == .inert .simplification
    let usrc := Parse.isUserSource ad.ax.attributes
    -- a lemma `--reads-h` names that applies a symbol through which evaluation may read the
    -- interpretation (`appliesHRead`), the condition on such an index; decided of those only
    let hr := (@READSH@ : List Nat).contains ad.index && appliesHRead c ad.ax.pattern
    -- an overload axiom Γ entails (`tieOvlEqB`), and a no-confusion sentence of two symbols that meet
    -- at values (`tieOvlNcB`), which Γ refutes; neither where the semantics has no overloading symbol
    let ovlEq := !c.ovls.isEmpty && tieOvlEqB c ad.ax
    let ovlNc := !c.ovls.isEmpty && !cons && tieOvlNcB c ad.ax
    -- KItem's no-junk sentence over its generators but the injections from sorts of the definition
    -- below KItem that its disjuncts do not name (`Parse.ReadingNote.tokKItem`), where `kitemOmitB`
    -- holds of those sorts and the generators it lists: the sorts, else none
    let omitX : List Srt := match ad.ax.pattern with
      | .or S ds =>
        let named := ds.filterMap Parse.tokKItemDisjunctSort?
        let xs := (c.gens Srt.kitem).filterMap fun g => match g with
          | .inj b => if named.contains (c.sortName b) then none else some b
          | .ctor _ => none
        let gs := kitemOmitGens c d.pres xs
        if S == srtOf c Srt.kitem && kitemOmitB c xs gs &&
            p == (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gs.map (Gen.toK c))).pat then xs else []
      | _ => []
    -- the `functional`, same-constructor and different-constructors sentences of a function-overloaded
    -- generator (`tieOvlFnFunB`, `tieOvlFnInjB`, `tieOvlFnDistB`); none where no overload is a function
    let ovlFn : String := if c.fnOvlSyms.isEmpty then "" else
      if tieOvlFnFunB c ad.ax then "fun" else if tieOvlFnInjB c ad.ax then "inj"
      else if tieOvlFnDistB c ad.ax then "dist" else ""
    IO.println s!"S {ad.index}\t{absent}\t{fnJ}\t{cons}\t{plain}\t{consItem}\t{triv}\t{kitem}\t{rw}\t{eh}\t{kind eh}\t{fh}\t{kind fh}\t{AttrsAgree.prioOf ad.ax.attributes}\t{pl}\t{simp}\t{usrc}\t{rl}\t{ovlEq}\t{ovlNc}\t{Parse.isOwnLibrarySentence (.axiom ad.ax)}\t{omitX}\t{hr}\t{ovlFn}"
    -- for such a sentence, each sort and generator (or pair) its predicate accepts it at, whether N is
    -- one of the semantics' sorts, and per generator: `tieOvlFnArityB`, the user sentences that are its
    -- `functional` sentence in the form `tieOvlFnFunShapeB` decides, and `Semantics.fnOvl`
    if ovlFn != "" then
      let gInfo := fun (N : Srt) (g : KCore.Gen) =>
        s!"{tgGenLit g}\t{tieOvlFnArityB c N g}\t{(us.filter fun af => tieOvlFnFunShapeB c N (Gen.toK c g) af.ax).map (·.index)}\t{c.fnOvl g}\t{match g with | .ctor k => c.symName k.name | .inj _ => "inj"}"
      for N in consSorts c do
        for g in c.gens N do
          if (ovlFn == "fun" && tieOvlFnFunAtB c N g ad.ax) || (ovlFn == "inj" && tieOvlFnInjAtB c N g ad.ax) then
            IO.println s!"OF {ad.index}\t{ovlFn}\t{N}\t{c.sortName N}\t{decide (N < nRegSorts + c.sortNames.length)}\t{gInfo N g}"
          if ovlFn == "dist" then
            for g' in c.gens N do
              if tieOvlFnDistAtB c N g g' ad.ax then
                IO.println s!"OF {ad.index}\t{ovlFn}\t{N}\t{c.sortName N}\t{decide (N < nRegSorts + c.sortNames.length)}\t{gInfo N g}\t{gInfo N g'}"
    for x in omitX do
      IO.println s!"KO {ad.index}\t{x}\t{c.sortName x}\t{(Parse.exhibit? c x).isSome}"
    if kitem then
      for vk in tableOf [] ad.ax.pattern do
        IO.println s!"TT {ad.index}\t{tgKey vk}"
    -- a sentence that is a constructor item and a `\or` at a sort with generators: the sort whose
    -- no-junk item over `Semantics.gens` it is (`--nojunk-eq`)
    if consItem then
      match ad.ax.pattern with
      | .or S _ =>
        for s in (consSorts c).filter fun s => !(c.gens s).isEmpty && srtOf c s == S do
          if (KoreAML.Cons.noJunkItem (c.sortName s) ((c.gens s).map (Gen.toK c))).pat == p then
            IO.println s!"J {ad.index}\t{s}\t{(c.gens s).length}"
      | _ => pure ()
    if !consItem && triv.isEmpty && !kitem then
      match njCands.find? (fun (_, o, _) => o == p) with
      | some (s, _, _) => IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\torder\t[]\t{(c.gens s).length}"
      | none =>
        for (s, _, pms) in njCands do
          match pms.find? (·.2 == p) with
          | some (pm, _) => IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\tperm\t{pm}\t{(c.gens s).length}"
          | none => pure ()
        -- a sort of more than 5 generators: the text's order (`gensInOrder`), or the order its
        -- disjuncts apply the generators in, taken where the item over it is the sentence
        match ad.ax.pattern with
        | .or S ds =>
          for s in (consSorts c).filter fun s => s != Srt.kitem && (c.gens s).length > 5 && srtOf c s == S do
            let gs := (c.gens s).map (Gen.toK c)
            if (KoreAML.Cons.noJunkItem (c.sortName s) ((gensInOrder c d.pres s).map (Gen.toK c))).pat == p then
              IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\torder\t[]\t{gs.length}"
            else match tgNjOrder gs ds with
              | some pm =>
                if pm.length == gs.length && pm.eraseDups.length == pm.length &&
                    (KoreAML.Cons.noJunkItem (c.sortName s) (pm.filterMap (gs[·]?))).pat == p then
                  IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\tperm\t{pm}\t{gs.length}"
              | none => pure ()
        | _ => pure ()
'''


# with --fn-readings: for each of Γ's equations, whether the text's sentence at its position (`TiePair.fnTextOf`) is
# Γ's item with an alternative beside its right side's first conjunct that holds nothing (`TieRhs.emptyAltOf`,
# `TieRhs.orEmptyOK`, the item mapped by `TieRhs.orEmptyIn` and `TiePair.sameB`); and, for each equation whose item
# is not its sentence, the cuts of its premise (`TieCutEq.Cut`: `andApp` at an argument path of at most four steps,
# `notCond`) at a place (`TieCutEq.Place`: `own`, or `under i n` for i < 4, n < 8) where the sentence is the item's
# text form up to the names of its variables (`TieCutEq.textItem`, `shapeOK`, `factsOK`, `TieAlpha.acEqB`: `WC` lines)
PROBE_READINGS = r'''  for j in List.range fis.length do
    match pairText[j]?, fax[j]? with
    | some ad, some a =>
      let t := (trS ad).pat
      let oe := match TieRhs.emptyAltOf ad.ax.pattern with
        | some (le, p) => TieRhs.orEmptyOK le p a &&
            TiePair.sameB (trAxiom [] [] ⟨0, "kernel", TieRhs.rhsMap (TieRhs.orEmptyIn le p) a⟩).pat t
        | none => false
      IO.println s!"WR {j}\t{oe}"
    | _, _ => pure ()
''' + r'''  for j in List.range fis.length do
    match pairText[j]?, fax[j]?, fis[j]? with
    | some ad, some a, some it =>
      let t := (trS ad).pat
      if it.pat != t then
        let ix := List.range 4
        let p1 := ix.map fun x => [x]
        let p2 := p1.flatMap fun p => ix.map fun x => p ++ [x]
        let p3 := p2.flatMap fun p => ix.map fun x => p ++ [x]
        let p4 := p3.flatMap fun p => ix.map fun x => p ++ [x]
        let cuts := TieCutEq.Cut.notCond :: (p1 ++ p2 ++ p3 ++ p4).map TieCutEq.Cut.andApp
        let pls := TieCutEq.Place.own :: ix.flatMap fun i => (List.range 8).map fun n => TieCutEq.Place.under i n
        let prem := match a.pattern with
          | .implies _ q _ => some q
          | _ => none
        for pl in pls do
          match prem.bind (TieCutEq.cutBody pl) with
          | some (_, body) =>
            for k in cuts do
              if (TieCutEq.textPrem k body).isSome then
                let ok := match TieCutEq.textItem k pl a with
                  | some g => TieCutEq.shapeOK k pl a && TieCutEq.factsOK c k pl a && TieAlpha.acEqB g t
                  | none => false
                if ok then
                  let ks := match k with
                    | .andApp p => s!"andApp\t{p}"
                    | .notCond => "notCond\t[]"
                  let ps := match pl with
                    | .own => "own"
                    | .under i n => s!"under\t{i}\t{n}"
                  IO.println s!"WC {j}\t{ks}\t{ps}"
          | none => pure ()
    | _, _, _ => pure ()'''


def probe(name, path, um, order="[]", cons_head=False, sig_pos=False, decl_pos=False, reads_h=(), readings=False):
    with tempfile.TemporaryDirectory(prefix="tiegen-") as d:
        f = os.path.join(d, "Probe.lean")
        open(f, "w").write(PROBE.replace("@PATH@", os.path.abspath(path)).replace("@MOD@", um)
                           .replace("@ORDER@", f"({order} : List Nat)")
                           .replace("@CONS@", "tchConsB" if cons_head else "tieConsB")
                           .replace("@SIGPOS@", "true" if sig_pos else "false")
                           .replace("@DECLPOS@", "true" if decl_pos else "false")
                           .replace("@READSH@", "[" + ", ".join(map(str, reads_h)) + "]")
                           .replace("@READINGS@", PROBE_READINGS if readings else ""))
        env = dict(os.environ, LEAN_NUM_THREADS="1")
        r = run(WRAP + ["timeout", os.environ.get("TIEGEN_PROBE_TIMEOUT", "900"), "lake", "env", "lean", "-j1", f], cwd=KS, env=env)
    if r.returncode != 0:
        raise Refused(f"{name}: the probe fails: {(r.stdout + r.stderr).strip()[-600:]}")
    head, sents = {}, {}
    head["rules"], head["raw"], head["fnA"], head["nj"], head["lawRef"], head["fnW"] = [], [], {}, {}, [], {}
    head["fnQ"] = {}
    head["gHeads"] = []
    head["gSyms"], head["aliases"], head["njEq"] = [], [], {}
    head["kGens"], head["tabI"], head["tabT"] = [], [], {}
    nums = lambda s: [int(x) for x in re.findall(r"\d+", s)]
    for l in r.stdout.split("\n"):
        if l.startswith("G "):
            f = l[2:].split("\t")
            head["gHeads"].append((f[0], [x for x in f[1:] if x]))
        elif l.startswith("Y "):
            head["gSyms"].append(l[2:])
        elif l.startswith("DP "):
            f = l[3:].strip()
            head.setdefault("declPos", []).append(int(f) if f.isdigit() else None)
        elif l.startswith("SP "):
            f = l[3:].split()
            head.setdefault("sigPos", []).append((f[0], int(f[1]) if len(f) > 1 else None))
        elif l.startswith("A "):
            head["aliases"].append(l[2:])
        elif l.startswith("K "):
            f = l[2:].split("\t")
            head["kGens"].append(("ctor", f[1], f[2], [x for x in f[3:] if x]) if f[0] == "C" else ("inj", f[1]))
        elif l.startswith("TI "):
            head["tabI"].append(tuple(l[3:].split("\t")))
        elif l.startswith("TT "):
            f = l[3:].split("\t")
            head["tabT"].setdefault(int(f[0]), []).append(tuple(f[1:]))
        elif l.startswith("J "):
            f = l[2:].split("\t")
            head["njEq"].setdefault(int(f[0]), []).append((int(f[1]), int(f[2])))
        elif l.startswith("H "):
            k, _, v = l[2:].partition(" ")
            head[k] = v
        elif l.startswith("L "):
            f = l[2:].split("\t")
            head["lawRef"].append(dict(j=int(f[0]), searched=f[1] == "true", tried=int(f[2]),
                                       wit=None if f[3] == "none" else dict(sigma=f[3], lhs=f[4], rhs=f[5])))
        elif l.startswith("R "):
            f = l[2:].split("\t")
            head["rules"].append((int(f[0]), f[1] == "true", [int(x) for x in re.findall(r"\d+", f[2])]))
            if f[3:4] == ["true"]:
                head.setdefault("ruleComp", set()).add(int(f[0]))
        elif l.startswith("P "):
            f = l[2:].split("\t")
            head["raw"].append(dict(sym=int(f[0]), name=f[1], args=nums(f[2]), res=int(f[3]), sort=f[4],
                                    assoc=f[5], idem=f[6], openGen=f[7] == "true"))
        elif l.startswith("F "):
            f = l[2:].split("\t")
            head["fnA"][int(f[0])] = nums(f[1])
        elif l.startswith("Q "):
            f = l[2:].split("\t")
            head["fnQ"][int(f[0])] = (f[1], nums(f[2]))
        elif l.startswith("WR "):
            f = l[3:].split("\t")
            head.setdefault("fnRd", {})[int(f[0])] = dict(orEmpty=f[1] == "true")
        elif l.startswith("WC "):
            f = l[3:].split("\t")
            head.setdefault("fnCut", {}).setdefault(int(f[0]), dict(
                kind=f[1], path=[int(x) for x in re.findall(r"\d+", f[2])],
                place=("own",) if f[3] == "own" else ("under", int(f[4]), int(f[5]))))
        elif l.startswith("W "):
            f = l[2:].split("\t")
            head["fnW"][int(f[0])] = dict(idx=None if f[1] == "none" else int(f[1]), same=f[2] == "true",
                                          narrowed=f[3] == "true", wtext=f[4] == "true", differs=f[5] == "true",
                                          ac=f[6:7] == ["true"])
        elif l.startswith("N "):
            f = l[2:].split("\t")
            head["nj"].setdefault(int(f[0]), []).append(dict(srt=int(f[1]), sort=f[2], form=f[3], perm=nums(f[4]),
                                                             ngens=int(f[5])))
        elif l.startswith("S "):
            f = l[2:].split("\t")
            nums = lambda s: [int(x) for x in re.findall(r"\d+", s)]
            sents[int(f[0])] = dict(idx=int(f[0]), absent=f[1] == "true", fnJ=nums(f[2]), cons=f[3] == "true", plain=f[4] == "true",
                                    consItem=f[5] == "true", triv=re.findall(r"Sort[^,\]\s]+", f[6]),
                                    kitem=f[7] == "true", rw=f[8] == "true", eh=f[9], ehk=f[10], fh=f[11],
                                    fhk=f[12], prio=int(f[13]), pl=f[14] == "true",
                                    simp=f[15] == "true", usrc=f[16] == "true", rl=f[17] == "true",
                                    ovlEq=f[18] == "true", ovlNc=f[19] == "true", own=f[20:21] == ["true"],
                                    omit=nums(f[21]) if len(f) > 21 else [],
                                    hr=f[22:23] == ["true"], ovlFn=f[23] if len(f) > 23 else "")
        elif l.startswith("OF "):
            f = l[3:].split("\t")
            gi = lambda k: dict(lit=f[k], arity=f[k + 1] == "true", fun=nums(f[k + 2]), fnOvl=f[k + 3] == "true",
                                sym=f[k + 4])
            head.setdefault("ovlFn", {}).setdefault(int(f[0]), []).append(
                dict(kind=f[1], srt=int(f[2]), sort=f[3], numbered=f[4] == "true",
                     gens=[gi(5)] + ([gi(10)] if len(f) > 10 else [])))
        elif l.startswith("KO "):
            f = l[3:].split("\t")
            head.setdefault("omit", {}).setdefault(int(f[0]), []).append(
                dict(srt=int(f[1]), sort=f[2], valued=f[3] == "true"))
    return head, sents


# ---------------------------------------------------------------------------------------------
# Classes

def builtin_symbol_decls(text):
    """The names of the text's symbol declarations (`symbol`, not `hooked-symbol`) with a K builtin
    file's `Source`, without a `hook` attribute and without sort parameters, in text order."""
    out, cur = [], None
    for l in text.split("\n") + ["endmodule"]:
        if l.lstrip().startswith("//"):
            continue
        if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|claim|alias|import|axiom)\b", l) or \
                l.startswith("endmodule") or l.startswith("module "):
            if cur:
                out.append(cur)
            cur = l.strip() if re.match(r"\s+symbol ", l) else None
        elif cur:
            cur += "\n" + l
    names = []
    for s in out:
        m = re.match(r"symbol (\S+?)\{([^}]*)\}", s)
        if (m and not m.group(2).strip() and "/include/kframework/builtin/" in s
                and not re.search(r'(?<![-\w])hook\{\}\("', s)):
            names.append(m.group(1))
    return names


def form_class(s, raw, builtin, laws=(), open_laws=(), raw_names=(), at_values=(), total_params=(), reads_h=()):
    """The class a sentence's form and its probe give, or None. `laws`: the sentences that are, as
    written, the reader's laws of functions (`lawPattern`); `open_laws`: those that are Γ's law
    items of open generators (`lawItemsK`); `raw_names`: the open generators' symbol names;
    `at_values`: the user lemmas the caller names as holding at values only; `total_params`: the
    names of the parameter symbols without `impl` that the text declares total
    (`Definition.totalParams`); `reads_h`: the user lemmas the caller names as reading a value the
    interpretation gives (the class parameter lemma)."""
    # a sentence applying a head Γ lacks: no item of Γ states anything of that head and H gives it
    # no value, so no class with a direction holds it. The class is not what the text owes: where
    # eliminating the head fixes a value of a symbol of Γ (findChar's equation, domains.md 1891,
    # applying `ite{SortInt}`: the condition `Semantics.findCharEq` on H), that is owed apart.
    if s["absent"]:
        return "no direction"
    if s["ovlEq"]:
        return OVL_EQ_CLASS
    if s["ovlNc"]:
        return OVL_NC
    if s.get("omit"):
        return TOK_OMIT
    # before the `// functional` and `// no confusion` arms, which would class such a sentence by its
    # comment: Γ holds it at uncovered arguments only
    if s.get("ovlFn"):
        return OVL_FN
    if s["idx"] in laws:
        return LAW_FN_CLASS
    if s["idx"] in open_laws:
        return LAW_OPEN_CLASS
    if "[functional{}()]" in raw and s["fh"] in raw_names and not s["fnJ"] and not s["consItem"]:
        return OPEN_FUNCTIONAL_CLASS
    if "[functional{}()]" in raw and s["fh"] in total_params and not s["fnJ"] and not s["consItem"]:
        return PARAM_FUNCTIONAL_CLASS
    if s["fnJ"]:
        return "function equation"
    if s["rw"]:
        return "rewrite rule"
    if s["pl"]:
        return PARAM_LEMMA_CLASS
    # a lemma of a user's file (the reader's inert simplification, a `Source` outside K's
    # installation), whatever its form: with a set variable it is no library lemma
    if s["simp"] and s["usrc"] and not builtin:
        if s["idx"] in reads_h:
            return PARAM_LEMMA_CLASS
        return USER_LEMMA_VALUES_CLASS if s["idx"] in at_values else USER_LEMMA_CLASS
    # a user's equation of a symbol whose value the registry gives (`Parse.regLemmaEqn`), applying no
    # parameter symbol without `impl`: it rests on an interpreted symbol's graph, at values
    if s["rl"] and not builtin:
        return USER_LEMMA_VALUES_CLASS
    if s["triv"] or s["consItem"] or s["kitem"] or "// no junk" in raw:
        return "no junk"
    if "[subsort{" in raw:
        return "subsort"
    if "// no confusion same constructor" in raw:
        return "injectivity"
    if "// no confusion different constructors" in raw:
        return "distinctness"
    # an overloading symbol is a generator of its result sort (`Semantics.gens`); where it overloads
    # no function, Γ holds its Cons-Fun item at every argument list (`consItemsK`), so its functional
    # sentence is that item where `tieConsB` accepts it. Where it overloads a function (`fnOvl`), Γ
    # holds the item at uncovered arguments only, and the sentence has no class here.
    if "[functional{}()]" in raw and s["fh"] and s["fhk"] == "ovl":
        return "constructor functional" if s["cons"] else None
    if "[functional{}()]" in raw and s["fh"]:
        return {"ctor": "constructor functional", "fn": "function functional", "hook": "hooked functional"}.get(s["fhk"])
    # an equation whose item is the sentence with the premise that the clauses of a smaller priority
    # do not apply (`narrowW`, from the probe) is a priority equation whatever its priority: one of
    # priority 50, written or not, beside a clause of a smaller priority is narrowed as well (a
    # sentence with an ens counterpart takes ens's class, `classify`)
    # an equation of a function of Γ whose sentence the reader reads as the definition's own (a K
    # builtin file's sentence about names no library text declares, `Parse.isOwnLibrarySentence`) is
    # classed as a user's is: the reader reads it as the definition's own clause
    if s["ehk"] == "fn" and (not builtin or s.get("own")):
        return "priority equation" if (s["prio"] != 50 and s["prio"] != 200) or s.get("narrowW") else "function equation"
    if "[idem{}()]" in raw:
        return "set idempotence"
    if "[assoc{}()]" in raw or "[unit{}()]" in raw:
        return "collection law"
    if re.search(r"@Var\w*:", raw) and "simplification{}" in raw:
        return "set-variable lemma"
    if builtin:
        return "library"
    return None


def classify(name, text, sents, laws=(), open_laws=(), raw_names=(), at_values=(), total_params=(), no_impl=(),
             reads_h=()):
    um, ua = user_axioms(text)
    both = sorted(set(at_values) & set(reads_h))
    if both:
        raise Refused(f"{name}: --at-values and --reads-h both name {', '.join(map(str, both))}: a lemma is of one class")
    if sorted(sents) != [a[0] for a in ua]:
        raise Refused(f"{name}: the probe's user-module sentences are not the text's (indices differ)")
    _, ea = user_axioms(open(ENS_TEXT).read())
    ecls = ens_classes()
    pool = {}
    for i, _, s, _ in ea:
        pool.setdefault(s, []).append(i)
    cls, mapped, unmapped = {}, {}, []
    for i, _, s, raw in ua:
        builtin = "/include/kframework/builtin/" in raw
        fc = form_class(sents[i], raw, builtin, laws, open_laws, raw_names, at_values, total_params, reads_h)
        # the functional sentence of a parameter without `impl` that the text does not declare total
        # has no class: the reader reads such a sentence only as the declaration (`totalParams`)
        if ("[functional{}()]" in raw and sents[i]["fh"] in no_impl and sents[i]["fh"] not in total_params
                and not sents[i]["absent"]):
            raise Refused(f"{name}: sentence {i} is the functional sentence of the parameter {sents[i]['fh']}, "
                          f"which the text does not declare total (`Definition.totalParams`)")
        # whether a sentence applies a head Γ lacks is a fact of this text's Γ: a sentence equal to one
        # of ens's that is in the no-direction class in one text and not in the other takes no class
        # from ens's and is unmapped
        if pool.get(s) and (ecls[pool[s][0]] == "no direction") == sents[i]["absent"]:
            j = pool[s].pop(0)
            mapped[i] = j
            # a lemma over a parameter symbol of this text's reading without `impl` is a parameter
            # lemma whatever ens's class of the same sentence (the parameters are the text's), and a
            # lemma of a user's file is a user lemma (the `Source` is this text's), and the functional
            # sentence of a parameter this text declares total is a parameter functional
            ec = fc if fc in (PARAM_LEMMA_CLASS, PARAM_FUNCTIONAL_CLASS, OVL_EQ_CLASS, OVL_NC, TOK_OMIT, OVL_FN) or fc in USER_LEMMA_CLASSES else ecls[j]
            # where the probe decides the class (a head Γ lacks, an item of Γ), it must agree with ens's
            decided = fc if fc in ("no direction", "function equation", "rewrite rule") or (fc == "no junk" and ec == "no junk") else None
            if decided and decided != ec:
                raise Refused(f"{name}: sentence {i} is ens's {j} (class {ec}), but the probe gives {decided}")
            cls[i] = ec
        else:
            if fc is None:
                raise Refused(f"{name}: sentence {i} has no ens counterpart and neither its form nor the probe gives its class: {raw[:200]}")
            cls[i] = fc
            unmapped.append(i)
    stray = sorted(i for i in at_values if cls.get(i) != USER_LEMMA_VALUES_CLASS)
    if stray:
        raise Refused(f"{name}: --at-values names {', '.join(map(str, stray))}, no user lemma of the text "
                      f"(a sentence of a user's file that the reader classes inert simplification and that "
                      f"applies no parameter symbol without `impl`)")
    builtin_of = {i: "/include/kframework/builtin/" in raw for i, _, _, raw in ua}
    no_lemma = sorted(i for i in reads_h if i not in sents or cls.get(i) != PARAM_LEMMA_CLASS or sents[i]["pl"]
                      or not (sents[i]["simp"] and sents[i]["usrc"]) or builtin_of.get(i, True))
    if no_lemma:
        raise Refused(f"{name}: --reads-h names {', '.join(map(str, no_lemma))}, no user lemma of the text "
                      f"(a sentence of a user's file that the reader classes inert simplification and that "
                      f"applies no parameter symbol without `impl`; one that applies one is a parameter lemma by "
                      f"its shape)")
    no_read = sorted(i for i in reads_h if not sents[i]["hr"])
    if no_read:
        raise Refused(f"{name}: --reads-h names {', '.join(map(str, no_read))}, whose sentence applies no symbol "
                      f"through which evaluation may read the interpretation (`appliesHRead` fails): its truth at "
                      f"values reads nothing H gives, so it is no hypothesis on H")
    return um, cls, mapped, unmapped


# ---------------------------------------------------------------------------------------------
# The Lean text

def wrap_nums(nums, indent, width=100):
    lines, cur = [], ""
    for n in nums:
        piece = f"{n}, "
        if len(cur) + len(piece) + indent > width:
            lines.append(cur.rstrip())
            cur = ""
        cur += piece
    lines.append(cur.rstrip().rstrip(","))
    return ("\n" + " " * indent).join(lines)


def lean_str(x):
    """`x` as a Lean string literal."""
    return '"' + x.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def head_lit(h):
    """A head of `gammaHeads` (a name and its sort arguments' names) as a Lean literal."""
    return "(" + lean_str(h[0]) + ", [" + ", ".join(f".ctor ⟨⟨{lean_str(s)}⟩⟩ []" for s in h[1]) + "])"


def str_code(name):
    """The name as `KoreAML.Distinct.strCode` codes it: its UTF-8 bytes in base 256, the first byte
    the lowest digit, behind a leading 1."""
    code = 1
    for b in reversed(name.encode("utf-8")):
        code = code * 256 + b
    return code


def head_code_lit(h):
    """A head of `gammaHeads` with its name as `KoreAML.Distinct.strCode` codes it, as a Lean literal."""
    return f"({str_code(h[0])}, [" + ", ".join(f".ctor ⟨⟨{lean_str(s)}⟩⟩ []" for s in h[1]) + "])"


def ax_list(nums, indent=3, pre=None):
    """The literals of the axioms `nums`: `U.axN`, or `pre[N].axN` for an axiom of a prelude module."""
    pre = pre or {}
    return "[" + wrap_nums([f"{pre.get(n, 'U')}.ax{n}" for n in nums], indent) + "]"


def ranges(n, first, chunk):
    """[(a, len)] covering 0..n: one block of `first`, then blocks of `chunk`, the last open."""
    out, a = [], 0
    if first and first < n:
        out.append((a, first))
        a = first
    while a + chunk < n:
        out.append((a, chunk))
        a += chunk
    out.append((a, None))
    return out


def pos_join(name, pty, at_p, pred, sound):
    """The lemma `name`: `pred` holds of each item of a list where `at_p` holds of each item paired
    with its position (of type `pty`) in a list at least as long, from `sound`, which gives `pred` of
    an item from `at_p` of it with any position (`--sig-positions`, `--decl-positions`)."""
    return "\n".join([
        f"theorem {name} {{l : List Item}} {{ps : List {pty}}} (hl : l.length ≤ ps.length)",
        f"    (h : (l.zip ps).all {at_p} = true) : l.all {pred} = true := by",
        "  induction l generalizing ps with",
        "  | nil => rfl",
        "  | cons it l ih =>",
        "    cases ps with",
        "    | nil => exact absurd hl (by simp)",
        "    | cons p ps =>",
        "      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢",
        f"      exact ⟨{sound} h.1, ih (by simpa using hl) h.2⟩"])


def by_ranges(prefix, lst, pred, rs, lem="tieAllE", named=False):
    """The range theorems of `{lst}.all {pred} = true` over `rs`, each its own kernel decision, and
    the term that joins them. `named`: the join names the list and the predicate at every step, so
    each step's statement is fixed before its argument is elaborated, and the predicate's binder
    has the list's member type; the join is then instantiation and the `a + n` of `tieAll_range`
    against the next range's literal start, with nothing of the list or the predicate reduced."""
    thms, chain = [], []
    for a, ln in rs:
        if ln is None:
            thms.append(f"theorem {prefix}_{a} : (({lst}).drop {a}).all {pred} = true := by decide +kernel")
        else:
            thms.append(f"theorem {prefix}_{a} : ((({lst}).drop {a}).take {ln}).all {pred} = true := by decide +kernel")
    lp = f"(l := {lst}) (p := {pred}) " if named else ""
    body = f"{lem}_whole {lp or f'(p := {pred}) '}<|\n"
    for a, ln in rs[:-1]:
        body += f"    {lem}_range {lp}(a := {a}) (n := {ln}) {prefix}_{a} <|\n"
    body += f"    {prefix}_{rs[-1][0]}"
    return "\n".join(thms), body


def generate(name, text_rel, um, cls, mapped, unmapped, sents, head, wf_ok, failing, ob, chunks, raws=None,
             hand=None, chunk=0, at_values=(), cons_head=False, wf_parts=None, split=False,
             account_sorted=None, heads_literal=False, heads_codes=False, attrs_parts=False, decl_parts=False,
             fn_blocks=0, attrs_blocks=0, absent_file=False, builtin_decls=(), decl_syms=False, nojunk_eq=False,
             nojunk_blocks=0, lists_by_class=False, heads_plain=False, sig_pos=False, fnfun_chunk=0,
             decl_pos=False, reads_h=(), fn_readings=False):
    """The Lean text of the tie. `ob`: what `obligations` read; `raws`: each sentence's text as
    written; `hand`: hand-written sections by name (`consistency`), each in place of the generated
    one; `chunk`: the length of the ranges the decisions over the whole user module are cut into
    (0: one decision each); `account_sorted`: `(a, n)` where the user module's indices, in text
    order, are `a, ..., a+n-1`, to prove the account from the sorted class lists; `heads_literal`:
    decide `account_absent`'s ranges on Γ's heads as a literal (`gHeads`); `heads_codes`: and on
    their names' codes (`gCodes`); `attrs_parts`, `decl_parts`: `attrs_agree` and `decl_counts` from
    one decision per conjunct or component; `fn_blocks`: decide `fn_shape` by blocks of that many
    equations (0: one decision); `decl_syms`: decide `decl_counts` and the `declsE` ranges on Γ's
    symbol names as a literal (`gSymCodes`); `nojunk_eq`: `nojunk_items` from each sentence's
    equation to its sort's item (`njEq`); `nojunk_blocks`: the no-junk orders of KItem and of a sort
    of more generators than that by blocks of that many disjuncts (0: one decision); `lists_by_class`:
    `lists_in_account` from one check per class (`tieAll_of_groups`); `heads_plain`: decide
    `account_absent`'s ranges on the codes of Γ's symbol names and subsort pairs (`gSymCodes`,
    `gInjCodes`, `hasHeadCoded`, by `gammaHasHead_coded`), in place of `gHeads`/`gCodes`, and
    `absent_proj_below`'s first conjunct by the same ranges (`absProjE_a`, `tieFilterMap_range`); `decl_pos`:
    the `declsE` ranges on each declaration item's position in `sigItems c` (`declPos`, `inSigItemsAt`);
    `reads_h`: the parameter lemmas named by `--reads-h` (`paramlemma_reads_h`); `fn_readings`: tie the
    function equations whose sentence is Γ's item by a reading (`readings_section`), the others one by
    one, where `fn_pairs` does not apply."""
    raws = raws or {}
    hand = hand or {}
    call_order = ob["call_order"]
    ns = "Tie" + camel(name)
    idx = sorted(cls)
    # a sentence of an overloading symbol: the account's classes in `tieClassesOvl`'s order (the class
    # overload equation before no direction), and the refuted no-confusion sentences apart
    ovl_eq = [i for i in idx if cls[i] == OVL_EQ_CLASS]
    ovl_nc = [i for i in idx if cls[i] == OVL_NC]
    ovl_any = bool(ovl_eq or ovl_nc)
    classes_list = CLASSES[:-1] + [OVL_EQ_CLASS, CLASSES[-1]] if ovl_any else CLASSES
    # KItem's no-junk sentence that leaves out sorts below KItem: in no class, listed apart
    tok_omit = [i for i in idx if cls[i] == TOK_OMIT]
    if len(tok_omit) > 1:
        raise Refused(f"{name}: sentences {', '.join(map(str, tok_omit))} are KItem no-junk sentences that leave out "
                      f"sorts below KItem: one is stated (`tokKItemSorts`)")
    tok_sorts = head.get("omit", {}).get(tok_omit[0], []) if tok_omit else []
    if tok_omit and [e["srt"] for e in tok_sorts] != sents[tok_omit[0]]["omit"]:
        raise Refused(f"{name}: the probe's left-out sorts of sentence {tok_omit[0]} are not listed one per line")
    # the sentences of a function-overloaded generator: in no class, listed apart (`ovlFnApart`), part 1
    # generated, part 2 by hand
    ovl_fn = [i for i in idx if cls[i] == OVL_FN]
    if "ovlfn" in hand and not ovl_fn:
        raise Refused(f"{name}: --hand ovlfn: the text states no sentence of a function-overloaded symbol")
    ovl_fn_rows, ovl_fn_gens = ovl_fn_rows_of(name, ovl_fn, head, sents) if ovl_fn else ({}, [])
    ovl_fn_hand = ovl_fn_hand_of(name, ovl_fn, hand.get("ovlfn")) if ovl_fn else {}
    unmapped = [i for i in unmapped if cls[i] not in (OVL_NC, TOK_OMIT, OVL_FN)]
    by_class = {c: [i for i in idx if cls[i] == c] for c in classes_list}
    # the no-direction sentences that are equations of a projection (`AttrsAgree.eqnHead`), each with
    # the projection's sort X
    abs_proj = [(i, sents[i]["eh"][len(PROJ_PREFIX):]) for i in by_class["no direction"]
                if sents[i]["eh"].startswith(PROJ_PREFIX) and len(sents[i]["eh"]) > len(PROJ_PREFIX)]
    nfn = int(head["nFnItems"])
    nrules = int(head["nRuleItems"])
    # function equations, in fnItems' order
    fn_order = {}
    for i in by_class["function equation"]:
        for j in sents[i]["fnJ"]:
            fn_order.setdefault(j, []).append(i)
    fn_full = (sorted(fn_order) == list(range(nfn)) and all(len(v) == 1 for v in fn_order.values())
               and sorted(v[0] for v in fn_order.values()) == by_class["function equation"])
    # otherwise the items no user sentence is may each be, as written, one sentence of the text's
    # prelude modules (KSEQ's `append`, which Γ holds where a rule or an equation applies it): every
    # other item one user sentence's, each function equation of the user module one item's
    fn_pre = {}
    if not fn_full and nfn and all(len(v) == 1 for v in fn_order.values()) and \
            sorted(v[0] for v in fn_order.values()) == by_class["function equation"]:
        rest = [j for j in range(nfn) if j not in fn_order]
        pre = {j: [i for i, (_, js) in head["fnQ"].items() if j in js] for j in rest}
        if all(len(v) == 1 for v in pre.values()) and len({v[0] for v in pre.values()}) == len(rest):
            fn_order.update(pre)
            fn_full = True
            fn_pre = {v[0]: head["fnQ"][v[0]][0] for v in pre.values()}
    fn_text = [fn_order[j][0] for j in range(nfn)] if fn_full else []
    # each prelude module of such a sentence, with the name of its axioms' literals (`user_axioms`)
    pre_mods = {m: "Prelude" + re.sub(r"[^A-Za-z0-9]", "", camel(m.lower())) for m in sorted(set(fn_pre.values()))}
    fn_user = [i for i in fn_text if i not in fn_pre]
    # otherwise each item may be its sentence up to a renaming of element variables (`alphaB`): an
    # `[owise]` equation's exclusion names its own bound variable
    fn_align, fn_nonlit = False, []
    if not fn_full and nfn:
        cand = [head["fnA"].get(j, []) for j in range(nfn)]
        if all(len(v) == 1 for v in cand) and sorted(v[0] for v in cand) == by_class["function equation"]:
            txt = [v[0] for v in cand]
            nonlit = [j for j in range(nfn) if j not in sents[txt[j]]["fnJ"]]
            if nonlit and all("owise{}()" in raws.get(txt[j], "") for j in nonlit):
                fn_align, fn_text, fn_nonlit = True, txt, nonlit
    if fn_blocks and not fn_full:
        raise Refused(f"{name}: --fn-blocks: the tie states no `fn_shape` (Γ's equations are not the text's "
                      f"sentences one for one" + (", but up to a renaming: `fn_shape_but_owise`)" if fn_align else ")"))
    raw = head["raw"]
    law_idx = [l[0] for l in nested(head["lawIx"])]
    open_law = [l[0] for l in nested(head["openLawIx"])]
    confined = head["readsConfined"] == "true"
    # otherwise each item may be its sentence's translation up to a renaming of one free variable
    # (`TiePair.sameB`) but one, a priority equation's: Γ's item is its sentence with the premise
    # that the clauses of a smaller priority that are not `aside` do not apply (`prioEquation`), and
    # without that premise it is the sentence (`TiePair.minusNeg`), which entails it (W1)
    fn_pair, pair_text, pair_w = False, [], None
    fn_pairs, pair_ws, pair_ac = False, [], []
    fn_rds, pair_rd, pair_un, pair_cut = False, [], [], []
    fw = head["fnW"]
    if not fn_full and not fn_align and nfn and (not confined or fn_readings) and not raw and \
            sorted(fw) == list(range(nfn)) and int(head.get("pairTextLen", -1)) == nfn and \
            all(fw[j]["idx"] is not None for j in range(nfn)):
        txt = [fw[j]["idx"] for j in range(nfn)]
        ws = [j for j in range(nfn) if not fw[j]["same"]]
        fn_prio_list = [int(x) for x in re.findall(r"\d+", head["fnPrios"])]
        w1_ok = lambda j: fw[j]["narrowed"] and fw[j]["wtext"] and fw[j]["differs"]
        ac_ok = lambda j: fw[j]["ac"] and fw[j]["differs"]
        common = sorted(txt) == sorted(by_class["function equation"] + by_class["priority equation"]) and \
            len(set(txt)) == nfn and [sents[i]["prio"] for i in txt] == fn_prio_list
        if len(ws) == 1 and w1_ok(ws[0]) and common and not confined:
            fn_pair, pair_text, pair_w = True, txt, ws[0]
        # several such items, or an item that is its sentence up to the order of the operands of its
        # sorted disjunctions and the names of its variables (`TieAlpha.acEqB`: an `[owise]`
        # equation's exclusion, which the text writes in another order with other bound variables)
        elif ws and common and all(ac_ok(j) or w1_ok(j) for j in ws) and not confined:
            fn_pairs, pair_text = True, txt
            pair_ac = [j for j in ws if ac_ok(j)]
            pair_ws = [j for j in ws if not ac_ok(j)]
        # with --fn-readings, also an item whose sentence writes an alternative beside its right side's
        # first conjunct that holds nothing (`TieRhs.orEmptyOK`, `orBottom`'s `dropEmptyAlts`), each item
        # tied by its own theorem, and an item no reading here ties left uncovered with its sentence,
        # the others tied as written (`readings_section`); a text that reads a confined sort too
        elif fn_readings and ws and common:
            rd_ok = lambda j: head.get("fnRd", {}).get(j, {}).get("orEmpty", False) and fw[j]["differs"]
            fn_rds, pair_text = True, txt
            pair_ac = [j for j in ws if ac_ok(j)]
            pair_ws = [j for j in ws if not ac_ok(j) and w1_ok(j)]
            pair_rd = [j for j in ws if not ac_ok(j) and not w1_ok(j) and rd_ok(j)]
            # an item whose premise Γ writes through a cut of the clause's `requires` (`TieCutEq`: the
            # readings `andUnderAppCut` and `notAsCondition`), the sentence being the premise as written
            pair_cut = [j for j in ws if j not in pair_ac + pair_ws + pair_rd and j in head.get("fnCut", {})
                        and fw[j]["differs"]]
            pair_un = [j for j in ws if j not in pair_ac + pair_ws + pair_rd + pair_cut]
    pair_cut_l = [(j, pair_text[j], head["fnCut"][j]) for j in pair_cut]
    agree = ob["agree"]
    facts_kind = ob["kind"]
    # a held-named function's fact or a `[total]` function's totality owed (`--hand consistency`
    # only): the hand section states `consistent` for every H, by `FnHyp` (`fnHypH`) or otherwise
    held_total = "consistency" in hand and bool(ob.get("held") or ob.get("total") or ob.get("prehyp"))
    held_hand = held_total and bool(ob.get("held"))
    hand_c = hand.get("consistency", "")
    if held_total and not re.search(r"^theorem consistent \(H : HookParams\) : Consistent \(cH H\)", hand_c, re.M):
        raise Refused(f"{name}: the consistency section does not state `consistent` for every H "
                      f"(`theorem consistent (H : HookParams) : Consistent (cH H)`)")
    fnhyp_hand = held_total and bool(re.search(r"^theorem fnHypH \(H : HookParams\) : FnHyp \(cH H\)", hand_c, re.M))
    # without `FnHyp`, the hand section may state the function functional sentences at values in
    # every model of `Γc` (`fnFun_at_values`, the sort predicates' results), and `FnHyp` false
    fnfun_hand = held_total and not fnhyp_hand and bool(re.search(
        r"^theorem fnFun_at_values \(H : HookParams\) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc \(cH H\) ad \(trS ad\)\.pat",
        hand_c, re.M))
    notfnhyp_hand = held_total and not fnhyp_hand and bool(re.search(
        r"^theorem not_fnHypH \(H : HookParams\) : ¬ FnHyp \(cH H\)", hand_c, re.M))
    # a clause's predicate not `\top`: `FnHyp` is no consequence of the named facts, so the section says
    # whether it holds, `fnHypH` or `not_fnHypH`
    if ob.get("prehyp") and not (fnhyp_hand or notfnhyp_hand):
        raise Refused(f"{name}: a clause's predicate is not \\top: the consistency section states `FnHyp` for every H "
                      f"(`theorem fnHypH (H : HookParams) : FnHyp (cH H)`) or that it fails "
                      f"(`theorem not_fnHypH (H : HookParams) : ¬ FnHyp (cH H)`)")
    # otherwise, where each function functional sentence is, as written, a sort predicate's
    # `functional` sentence and the clauses meet what `LibEv.sortPredFun_evC` reads, the tie states
    # them at values in every model of `Γc` (`fnFun_section`)
    fnfun_idx = by_class["function functional"]
    fnfun_ok = {int(x) for x in re.findall(r"\d+", head.get("fnFunOK", ""))}
    fnfun_gen = (not fnfun_hand and "fnFun" not in hand_c and bool(fnfun_idx) and head.get("fnFunGate") == "true"
                 and all(i in fnfun_ok and sents[i]["plain"] for i in fnfun_idx))
    tp_params = ob["hform"] and head["totalNil"] != "true"
    # where a `[total]` function applies a parameter the text declares total, its totality holds
    # under the interpretations total on those parameters (`totalObligationsRP callOrder
    # defn.totalParams`): the statements take `ParamsTotal` as the hypothesis on H, and one H meets
    # it (`constH` at a value the search exhibits of the parameters' one result sort)
    tp_held = tp_params and head.get("totalTp") == "true" and head.get("totalWit") == "true"
    # otherwise, where the tie states `FnHyp` for every H (`fnHypH`, without a hypothesis on H: the
    # consistency section by hand, or the generated one of a text without an open generator, an owed
    # agreement or a parameter declared total), and each function functional sentence is, as written,
    # a sort predicate's `functional` sentence or that of a function of the text declared total: the
    # tie states them at values in every model of `Γc` from `FnHyp`, which gives a function declared
    # total its values and decides the clauses' conditions where `needsWitness` holds
    # (`fnfun_section_fnhyp`)
    fnhyp_all = (bool(re.search(r"^theorem fnHypH \(H : HookParams\) : FnHyp \(cH H\)", hand_c, re.M))
                 if "consistency" in hand else not raw and not agree and not tp_held)
    fnfun_u = {int(x) for x in re.findall(r"\d+", head.get("fnFunU", ""))}
    fnfun_fh = (not fnfun_gen and not fnfun_hand and "fnFun" not in hand_c and bool(fnfun_idx) and fnhyp_all
                and head.get("fnFunPre") == "true"
                and all((i in fnfun_ok or i in fnfun_u) and sents[i]["plain"] for i in fnfun_idx))
    fnfun_user = [i for i in fnfun_idx if i not in fnfun_ok] if fnfun_fh else []
    fnfun_gen = fnfun_gen or fnfun_fh
    fnfun_any = fnfun_hand or fnfun_gen
    if fnfun_chunk and fnfun_fh:
        raise Refused(f"{name}: --fnfun-chunk cuts the sort-predicate route's `fnFun_checked` and `fnFun_trS`; "
                      f"this text's function functional sentences take the `FnHyp` route (`fnfun_section_fnhyp`), "
                      f"which it does not cut")
    parts = dict(zip(["ctors", "fns", "hooks", "colls", "prios"], head["attrsParts"].split()))
    if head["attrsAgree"] != "true":
        bad = [k for k, v in parts.items() if v != "true"]
        raise Refused(f"{name}: the attributes do not agree with the definition (attrsAgree false; failing "
                      f"{', '.join(bad)})")
    taken = set(RESERVED)
    rn = [ident(short_sym(k["name"]), f"openGen{j}", taken) for j, k in enumerate(raw)]
    sn = {}
    for k in raw:
        if k["res"] not in sn:
            sn[k["res"]] = ident(k["sort"].lower() if k["sort"].isalpha() else None,
                                 f"srt{k['res']}", taken)
    cons_text = [i for i in idx if cls[i] in CONS_CLASSES and sents[i]["cons"] and sents[i]["plain"]]
    nj = by_class["no junk"]
    nj_triv = [(i, sents[i]["triv"][0]) for i in nj if sents[i]["triv"]]
    nj_items = [i for i in nj if not sents[i]["triv"] and sents[i]["consItem"]]
    kc = head["kitemCons"].split()
    kp = head["kitemPerm"].split()
    kitem_ok = kc == ["true", "false"] and kp == ["true", "true"]
    nj_kitem = [i for i in nj if not sents[i]["triv"] and not sents[i]["consItem"] and sents[i]["kitem"] and kitem_ok]
    # the no-junk sentence of another sort with generators that is not Γ's item as written: the item
    # over its generators in the text's order (`gensInOrder`) or in a permutation of
    # `Semantics.gens`, whatever the sort (`noJunkItem_of_subset` reads the generators as a set); the
    # sort of an open generator also states that generator open
    nj_sorts = [(i, head["nj"][i][0]) for i in nj
                if not sents[i]["triv"] and not sents[i]["consItem"] and i not in nj_kitem and head["nj"].get(i)]
    nj_sort_new = {}
    for i, e in nj_sorts:
        if e["srt"] not in sn:
            sn[e["srt"]] = ident(e["sort"].lower() if e["sort"].isalpha() else None, f"srt{e['srt']}", taken)
            nj_sort_new[e["srt"]] = e["sort"]
    inv = {j: i for i, j in mapped.items()}
    idem = inv.get(61) if cls.get(inv.get(61)) == "set idempotence" else None
    # the idempotence sentences of the other set collections (the definition's own, hooked to
    # SET.concat), each `(index, concatenation symbol, variable)`; refuted by
    # `setColl_idem_refuted_text`, which decides in the kernel that the collection is a set
    # collection with a value of its key sort and that the sentence is its idempotence sentence
    own_idem = [(i,) + m for i in by_class["set idempotence"] if i != idem
                for m in [own_idem_shape(raws.get(i, ""))] if m]
    lib166 = inv.get(166) if cls.get(inv.get(166)) == "library" else None
    rule_map = [(j, ix[0]) for j, ok, ix in head["rules"] if ok and len(ix) == 1]
    rules_full = (len(rule_map) == nrules and sorted(i for _, i in rule_map) == by_class["rewrite rule"])
    rule_text = [i for _, i in rule_map] if rules_full else []
    comp_map = [(j, i) for j, i in rule_map if j in head.get("ruleComp", ())] if rules_full else []
    covered = set(fn_text) | set(rule_text) | set(cons_text) | {i for i, _ in nj_triv} | set(nj_items) | set(nj_kitem)
    covered |= {i for i, _ in nj_sorts}
    if fn_pair or fn_pairs:
        covered |= set(pair_text)
    if fn_rds:
        covered |= set(pair_text) - {pair_text[j] for j in pair_un}
    covered |= {i for i, _, _ in own_idem}
    if idem is not None:
        covered.add(idem)
    # a user lemma has no generated theorem: it is the tie's remainder, as an uncovered sentence of a
    # class with a theorem is
    uncovered = [(i, cls[i]) for i in idx
                 if (cls[i] in THEOREM_CLASSES and i not in covered) or cls[i] in USER_LEMMA_CLASSES]
    gamma = (fn_full and rules_full) or (fn_align and nrules == 0)
    fn_any = fn_full or fn_align
    open_fun = [i for i in idx if cls[i] == OPEN_FUNCTIONAL_CLASS and sents[i]["fh"] in {k["name"] for k in raw}]
    param_lem = by_class[PARAM_LEMMA_CLASS]
    param_fun = by_class[PARAM_FUNCTIONAL_CLASS]
    total_names = re.findall(r"[^\s\[\],]+", head.get("totalParams", ""))
    user_lem, user_lem_v = by_class[USER_LEMMA_CLASS], by_class[USER_LEMMA_VALUES_CLASS]
    if tp_params and (not tp_held or raw or agree or ob["match"] or ob["owed"]):
        raise Refused(f"{name}: a `[total]` function owes the totality of a parameter the text declares total "
                      f"(`totalObligationsRP callOrder []` not empty): tiegen states `ParamsTotal` as the hypothesis "
                      f"only where the totality holds under it (`totalObligationsRP callOrder defn.totalParams` empty), "
                      f"one value exhibited is of every such parameter's result sort (`constTotal`), and no open "
                      f"generator, agreement, match independence or condition is owed")
    if len(raw) > 1:
        raise Refused(f"{name}: {len(raw)} open generators: tiegen states one")
    if raw and (agree or confined or facts_kind != "FnFacts"):
        raise Refused(f"{name}: an open generator beside an owed agreement or a confined sort: tiegen states "
                      f"neither together")
    if agree and confined and not held_hand:
        raise Refused(f"{name}: an owed agreement beside a confined sort: tiegen states not both")
    if confined and head["litBool"] != "true":
        raise Refused(f"{name}: the definition reads a confined sort and Bool holds other than its literals (`Γcl` empty)")
    law_fns = sorted({sents[i]["eh"] for i in law_idx})
    rawd = [(k, rn[j], sn[k["res"]]) for j, k in enumerate(raw)]
    sig_rs = ranges(int(head["nSig"]), chunks[0], chunks[1])
    decl_rs = ranges(int(head["nDecl"]), 0, chunks[2])
    dc = head["declCounts"].split()

    L = []
    w = L.append
    marks = []
    mark = lambda m: marks.append((len(L), m))  # the section of the file `--split` puts what follows in

    def gsym_block(beq):
        """The literal `gSymCodes` of Γ's symbol names' codes and its equation (`--decl-syms-literal`,
        `--heads-plain`), with `symCode_beq` where `beq` (`hasSymL_eq` reads it)."""
        w("/-! ## Γ's symbol names, as a literal -/")
        w("")
        w("/-- Γ's symbol names (`c.symName` of each of `kernelSyms c`, in its order), each as its code")
        w("(`KoreAML.Distinct.strCode`), written out. -/")
        w("def gSymCodes : List Nat :=")
        w("  [" + wrap_nums([str(str_code(n)) for n in head["gSyms"]], 3) + "]")
        w("")
        w("theorem gSymCodes_eq :")
        w("    (kernelSyms c).map (fun k => KoreAML.Distinct.strCode (c.symName k.name)) = gSymCodes := by")
        w("  decide +kernel")
        w("")
        if beq:
            w("/-- Two names are equal exactly where their codes are (`strCode_inj`). -/")
            w("theorem symCode_beq (a b : String) :")
            w("    (KoreAML.Distinct.strCode a == KoreAML.Distinct.strCode b) = (a == b) := by")
            w("  apply Bool.eq_iff_iff.mpr")
            w("  simp only [beq_iff_eq]")
            w("  exact ⟨fun h => KoreAML.Distinct.strCode_inj h, fun h => h ▸ rfl⟩")
            w("")
    # ---- header
    w("/-")
    w(f"  The tie (C14) on `{text_rel}`, the kompiled text of construct fixture {name}")
    w(f"  (`test/constructs/fixtures/{name}`), sentence by sentence, against the translation of the text as")
    w("  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for")
    w("  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by")
    cmd = name + (f" --at-values {','.join(map(str, sorted(at_values)))}" if at_values else "") + \
        (f" --reads-h {','.join(map(str, sorted(reads_h)))}" if reads_h else "")
    if hand:
        w(f"  `test/constructs/tiegen.py {cmd}`, its {', '.join(sorted(hand))} section by hand; run from the package root:")
        w(f"  `lake env lean -j1 test/{ns}.lean`.")
    else:
        w(f"  `test/constructs/tiegen.py {cmd}`; run from the package root: `lake env lean -j1 test/{ns}.lean`.")
    w("")
    if confined:
        w("  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its")
        w("  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise")
        w("  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end)" +
          (", and every\n  premise of `Γc` is a premise of Γ or `boolClosed`, the one item of `Γcl` here, which no sentence\n"
           "  states (`gamma_origin_c`)." if gamma else "."))
        w("")
    w("  Layer 1.")
    if wf_ok:
        w("  - `wf_defn`: `wf defn = true`.")
    else:
        w(f"  - `coreOK`: `coreOK`; `wf` fails at the conjuncts {', '.join(failing)} (`wfFailing`).")
    if ovl_fn:
        refl = (f", the {numword(len(ovl_nc))} refuted sentence{'s' if len(ovl_nc) > 1 else ''} in no class (`ovlRefuted`)"
                if ovl_nc else "")
        tokl = f", KItem's no-junk sentence {tok_omit[0]}, listed apart (`tokKItemApart`)," if tok_omit else ""
        w(textwrap.fill(
            f"- The account: the class lists{refl}{tokl} and the {numword(len(ovl_fn))} sentence"
            f"{'s' if len(ovl_fn) > 1 else ''} of a function-overloaded symbol, listed apart (`ovlFnApart`), "
            f"partition the {len(idx)} sentences of the user module {um}, the classes in "
            f"`{'tieClassesOvl' if ovl_any else 'tieClasses'}`' order (`account`, `account_sizes`, `account_classes`); "
            "the no-direction class holds exactly the sentences that apply a symbol Γ lacks (`account_absent`, "
            "`absent_closed`).", width=100, initial_indent="  ", subsequent_indent="    ", break_on_hyphens=False,
            break_long_words=False))
    elif tok_omit:
        refl = (f", the {numword(len(ovl_nc))} refuted sentence{'s' if len(ovl_nc) > 1 else ''} in no class (`ovlRefuted`)"
                if ovl_nc else "")
        w(textwrap.fill(
            f"- The account: the class lists{refl} and KItem's no-junk sentence {tok_omit[0]}, listed apart "
            f"(`tokKItemApart`), partition the {len(idx)} sentences of the user module {um}, the classes in "
            f"`{'tieClassesOvl' if ovl_any else 'tieClasses'}`' order (`account`, `account_sizes`, `account_classes`); "
            "the no-direction class holds exactly the sentences that apply a symbol Γ lacks (`account_absent`, "
            "`absent_closed`).", width=100, initial_indent="  ", subsequent_indent="    ", break_on_hyphens=False,
            break_long_words=False))
    elif ovl_nc:
        w(f"  - The account: the class lists and the {numword(len(ovl_nc))} refuted sentence{'s' if len(ovl_nc) > 1 else ''} in no class (`ovlRefuted`)")
        w(f"    partition the {len(idx)} sentences of the user module {um}, the classes in `tieClassesOvl`'s order")
        w("    (`account`, `account_sizes`, `account_classes`); the no-direction class holds exactly the")
        w("    sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).")
    elif ovl_any:
        w(f"  - The account: the class lists partition the {len(idx)} sentences of the user module {um}, in")
        w("    `tieClassesOvl`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds")
        w("    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).")
    else:
        w(f"  - The account: the class lists partition the {len(idx)} sentences of the user module {um}, in")
        w("    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds")
        w("    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).")
    if abs_proj:
        w(f"  - `absent_proj_below`: the {len(abs_proj)} no-direction sentences that are equations of a projection")
        w("    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).")
    il = ", ".join(map(str, law_idx))
    rnames = " and ".join(f"`{r}`" for _, r, _ in rawd)
    if law_idx:
        w("  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the law")
        w(f"    sentences ({il}) are no equations of {', '.join(f'`{x}`' for x in law_fns)} (`AttrsAgree.isLaw`), so the priorities")
        w("    compared are those of its equations.")
    elif raw:
        gens = "generator" if len(raw) == 1 else "generators"
        w(f"  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the open")
        w(f"    {gens} {rnames} {'is a parameter' if len(raw) == 1 else 'are parameters'} declared without `hook` and without `function`, of which the")
        w("    text states no equation.")
    else:
        w("  - `attrs_agree`: the attributes the translation does not read agree with `defn`.")
    if head["sigAll"] == "true":
        w(f"  - `sig_origin`: each of the {head['nSig']} items of `sigItems c` is a declaration's item of the text or a")
        w("    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters")
        w("    of a symbol Γ has (both by ranges of the lists).")
    else:
        w(f"  - `sig_origin_but_next`: each of the {head['nSig']} items of `sigItems c` but one is a declaration's item")
        w("    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states")
        w("    and the text, having no `\\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails")
        w("    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).")
    no_law = raw and all(k["assoc"] == "false" and k["idem"] == "false" for k in raw)
    if raw:
        srts = sorted({s for _, _, s in rawd})
        w(f"  - The definition reads no confined sort (`readsConfined_c`); its {numword(len(raw))} open generator{'s' if len(raw) > 1 else ''} {'is' if len(raw) == 1 else 'are'} {rnames}")
        w(f"    (`params_raw`), of {', '.join(k['sort'] for k in raw)}. It owes no fact")
        w("    about its functions (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the")
        w("    step's closure has a model for every H that satisfies the open generator's laws (`facts`,")
        if no_law:
            w(f"    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`); {rnames}")
            w("    has no law, so that is every H (`openLaws_any`, `consistent_any`).")
        else:
            w("    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`).")
    elif held_total:
        th = "`Γc`" if confined else "Γ"
        owes = []
        if ob.get("held"):
            hn = " and ".join(f"`{x}`" for x in ob["held_names"])
            owes.append(f"the fact of the held-named function {hn} (`held_named`, `HeldOwed`: the variables of its "
                        f"clauses are held, or it has a result at every argument list of its sorts)")
        if ob.get("total"):
            tn = " and ".join(f"`{x}`" for x in ob["total_names"])
            owes.append(f"the totality of the `[total]` function {tn} (`total_named`)")
        if agree:
            owes.append("the agreement of " + " and ".join(f"`{x}`" for x in ob["agree_names"]) + " (`agree_named`)")
        if ob["match"]:
            owes.append("the match independence of a clause (`match_named`)")
        if ob["owed"]:
            owes.append("the condition of a rule or clause (`owed_rules`, `owed_clauses`)")
        if ob.get("prehyp"):
            owes.append("`FnHyp` itself: a clause's predicate is not `\\top` (`Semantics.clausesPreTop` false), so the "
                        "named facts do not give it and `kcore gen --core` takes it as the hypothesis of its statements")
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`) and has no open generator (`noRaw`).")
        para = (f"It owes {'; '.join(owes)}, which no decider confirms. The consistency section, written by hand, "
                f"proves that {th} with the step's closure has a model for every H (`consistent`), ")
        para += ("through `FnHyp` for every H (`fnHypH`)." if fnhyp_hand else
                 "without `FnHyp`, " + ("which is false for every H (`not_fnHypH`)" if notfnhyp_hand else
                                        "which it does not state (its comment says why)") +
                 (": the function functional sentences, the sort predicates' `functional` sentences, hold at "
                  "values in every model of `Γc` from the sort predicates' own results (`fnFun_at_values`)."
                  if fnfun_any else
                  ": the function functional sentences, owed as `FnHyp`, are not shown by this tie where `FnHyp` fails."))
        w(textwrap.fill(para, 104, initial_indent="    ", subsequent_indent="    "))
    elif agree:
        an = " and ".join(f"`{x}`" for x in ob["agree_names"])
        w("  - The definition reads no confined sort (`readsConfined_c`) and has no open generator (`noRaw`).")
        w(f"    It owes {'one fact' if len(agree) == 1 else numword(len(agree)) + ' facts'}, the agreement of {an} (`agree_named`): no decider shows that its")
        w("    competing clauses give one result where more than one applies (`ClausesAgree`).")
        if "consistency" in hand:
            w("    The agreement holds for every H (`agree`), so Γ with the step's closure has a model for every")
            w("    H (`facts`, `consistent`).")
        else:
            w("    Under every H where it holds (`AgreeOwed`), Γ with the step's closure has a model (`facts`,")
            w("    `consistent`): the proof of `AgreeOwed` is owed.")
    elif ob["match"] or ob["owed"]:
        th = "`Γc`" if confined else "Γ"
        owes = (["the match independence of a clause (`match_named`)"] if ob["match"] else []) + \
            (["the condition of a rule or clause (`owed_rules`, `owed_clauses`)"] if ob["owed"] else [])
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`) and has no open generator")
        w(f"    (`noRaw`). It owes {' and '.join(owes)}.")
        w("    The consistency section, written by hand, proves what it owes for every H"
          + (" (`openDecidedH`)" if facts_kind == "FnFacts" else "") + ",")
        w(f"    so {th} with the step's closure has a model for every H (`consistent`).")
    elif tp_held:
        th = "`Γc`" if confined else "Γ"
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`) and has no open generator (`noRaw`).")
        w("    Its `[total]` functions are total under every H total on the parameters the text declares")
        w("    total (`total_named` at `defn.totalParams`), and it owes no other fact (`term_named`,")
        w(f"    `agree_named`, `match_named`), so {th} with the step's closure has a model for every H with")
        w("    `ParamsTotal c defn.totalParams H` (`consistent`); one H has it (`paramsTotal_witness`,")
        w("    `consistent_witness`).")
    elif facts_kind == "FnFacts":
        th = "`Γc`" if confined else "Γ"
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes")
        w("    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's")
        w(f"    condition (`owed_rules`, `owed_clauses`), so {th} with the step's closure has a model for every")
        w("    H (`consistent`).")
    else:
        w("  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and")
        w("    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's")
        w("    closure has a model for every H (`consistent`).")
    w("")
    w("  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).")
    if fn_align:
        ow = f"the {numword(len(fn_nonlit))} `[owise]` equations" if len(fn_nonlit) > 1 else "the `[owise]` equation"
        w(f"  - Function equations ({len(fn_text)}): each of Γ's items is the translation of one sentence up to a renaming")
        w("    of element variables, free and bound, both ways, in the order `fnText` lists them (`fn_align`;")
        w(f"    `alphaB`, `satisfies_of_alphaB`): pattern for pattern but for {ow}")
        w("    (`fn_shape_but_owise`), whose exclusion the text writes with its own bound variable")
        w("    (`owise_not_literal`). `fns_entailed` (E), `fns_from_text` (the converse), `fn_prios` (the")
        w("    priorities the sentences state are the clauses').")
    if fn_full and fn_pre:
        pl = ", ".join(f"{i} ({fn_pre[i]})" for i in sorted(fn_pre))
        w(textwrap.fill(
            f"Function equations ({len(fn_user)}, and {numword(len(fn_pre))} sentences of the text's prelude modules, "
            f"{pl}, which no user sentence is): each of Γ's items is the translation of one sentence, in the order "
            f"`fnText` lists them (`fn_shape`); its user-module sentences are the class, the others those prelude "
            f"sentences (`fns_account`, and `{'`, `'.join(n[:1].lower() + n[1:] + '_eq' for n in pre_mods.values())}`: "
            f"they are the text's); `fns_entailed` (E), `fns_from_text` (the converse), `fn_prios` (the priorities "
            f"the sentences state are the clauses').",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    elif fn_full:
        w(f"  - Function equations ({len(fn_text)}): each of Γ's items is the translation of one sentence, in the")
        w("    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),")
        w("    `fn_prios` (the priorities the sentences state are the clauses').")
    if fn_pair:
        wi, wj = pair_text[pair_w], pair_w
        nfe = len(by_class["function equation"])
        w(textwrap.fill(
            f"Function equations ({nfe}) and the priority equation ({wi}, of priority {sents[wi]['prio']}), in the "
            f"order `fnText` lists them (`fns_account`): each of Γ's items but item {wj} is the translation of "
            f"one sentence (`shape`), so Γ entails it (`fns_entailed`); item {wj} is the clause of {wi} under the "
            f"negation of the clauses of a smaller priority that are not `aside`, which sentence {wi} entails "
            f"(`w1`, W1) and is without that premise (`w_text`); `fns_from_text` (the converse), `fn_prios` "
            f"(the priorities the sentences state are the clauses').",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    if fn_pairs:
        nfe, npe = len(by_class["function equation"]), len(by_class["priority equation"])
        wtx = ", ".join(f"{j} ({pair_text[j]})" for j in pair_ws)
        atx = ", ".join(f"{j} ({pair_text[j]})" for j in pair_ac)
        txt_ = (f"Function equations ({nfe}) and priority equations ({npe}), in the order `fnText` lists them "
                f"(`fns_account`): each of Γ's items but {', '.join(map(str, sorted(pair_ws + pair_ac)))} is the "
                f"translation of one sentence (`shape`), so Γ entails it (`fns_entailed`).")
        if pair_ws:
            txt_ += (f" Item{'s' if len(pair_ws) > 1 else ''} {wtx} (sentence in parentheses) "
                     f"{'are' if len(pair_ws) > 1 else 'is'} the clause under the negation of the clauses of a "
                     f"smaller priority that are not `aside`, which the sentence entails (`prio<j>_w1`, W1) and is "
                     f"without that premise (`prio<j>_text`).")
        if pair_ac:
            txt_ += (f" Item{'s' if len(pair_ac) > 1 else ''} {atx} and {'their sentences' if len(pair_ac) > 1 else 'its sentence'} "
                     f"agree up to the order of the operands of their sorted disjunctions and the names of their "
                     f"variables (`ac<j>_same`, `TieAlpha.acEqB`), so they are satisfied by the same "
                     f"interpretations (`ac<j>_iff`) and Γ entails the sentence.")
        txt_ += " `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the clauses')."
        w(textwrap.fill(txt_, width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False,
                        break_long_words=False))
    if fn_rds:
        w(readings_header(by_class, pair_text, pair_ws, pair_ac, pair_rd, pair_un, pair_cut_l, confined))
    if rules_full and nrules:
        w(f"  - Rewrite rules ({nrules}): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence")
        w("    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).")
        if comp_map:
            w(textwrap.fill(
                f"Rule{'s' if len(comp_map) > 1 else ''} {', '.join(str(j) for j, _ in comp_map)} "
                f"{'have' if len(comp_map) > 1 else 'has'} rules of a smaller priority: Γ's item has also the "
                f"premise `¬\0⋁\0competitors`, that none of them applies, which the sentence states by its "
                f"priority attribute only (`rule_prios`); the item without both premises is the sentence "
                f"(`rule<j>_text`, `item_of_minusComp`).",
                width=100, initial_indent="    ", subsequent_indent="    ", break_on_hyphens=False,
                break_long_words=False).replace("\0", " "))
    w(f"  - Constructor sentences ({len(cons_text)}): entailed by Γ (`cons_entailed`).")
    if ovl_eq:
        w(f"  - Overload axioms ({', '.join(map(str, ovl_eq))}): entailed by Γ, whose overload equation states each at every")
        w("    element (`ovleq_entailed`).")
    if ovl_nc:
        w(f"  - No-confusion sentences of two symbols that meet at values ({', '.join(map(str, ovl_nc))}; an overloading")
        w("    symbol and a symbol it overloads, which the overload axiom equates there): refuted by every model")
        w("    of Γ (`ovlnc_refuted`), in no class.")
    if tok_omit:
        w(tok_omit_doc(tok_omit[0], tok_sorts))
    if ovl_fn:
        w(ovl_fn_doc(ovl_fn, ovl_fn_rows, ovl_fn_hand))
    w(f"  - No junk ({len(nj_triv)} of a sort without generators, `nojunk_trivial_entailed`; {len(nj_items)} equal to")
    w(f"    one of Γ's constructor items, `nojunk_items`; {len(nj_kitem)} KItem's with its disjuncts in the text's")
    w("    order, `nojunk_kitem_entailed`).")
    if idem is not None:
        w(f"  - Set idempotence ({idem}): Γ with it has no model (`idem_refuted`).")
    for i, f, _ in own_idem:
        w(f"  - Set idempotence of the set collection of `{f}` ({i}): Γ with it has no model")
        w(f"    (`own_idem_refuted_{i}`, from `setColl_idem_refuted_text`).")
    if lib166 is not None:
        w(f"  - Library sample, {lib166} (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).")
    if gamma and fn_align:
        w("  - The converse over Γ's content: each premise is a function sentence's translation up to a")
        w("    renaming, one of the five parts Γ defines by predicates, or definedness (`gamma_origin`,")
        w("    `gamma_from`).")
    elif gamma:
        w("  - The converse over Γ's content: each premise is a function sentence's translation, one of the")
        w("    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).")
    if fn_pair:
        w(textwrap.fill(
            f"The converse over Γ's content: each premise is a consequence of the function sentences "
            f"({pair_text[pair_w]} through W1), Γ's rule items, the five parts Γ defines by predicates, or "
            f"definedness (`gamma_from`).",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    if fn_pairs:
        w(textwrap.fill(
            f"The converse over Γ's content: each premise is a consequence of the function sentences ("
            + ", ".join(([f"{', '.join(str(pair_text[j]) for j in pair_ws)} through W1"] if pair_ws else [])
                        + [f"{pair_text[j]} through `ac{j}_iff`" for j in pair_ac]) + "), Γ's rule items, the five "
            f"parts Γ defines by predicates, or definedness (`gamma_from`).",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    if fn_rds:
        w(readings_gamma_header(pair_text, pair_ws, pair_ac, pair_rd, pair_un, pair_cut_l))
    owed_more = ""
    if law_idx:
        owed_more += "; function law: owed as `FnLaws` (`law_account`)"
    if open_fun:
        owed_more += "; open generator functional: owed as `OpenTotal`\n    (`open_functional_not_item`)"
    if open_law:
        owed_more += "; open generator law: Γ's law item (`openlaw_item`,\n    `openlaw_account`)"
    if param_fun:
        owed_more += ("; parameter functional: owed as `ParamsTotal`\n    (`total_params`, `paramfunctional_account`, "
                      "`paramfunctional_heads`)")
    if param_lem:
        owed_more += ("; parameter lemma: owed as a hypothesis on H, at values\n    (`paramlemma_account`, "
                      "`paramlemma_heads`,\n    " + ("`paramlemma_reads_h`, " if reads_h else "") +
                      "`ParamLemmaWitnessAtValues`)")
    if user_lem or user_lem_v:
        owed_more += ("; user lemma: owed, by hand\n    (`userlemma_account`, `UserLemmaEntailed`, "
                      "`UserLemmaAtValues`)")
    if fnfun_any:
        if fnfun_fh:
            w("  - Function functional: at values in every model of `Γc`, from `FnHyp`, which holds for every H")
            w("    (`fnHypH`), and the sort predicates' results (`fnFun_at_values`, `fnFun_account`).")
        else:
            w("  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not")
            w("    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).")
        if owed_more:
            w(textwrap.fill("Hooked functional, collection law, library: at values (no theorem here)" +
                            owed_more.replace("\n    ", " ") + "; no direction: `absent_closed`.",
                            width=100, initial_indent="  - ", subsequent_indent="    ",
                            break_on_hyphens=False, break_long_words=False))
        else:
            w("  - Hooked functional, collection law, library: at values (no theorem here); no direction:")
            w("    `absent_closed`.")
    else:
        w("  - Hooked functional, collection law, library: at values (no theorem here); function functional:")
        w(f"    owed as `FnHyp` ({'not stated here; ' if held_total and not fnhyp_hand else ''}no theorem){owed_more}; no direction: `absent_closed`.")
    w("")
    if law_idx:
        what = law_what(law_idx, raws, sents)
        w(f"  The law sentences ({il}; {what}) are neither a function equation's item nor a constructor item of Γ")
        w("  (`law_not_item`): the reader reads each as a")
        w("  law of the function stated at values (`Definition.laws`, `law_text`: the sentence as written is the")
        w(f"  law's `lawPattern`), owed as `FnLaws`. The account holds them in the class `{LAW_FN_CLASS}`, of the")
        w("  direction `hypothesis` (Γ does not hold the sentence; it is owed).")
        w("")
    if raw or nj_sorts:
        para = []
        for i, e in nj_sorts:
            gr = [r for k, r, s in rawd if k["res"] == e["srt"]]
            para.append(f"{e['sort']}'s no junk ({i}) is entailed (`nojunk_{sn[e['srt']]}_entailed`): its item lists {e['sort']}'s generators"
                        + (f", {' and '.join(f'`{g}`' for g in gr)} among them," if gr else "")
                        + (" in the text's order." if e["form"] == "order" else " in another order than `Semantics.gens`."))
        for i in open_law:
            para.append(f"The law sentence of {rnames} ({i}) is Γ's law item as written and entailed")
            para.append(f"(`openlaw_item`, `openlaw_entailed`); the account holds it in `{LAW_OPEN_CLASS}`, of the")
            para.append("direction `equal`.")
        if open_fun:
            para.append(f"{rnames}'s functional sentence{'s' if len(open_fun) > 1 else ''} ({', '.join(map(str, open_fun))}) {'is' if len(open_fun) == 1 else 'are'} no item of")
            para.append("Γ and is owed at values as `OpenTotal` (`open_functional_not_item`); the account holds it in")
            para.append(f"`{OPEN_FUNCTIONAL_CLASS}`, of the direction `hypothesis`.")
        if para:
            w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                            break_on_hyphens=False, break_long_words=False))
            w("")
    if param_fun:
        para = [f"The parameter functional sentence{'s' if len(param_fun) > 1 else ''} ({', '.join(map(str, param_fun))}) "
                f"{'are' if len(param_fun) > 1 else 'is'} the `functional` sentence of a parameter symbol no registry hook "
                "interprets that the text declares total (`Definition.totalParams`, `total_params`), which the reader "
                "reads as that declaration. Γ states the parameter's graph at values from the interpretation "
                "(`ΓDomains`: its application to values denotes `paramVal`'s value, or nothing), so the sentence "
                "holds at values where H gives the parameter a value of its sort at every argument list of its "
                "sorts: the hypothesis on H the statements take (`ParamsTotal`). The account holds "
                f"{'them' if len(param_fun) > 1 else 'it'} in the class `{PARAM_FUNCTIONAL_CLASS}`, of the direction "
                "`hypothesis` (`paramfunctional_account`), and every such sentence of the user module is in it "
                "(`paramfunctional_heads`)."]
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    if param_lem and reads_h:
        shape = [i for i in param_lem if i not in reads_h]
        para = [f"The parameter lemmas ({', '.join(map(str, param_lem))}) are lemmas whose truth at values reads a "
                "value the interpretation gives."]
        if shape:
            para.append(f"{', '.join(map(str, shape))} {'apply' if len(shape) > 1 else 'applies'} a parameter symbol "
                        "no registry hook interprets, whose value the interpretation gives.")
        para.append(f"{', '.join(map(str, reads_h))}, named by `--reads-h`, {'apply' if len(reads_h) > 1 else 'applies'} "
                    "no such parameter: each applies, at a head Γ has, a symbol through which evaluation may read the "
                    "interpretation "
                    "(`paramlemma_reads_h`, `appliesHRead`), a function at argument lists none of its clauses "
                    "decides, whose rest Γ states from the interpretation (`ΓFallback`), or a hook at a point its "
                    "text leaves open.")
        para.append("Each is owed as a hypothesis on H, at the valuations sending its variables to values "
                    "(`EntailsAtValues (cH H) ad (trS ad).pat`), since Γ states a parameter's graph, a function's "
                    "rest and a hook's open point at values only. The account holds them in the class "
                    f"`{PARAM_LEMMA_CLASS}`, of the direction `hypothesis`. A hypothesis no H satisfies would tie a "
                    "text without a model, so the tie owes one H at which `FnHyp` holds and every "
                    "parameter lemma holds at values (`ParamLemmaWitnessAtValues`, stated here and proved by hand: "
                    "owed). Every `simplification` equation of the user module whose left side's head is a "
                    "parameter symbol without `impl` is one of them (`paramlemma_heads`).")
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    elif param_lem:
        para = [f"The parameter lemmas ({', '.join(map(str, param_lem))}) apply a parameter symbol no registry hook "
                "interprets, whose value the interpretation gives: each is owed as a hypothesis on H, at the "
                "valuations sending its variables to values (`EntailsAtValues (cH H) ad (trS ad).pat`), since Γ "
                "states the parameter's graph at values only (`ΓDomains`). The account holds them in the class "
                f"`{PARAM_LEMMA_CLASS}`, of the direction `hypothesis`. A hypothesis no H satisfies would tie a text "
                "without a model, so the tie owes one H at which `FnHyp` holds and every "
                "parameter lemma holds at values (`ParamLemmaWitnessAtValues`, stated here and proved by hand: "
                "owed). Every `simplification` equation of the user module whose left side's head is a parameter "
                "symbol without `impl` is one of them (`paramlemma_heads`)."]
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    if user_lem or user_lem_v:
        # the class at values holds the lemmas `--at-values` names and, named by no option, the user's
        # equations of a symbol whose value the registry gives (`Parse.regLemmaEqn`)
        v_named = [i for i in user_lem_v if i in at_values]
        v_reg = [i for i in user_lem_v if i not in at_values]
        if not v_reg:
            para = [f"The user lemmas ({', '.join(map(str, user_lem + user_lem_v))}) are sentences of a user's file "
                    "that the reader leaves out of Γ as lemmas (inert simplification) and that apply no parameter "
                    "symbol without `impl`."]
        else:
            para = [f"The user lemmas ({', '.join(map(str, user_lem + user_lem_v))}) are sentences of a user's file "
                    "that the reader leaves out of Γ and that apply no parameter symbol without `impl`."]
            if user_lem or v_named:
                para.append(f"Lemmas (inert simplification): {', '.join(map(str, user_lem + v_named))}.")
            para.append("Equations whose left side is headed by a symbol whose value the registry gives "
                        f"(`Parse.regLemmaEqn`): {', '.join(map(str, v_reg))}; each rests on that symbol's graph, "
                        "which Γ states at values.")
        if user_lem:
            para.append(f"Of the class `{USER_LEMMA_CLASS}` (direction `entailed`): {', '.join(map(str, user_lem))}, "
                        "each owed as `Γ (cH H) ⊧ (trS ad).pat` for every H (`UserLemmaEntailed`).")
        if user_lem_v:
            para.append(f"Of the class `{USER_LEMMA_VALUES_CLASS}` (direction `atValues`)"
                        + (", named by `--at-values`" if not v_reg else "") + f": {', '.join(map(str, user_lem_v))}, "
                        "each owed at the valuations sending its variables to values, for every H "
                        "(`UserLemmaAtValues`).")
        para.append("Both are stated here and proved by hand: owed. A lemma that no H meets has no proof; one that "
                    "holds under some interpretations only is a parameter lemma (`--reads-h`).")
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    w(f"  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` ({len(unmapped)});")
    if user_lem or user_lem_v:
        w(f"  the sentences of a class with a theorem that no theorem here holds of, and the user lemmas, are")
        w(f"  `uncovered` ({len(uncovered)}).")
    else:
        w(f"  the sentences of a class with a theorem that no theorem here holds of are `uncovered` ({len(uncovered)}).")
    w("-/")
    w("import KcoreSpec")
    w("")
    w("set_option autoImplicit false")
    w("set_option maxRecDepth 1000000")
    w("")
    w(f"namespace KCore.{ns}")
    w("")
    w("open KCore ML Faithful KoreAML")
    w("")
    w(f'kore_term kore from "{text_rel}"')
    w(f'definition_of defn from "{text_rel}"')
    w(f'user_axioms U from "{text_rel}" module "{um}"')
    for m, pn in pre_mods.items():
        w(f'user_axioms {pn} from "{text_rel}" module "{m}"')
    w("")
    w("noncomputable abbrev c : Semantics := defn.sem")
    w("noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H")
    w("")
    if raw:
        one = len(raw) == 1
        sorts_of = sorted({k["res"] for k in raw})
        w(f"/-- {rnames}, the text's {numword(len(raw))} open generator{'' if one else 's'} (`raw`), and "
          f"{', '.join(k['sort'] for k in raw if k['res'] in sorts_of)}, {'its sort' if one else 'their sorts'}. -/")
        for k, r, _ in rawd:
            w(f"def {r} : Sym := {k['sym']}")
        for s in sorts_of:
            w(f"def {sn[s]} : Srt := {s}")
        w("")
        conj = [f'c.symName {r} = "{k["name"]}"' for k, r, _ in rawd] + \
            [f'c.sortName {sn[s]} = "{next(k["sort"] for k in raw if k["res"] == s)}"' for s in sorts_of]
        w(f"theorem names : {' ∧ '.join(conj)} := by decide +kernel")
        w("")
        srt = lambda s: sn.get(s, str(s))
        tup = [f"({r}, [{', '.join(srt(a) for a in k['args'])}], {s}, {k['assoc']}, {k['idem']})" for k, r, s in rawd]
        if one:
            k, r, s = rawd[0]
            w(f"/-- **The definition's one open generator is `{r}`**, of {k['sort']}, `assoc` {k['assoc']} and `idem` {k['idem']}. -/")
        else:
            w("/-- **The definition's open generators**, each with its sort, `assoc` and `idem`. -/")
        w("theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =")
        w(f"    [{', '.join(tup)}] := by decide +kernel")
    else:
        w("/-- No parameter of the definition is an open generator. -/")
        w("theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel")
    w("")
    if confined:
        w("/-- The definition reads a confined sort: its theory is `Γc`. -/")
        w("theorem readsConfined_c : c.readsConfined = true := by decide +kernel")
    else:
        w("/-- The definition reads no confined sort: its theory is Γ. -/")
        w("theorem readsConfined_c : c.readsConfined = false := by decide +kernel")
    w("")
    w("/-- The axioms of the user module, in text order. -/")
    w(f'noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "{um}")')
    w("")
    w("theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl")
    w(f"theorem userAxioms_length : U.all.length = {len(idx)} := by decide +kernel")
    w("")
    w("/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/")
    w("noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad")
    w("")
    w("theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl")
    w("")
    w("/-! ## Layer 1 -/")
    w("")
    w("set_option maxHeartbeats 1000000 in")
    w("theorem coreOK : c.coreOK = true := by decide_cheap")
    w("theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK")
    w("")
    if wf_ok and wf_parts:
        w("/-! `wf defn` conjunct by conjunct (`wf_of_parts_all`), each a decision of its own; the names")
        w("declared once by their codes (`KoreAML.Distinct.codesDistinct`), sorted in as many passes as the")
        w("bits of the text's number of declarations. -/")
        w(f"theorem sorts_distinct : KoreAML.Distinct.codesDistinct {wf_parts[0]} (defn.emit.sortDecls.map (·.name)) = true := by")
        w("  decide +kernel")
        w(f"theorem syms_distinct :")
        w(f"    KoreAML.Distinct.codesDistinct {wf_parts[1]} (defn.emit.symbolDecls.map (·.name) ++ defn.emit.aliasNames) = true := by")
        w("  decide +kernel")
        w("theorem names_rest : (c.hooksApart && c.predsApart && c.idsOK) = true := by decide_cheap")
        w("theorem okAll_c : c.okAll = true := by decide_cheap")
        w("theorem cert_ok : defn.cert.ok c = true := by decide +kernel")
        w("theorem pres_ok : defn.pres.ok c = true := by decide +kernel")
        w("theorem params_ok : defn.paramsOK = true := by decide +kernel")
        w("theorem faith_ok : c.faithOK = true := by unfold Semantics.faithOK; decide_cheap")
        w("theorem overloads_ok : c.overloadsOK = true := by decide +kernel")
        w("theorem wf_defn : wf defn = true :=")
        w("  wf_of_parts_all sorts_distinct syms_distinct names_rest okAll_c cert_ok pres_ok params_ok faith_ok overloads_ok")
    elif wf_ok:
        w("set_option maxHeartbeats 1000000 in")
        w("theorem wf_defn : wf defn = true := by decide_cheap")
    else:
        w("/-- The conjuncts of `wf` that fail on this text (`kcore account`); `coreOK` holds. -/")
        w("def wfFailing : List String := [" + ", ".join(f'"{x}"' for x in failing) + "]")
    w("")
    # ---- account
    mark("Account")
    w("/-! ## The account: every sentence of the user module is in exactly one class -/")
    w("")
    if ovl_any:
        w("/-- Per class of the tie (`tieClassesOvl`: `tieClasses` with the class overload equation), the")
        w("indices (`AxiomDecl.index`) of its sentences. -/")
    else:
        w("/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/")
    w("def classes : List (String × List Nat) :=")
    rows = []
    for c_ in classes_list:
        rows.append(f'("{c_}", [' + wrap_nums(by_class[c_], 6) + "])")
    w("  [" + ",\n   ".join(rows) + "]")
    w("")
    w("/-- The indices of a class. -/")
    w("def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)")
    w("")
    if ovl_nc:
        w("/-- The no-confusion sentences of two symbols that meet at values (an overloading symbol and a")
        w("symbol it overloads), which Γ refutes (`ovlnc_refuted`): in no class. -/")
        w("def ovlRefuted : List Nat := [" + ", ".join(map(str, ovl_nc)) + "]")
        w("")
    if tok_omit:
        w(f"/-- KItem's no-junk sentence that leaves out the injections from sorts the definition holds below")
        w("KItem (`tokKItemSorts`), which Γ's no-junk item of KItem has: weaker under tokKItem, in no class. -/")
        w("def tokKItemApart : List Nat := [" + ", ".join(map(str, tok_omit)) + "]")
        w("")
    if ovl_fn:
        w("/-- The sentences of a function-overloaded symbol (its `functional` sentence and its no-confusion")
        w("sentences), which Γ holds at the arguments no overload covers only: weaker under overloadFunction,")
        w("in no class. -/")
        w("def ovlFnApart : List Nat := [" + ", ".join(map(str, ovl_fn)) + "]")
        w("")
    if account_sorted and (ovl_nc or tok_omit or ovl_fn):
        raise Refused(f"{name}: --account-sorted with sentences in no class (`ovlRefuted`, `tokKItemApart`, "
                      f"`ovlFnApart`): not stated")
    if ovl_nc or tok_omit or ovl_fn:
        apart = (["the refuted sentences"] if ovl_nc else []) + (["the sentence listed apart"] if tok_omit else []) + \
            (["the sentences of a function-overloaded symbol"] if ovl_fn else [])
        among = (["among the refuted ones"] if ovl_nc else []) + (["listed apart"] if tok_omit else []) + \
            (["among those of a function-overloaded symbol"] if ovl_fn else [])
        if ovl_fn:
            w(textwrap.fill(f"/-- **The account**: the class lists and {', '.join(apart[:-1]) + ' and ' if len(apart) > 1 else ''}"
                            f"{apart[-1]} partition the user module's sentences. Their concatenation is a permutation "
                            f"of the sentences' indices, which are distinct, so each sentence is in one class or "
                            f"{' or '.join(among)}, and there once. -/", width=100, break_on_hyphens=False,
                            break_long_words=False))
        else:
            w(f"/-- **The account**: the class lists and {' and '.join(apart)} partition the user module's")
            w("sentences. Their concatenation is a permutation of the sentences' indices, which are distinct, so")
            w(f"each sentence is in one class or {' or '.join(among)}, and there once. -/")
        w("theorem account : (classes.flatMap (·.2)" + (" ++ ovlRefuted" if ovl_nc else "") +
          (" ++ tokKItemApart" if tok_omit else "") + (" ++ ovlFnApart" if ovl_fn else "") +
          ").isPerm (userAxioms.map (·.index)) = true ∧")
        w("    (userAxioms.map (·.index)).Nodup := by")
        w("  rw [userAxioms_eq]; decide +kernel")
    elif account_sorted:
        a0, n0 = account_sorted
        w(f"/-- The indices of the user module's sentences, in text order, are {a0}, …, {a0 + n0 - 1}. -/")
        w(f"theorem indices_eq : U.all.map (·.index) = List.range' {a0} {n0} := by decide +kernel")
        w("")
        w(f"/-- The class lists, sorted ({n0.bit_length() + 1} passes of `KoreAML.Distinct.msort`), are the same range. -/")
        w(f"theorem classes_sorted : KoreAML.Distinct.msort {n0.bit_length() + 1} (classes.flatMap (·.2)) = List.range' {a0} {n0} := by")
        w("  decide +kernel")
        w("")
        w("/-- **The account**: the class lists partition the user module's sentences. Their concatenation is")
        w("a permutation of the sentences' indices, which are distinct, so each sentence is in one class and")
        w("in it once: sorted, the class lists are the range the indices are (`tacAccount_of_msort`). -/")
        w("theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧")
        w("    (userAxioms.map (·.index)).Nodup :=")
        w("  tacAccount_of_msort classes_sorted (by rw [userAxioms_eq]; exact indices_eq)")
    else:
        w("/-- **The account**: the class lists partition the user module's sentences. Their concatenation is")
        w("a permutation of the sentences' indices, which are distinct, so each sentence is in one class and")
        w("in it once. -/")
        w("theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧")
        w("    (userAxioms.map (·.index)).Nodup := by")
        w("  rw [userAxioms_eq]; decide +kernel")
    w("")
    w("/-- The class sizes. -/")
    w("theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =")
    w("    [" + ", ".join(f'("{c_}", {len(by_class[c_])})' for c_ in classes_list) + "] := by")
    w("  decide +kernel")
    w("")
    if ovl_any:
        w("/-- The classes are the tie's for a text with a sentence of an overloading symbol (`tieClassesOvl`,")
        w("which gives each its direction), in its order. -/")
        w("theorem account_classes : classes.map (·.1) = tieClassesOvl.map (·.1) := by decide +kernel")
    else:
        w("/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/")
        w("theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel")
    w("")
    if heads_plain and decl_syms:
        # the literal is read by the absent section and by `decl_counts`' parts and the `declsE` ranges:
        # written once, before its first reader, and repeated in each file that reads it
        mark("Head")
        gsym_block(True)
        mark("Account")
    if absent_file:
        mark("Absent")
    if chunk:
        w("/-- The sentence is in the no-direction class exactly where it applies a head Γ lacks. -/")
        w("noncomputable def absentP (ad : AxiomDecl) : Bool :=")
        w('  (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)')
        w("")
        if heads_plain:
            if not decl_syms:
                gsym_block(False)
            w("/-- Γ's subsort pairs (`c.subsorts`, in its order), each sort as the code of the identifier")
            w("`KoreAML.srt` writes for it (`injCodesOf`), written out. -/")
            w("def gInjCodes : List (Nat × Nat) :=")
            w("  [" + wrap_nums([f"({str_code(a)}, {str_code(b)})" for _, (a, b) in head["gHeads"][len(head["gSyms"]):]], 3) + "]")
            w("")
            w("theorem gInjCodes_eq : injCodesOf c = gInjCodes := by decide +kernel")
            w("")
            w("/-- No code of Γ's symbol names holds the byte of `{`, so the decoder reads none of the names as an")
            w("instance (`noInst_of_codes`). -/")
            w("theorem gSymCodes_noInst : gSymCodes.all (fun x => !Faithful.instCoded x) = true := by decide +kernel")
            w("")
            w("/-- `absentP` with Γ's heads read on the codes of its symbol names and subsort pairs (`hasHeadCoded`). -/")
            w("noncomputable def absentPH (ad : AxiomDecl) : Bool :=")
            w('  (classOf "no direction").contains ad.index !=')
            w("    (appHeadsOf ad.ax.pattern).all (hasHeadCoded gSymCodes gInjCodes)")
            w("")
            w("/-- `absentPH` is `absentP`: `gammaHasHead c` is `hasHeadCoded gSymCodes gInjCodes` (`gammaHasHead_coded`). -/")
            w("theorem absentPH_eq : absentPH = absentP := by")
            w("  funext ad; unfold absentPH absentP")
            w("  rw [gammaHasHead_coded gSymCodes_eq gInjCodes_eq gSymCodes_noInst]")
            w("")
        if heads_literal:
            w("/-- The heads at which Γ applies its symbols (`gammaHeads c`), written out. -/")
            w("def gHeads : List (String × List Kore.KSort) :=")
            w("  [" + wrap_nums([head_lit(h) for h in head["gHeads"]], 3) + "]")
            w("")
            w("/-- The literal is Γ's heads. -/")
            w("theorem gHeads_eq : gammaHeads c = gHeads := by decide +kernel")
            w("")
            w("/-- `absentP` with Γ's heads read from the literal `gHeads`. -/")
            w("noncomputable def absentPL (ad : AxiomDecl) : Bool :=")
            w('  (classOf "no direction").contains ad.index !=')
            w("    (appHeadsOf ad.ax.pattern).all (fun h => gHeads.any fun g => decide (g = h))")
            w("")
            w("/-- `absentPL` is `absentP`: `gammaHasHead c` is membership in `gammaHeads c`, which is `gHeads`. -/")
            w("theorem absentPL_eq : absentPL = absentP := by")
            w("  funext ad; unfold absentPL absentP gammaHasHead; rw [gHeads_eq]")
            w("")
        if heads_codes:
            w("/-- Γ's heads (`gHeads`), each name as its code (`KoreAML.Distinct.strCode`), written out. -/")
            w("def gCodes : List (Nat × List Kore.KSort) :=")
            w("  [" + wrap_nums([head_code_lit(h) for h in head["gHeads"]], 3) + "]")
            w("")
            w("/-- The literal is `gHeads` with each name coded. -/")
            w("theorem gCodes_eq : gHeads.map (fun g => (KoreAML.Distinct.strCode g.1, g.2)) = gCodes := by")
            w("  decide +kernel")
            w("")
            w("/-- `absentPL` with each head compared with Γ's by the code of its name (a number), and by its")
            w("sort arguments only where the codes are equal. -/")
            w("noncomputable def absentPC (ad : AxiomDecl) : Bool :=")
            w('  (classOf "no direction").contains ad.index !=')
            w("    (appHeadsOf ad.ax.pattern).all (fun h =>")
            w("      gCodes.any fun g => g.1 == KoreAML.Distinct.strCode h.1 && decide (g.2 = h.2))")
            w("")
            w("/-- Two heads are equal exactly where their names' codes and their sort arguments are")
            w("(`strCode_inj`). -/")
            w("theorem headCode_eq (g h : String × List Kore.KSort) :")
            w("    (KoreAML.Distinct.strCode g.1 == KoreAML.Distinct.strCode h.1 && decide (g.2 = h.2)) = decide (g = h) := by")
            w("  obtain ⟨g1, g2⟩ := g")
            w("  obtain ⟨h1, h2⟩ := h")
            w("  by_cases e : g1 = h1")
            w("  · subst e; simp")
            w("  · have hc : KoreAML.Distinct.strCode g1 ≠ KoreAML.Distinct.strCode h1 :=")
            w("      fun hc => e (KoreAML.Distinct.strCode_inj hc)")
            w("    simp [hc, e]")
            w("")
            w("/-- `absentPC` is `absentPL`: the membership in `gCodes` is the membership in `gHeads`. -/")
            w("theorem absentPC_eq : absentPC = absentPL := by")
            w("  funext ad; unfold absentPC absentPL; rw [← gCodes_eq]")
            w("  simp only [List.any_map, Function.comp_def, headCode_eq]")
            w("")
        thms, body = by_ranges("absentE", "U.all",
                               "absentPH" if heads_plain else "absentPC" if heads_codes else
                               "absentPL" if heads_literal else "absentP",
                               ranges(len(idx), 0, chunk), "tieAll", True)
        w(thms)
        w("")
    w("/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its")
    w("sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one")
    w("Γ lacks. -/")
    w("theorem account_absent : userAxioms.all (fun ad =>")
    w('    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by')
    if chunk and heads_plain:
        w("  rw [userAxioms_eq]")
        w("  have h : (U.all).all absentPH = true :=")
        w("    " + body.replace("\n    ", "\n      "))
        w("  rw [absentPH_eq] at h; exact h")
    elif chunk and heads_codes:
        w("  rw [userAxioms_eq]")
        w("  have h : (U.all).all absentPC = true :=")
        w("    " + body.replace("\n    ", "\n      "))
        w("  rw [absentPC_eq, absentPL_eq] at h; exact h")
    elif chunk and heads_literal:
        w("  rw [userAxioms_eq]")
        w("  have h : (U.all).all absentPL = true :=")
        w("    " + body.replace("\n    ", "\n      "))
        w("  rw [absentPL_eq] at h; exact h")
    elif chunk:
        w("  rw [userAxioms_eq]; exact")
        w("    " + body.replace("\n    ", "\n      "))
    else:
        w("  rw [userAxioms_eq]; decide +kernel")
    w("")
    w("/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,")
    w("so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of")
    w("`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it")
    w("(`gammaHeads`). -/")
    w("theorem absent_closed :")
    w('    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all')
    w("      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=")
    w("  tieAbsent_of_account userAxioms _ _ account_absent")
    w("")
    if abs_proj:
        w("/-- The sentences of the no-direction class that are equations of a projection `project:X` (their")
        w(f"left side applies `{PROJ_PREFIX}X`), each with X. -/")
        w("def absentProj : List (Nat × String) :=")
        w("  [" + wrap_nums([f'({i}, "{x}")' for i, x in abs_proj], 3) + "]")
        w("")
        w("/-- Each sort of `absentProj` is K, KItem or a sort below KItem of Γ, with K and KItem")
        w("constructor sorts. -/")
        w("theorem absent_proj_below_c : absentProj.all (fun p => GenEqs.projBelowB c p.2) = true := by")
        w("  decide +kernel")
        w("")
        if chunk and heads_plain:
            # the first conjunct by the ranges of `account_absent`, each its own decision: one decision
            # over the whole text scans the class once per sentence, all in one reduction
            # `U.all` is the user module's sentences in text order (`userAxioms_eq`), and an `index` is
            # the position in text order (`AxiomDecl.index`), so its j-th member is idx[j]
            pos = {i: j for j, i in enumerate(idx)}
            w("/-- `absent_proj_below`'s filter, named for the ranges below. -/")
            w("noncomputable def absProjP (ad : AxiomDecl) : Bool :=")
            w('  (classOf "no direction").contains ad.index &&')
            w(f'    ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "{PROJ_PREFIX}"')
            w("")
            w("/-- `absent_proj_below`'s map of the sentences. -/")
            w("noncomputable def absProjF (ad : AxiomDecl) : Nat × Option String :=")
            w("  (ad.index, AttrsAgree.eqnHead ad.ax.pattern)")
            w("")
            w("/-- `absent_proj_below`'s map of `absentProj`. -/")
            w("def absProjG (p : Nat × String) : Nat × Option String :=")
            w(f'  (p.1, some ("{PROJ_PREFIX}" ++ p.2))')
            w("")
            w("/-- `absent_proj_below`'s first conjunct range by range of the user module (the ranges of")
            w("`account_absent`), each with the members of `absentProj` in it, joined by `tieFilterMap_range`. -/")
            rs, steps, b = ranges(len(idx), 0, chunk), [], 0
            lp = "(l := U.all) (p := absProjP) (f := absProjF) (m := absentProj) (g := absProjG)"
            for a, ln in rs:
                if ln is None:
                    w(f"theorem absProjE_{a} : (((U.all).drop {a}).filter absProjP).map absProjF =")
                    w(f"    (absentProj.drop {b}).map absProjG := by decide +kernel")
                else:
                    k = sum(1 for i, _ in abs_proj if a <= pos[i] < a + ln)
                    w(f"theorem absProjE_{a} : ((((U.all).drop {a}).take {ln}).filter absProjP).map absProjF =")
                    w(f"    ((absentProj.drop {b}).take {k}).map absProjG := by decide +kernel")
                    steps.append(f"      tieFilterMap_range {lp}\n        (a := {a}) (n := {ln}) (b := {b}) (k := {k}) absProjE_{a} <|")
                    b += k
            w("")
        w("/-- **The projections the no-direction class defines are of sorts below KItem**: `absentProj` is")
        w(f"the list of the no-direction sentences whose left side applies a symbol `{PROJ_PREFIX}X`, each")
        w("with that X, and each such X is K, KItem or a sort below KItem of Γ, with K and KItem constructor")
        w("sorts (`GenEqs.projBelowB`). So the pattern each of these equations is at is functional and")
        w("injective on X in every model of Γ (`GenEqs.projSel_fun`, `GenEqs.projSel_inj`): what the")
        w("equation states of the pattern's symbols, Γ entails. -/")
        w("theorem absent_proj_below (H : HookParams) :")
        w('    (userAxioms.filter (fun ad => (classOf "no direction").contains ad.index &&')
        w(f'        ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "{PROJ_PREFIX}")).map')
        w("      (fun ad => (ad.index, AttrsAgree.eqnHead ad.ax.pattern)) =")
        w(f'      absentProj.map (fun p => (p.1, some ("{PROJ_PREFIX}" ++ p.2))) ∧')
        w("    absentProj.all (fun p => GenEqs.projBelowB (cH H) p.2) = true :=")
        if chunk and heads_plain:
            w("  ⟨by")
            w("    rw [userAxioms_eq]")
            w(f"    exact tieFilterMap_whole {lp} <|")
            for st in steps:
                w(st)
            w(f"      absProjE_{rs[-1][0]},")
            w("    absent_proj_below_c⟩")
        else:
            w("  ⟨by rw [userAxioms_eq]; decide +kernel, absent_proj_below_c⟩")
        w("")
    if absent_file:
        mark("Account")
    w("/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/")
    w("def unmapped : List (Nat × String) :=")
    w("  [" + wrap_nums([f'({i}, "{cls[i]}")' for i in unmapped], 3) + "]")
    w("")
    if user_lem or user_lem_v:
        w("/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of, and")
        w("the user lemmas, of which the tie has no generated theorem: the tie's remainder on this text. -/")
    else:
        w("/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the")
        w("tie's remainder on this text. -/")
    w("def uncovered : List (Nat × String) :=")
    w("  [" + wrap_nums([f'({i}, "{c_}")' for i, c_ in uncovered], 3) + "]")
    w("")
    if lists_by_class:
        listed = [(i, cls[i]) for i in unmapped] + list(uncovered)
        for c_ in classes_list:
            got, it = [i for i, k in listed if k == c_], iter(by_class[c_])
            if not all(any(i == j for j in it) for i in got):
                raise Refused(f"{name}: --lists-by-class: the listed sentences of class {c_!r}, in the order "
                              f"`unmapped ++ uncovered` lists them, are no sublist of the class's indices")
        if any(k not in classes_list for _, k in listed):
            raise Refused(f"{name}: --lists-by-class: a listed sentence's class is no class of the account")
        w("/-- Each listed sentence's class is a class of the account. -/")
        w("theorem lists_classes : (unmapped ++ uncovered).all (fun ic => (classes.map (·.1)).contains ic.2) = true := by")
        w("  decide +kernel")
        w("")
        w("/-- For each class of the account, the listed sentences of it, in their order, are a sublist of its")
        w("indices: one pass over each class's list. -/")
        w("theorem lists_sub : (classes.map (·.1)).all (fun n =>")
        w("    (((unmapped ++ uncovered).filter (·.2 == n)).map (·.1)).isSublist (classOf n)) = true := by")
        w("  decide +kernel")
        w("")
        w("/-- Each listed sentence is in its class in the account (`tieAll_of_groups`). -/")
        w("theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true :=")
        w("  tieAll_of_groups lists_classes lists_sub")
    else:
        w("/-- Each listed sentence is in its class in the account. -/")
        w("theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by")
        w("  decide +kernel")
    w("")
    mark("Attrs")
    w("/-! ## The attributes -/")
    w("")
    if attrs_parts:
        if attrs_blocks:
            w("/-- The conjuncts of `attrsAgree`, each its own decision; `ctors`, `fns` and")
            w(f"`hooks` over the symbol declarations (`symDeclsAt`) by blocks of {attrs_blocks}, `prios` conjunct by")
            w(f"conjunct, each list by blocks of {attrs_blocks} (`decide_cheap`). Each block is a decision with a")
            w("heartbeat budget of its own, and their number is not known here: the theorems set no bound of")
            w("their own (the run's time limit bounds them). -/")
            w("theorem attrs_colls : AttrsAgree.colls kore defn.sem = true := by decide +kernel")
            for cj in ("ctors", "fns", "hooks"):
                w("set_option maxHeartbeats 0 in")
                w(f"theorem attrs_{cj} : AttrsAgree.{cj} kore defn.sem = true := by")
                w(f"  unfold AttrsAgree.{cj}; decide_cheap {attrs_blocks}")
            w("set_option maxHeartbeats 0 in")
            w("theorem attrs_prios : AttrsAgree.prios kore defn = true := by")
            w(f"  unfold AttrsAgree.prios; dsimp only; decide_cheap {attrs_blocks}")
        else:
            w("/-- The conjuncts of `attrsAgree`, each its own decision. -/")
            w("theorem attrs_ctors : AttrsAgree.ctors kore defn.sem = true := by decide +kernel")
            w("theorem attrs_fns : AttrsAgree.fns kore defn.sem = true := by decide +kernel")
            w("theorem attrs_hooks : AttrsAgree.hooks kore defn.sem = true := by decide +kernel")
            w("theorem attrs_colls : AttrsAgree.colls kore defn.sem = true := by decide +kernel")
            w("theorem attrs_prios : AttrsAgree.prios kore defn = true := by decide +kernel")
        w("")
    if law_idx:
        what = law_what(law_idx, raws, sents)
        w(f"/-- The law sentences of the text: {what}. -/")
        w(f"def lawIdx : List Nat := [{il}]")
        w("")
        w("/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,")
        w(f"hooks, collection symbols, priorities. The law sentences (`lawIdx`) are no equations of {', '.join(f'`{x}`' for x in law_fns)}")
        w("(`AttrsAgree.isLaw`, `AttrsAgree.eqnsOf`), so its priorities are those of its equations, which")
        w("`fn_prios` pairs with its clauses. -/")
    elif raw:
        w("/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,")
        if len(raw) == 1:
            w(f"hooks, collection symbols, priorities. The open generator {rnames} is a parameter (`raw`) that no")
        else:
            w(f"hooks, collection symbols, priorities. The open generators {rnames} are parameters (`raw`) that no")
        w("registry hook interprets, declared without `hook` and without `function`, and the text states")
        w("no equation of it (`AttrsAgree.eqnsOf`), which `AttrsAgree.hooks` admits. -/")
    else:
        w("/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,")
        w("hooks, collection symbols, priorities. -/")
    if attrs_parts:
        w("theorem attrs_agree : attrsAgree kore defn = true := by")
        w("  unfold attrsAgree")
        w("  rw [attrs_ctors, attrs_fns, attrs_hooks, attrs_colls, attrs_prios]")
        w("  rfl")
    else:
        w("theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel")
    w("")
    # ---- signature
    mark("Sig")
    w("/-! ## The declarations: `sig_origin` and `decls_entailed`, by ranges -/")
    w("")
    w("/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/")
    w("theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}")
    w("    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :")
    w("    (l.drop a).all p = true := by")
    w("  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl")
    w("")
    w("/-- `p` holds of the whole list where it holds from `0` on. -/")
    w("theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :")
    w("    l.all p = true := h")
    w("")
    w("/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/")
    w("noncomputable def sigFrom (it : Item) : Bool :=")
    w("  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it")
    w("")
    sig_next = head["sigAll"] != "true"
    if sig_next:
        w("/-- Next's arity at the configuration sort, which Γ states whatever the text. -/")
        w("noncomputable def nextItem : Item := KoreAML.nextArityItem [] (srtOf c topCellSort)")
        w("")
        w("/-- No sentence of the text has a `\\rewrites` or a `\\next`, so the text's signature states the")
        w("arity of next at no sort. -/")
        w("theorem text_nextless : kore.axiomDecls.all (fun ad => (nextSortsOf ad.ax.pattern).isEmpty) = true := by")
        w("  decide +kernel")
        w("")
        w("/-- The item has an origin in the text, or is next's arity at the configuration sort. -/")
        w("noncomputable def sigFromN (it : Item) : Bool := sigFrom it || it.pat == nextItem.pat")
        w("")
    pred = "sigFromN" if sig_next else "sigFrom"
    if sig_pos:
        lit = {"t": "text", "s": "regSort", "h": "hook"}
        pos = [f".{lit[k]} {v}" if k in lit else ".next" for k, v in head["sigPos"]]
        sn = "sigFromN, " if sig_next else ""
        w("/-- Where an item of Γ's signature has its origin: the text's signature item at a position, the")
        w("registry sort at a number or the hooked symbol of `hookSigs` at a position whose surplus item it")
        w("is, or next's arity. -/")
        w("inductive TieSigAt")
        w("  | text (j : Nat)")
        w("  | regSort (s : Nat)")
        w("  | hook (j : Nat)")
        w("  | next")
        w("")
        w("/-- The origin of each item of `sigItems c`, in its order. -/")
        w("def sigPos : List TieSigAt :=")
        w("  [" + wrap_nums(pos, 3) + "]")
        w("")
        w(f"theorem sigPos_length : sigPos.length = {len(pos)} := rfl")
        w("")
        w("/-- The item is the one its origin names: one comparison, with the text's item at the position or")
        w("with the surplus item of the registry sort or the hooked symbol (a disjunct of `surplusItem`). -/")
        w("noncomputable def sigFromAt (it : Item) : TieSigAt → Bool")
        w("  | .text j => ((Theory.ofDefinition kore).signature[j]?).any (·.pat == it.pat)")
        w("  | .regSort s => decide (s < nRegSorts) &&")
        w("      (let n := \"Sort\" ++ regSortNames.getD s \"\"")
        w("       !(kore.sortDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&")
        w("         it.pat == (KoreAML.sortConstantItem ⟨n, [], false⟩).pat)")
        w("  | .hook j => (hookSigs[j]?).any fun h =>")
        w("      let n := regSymNames.getD h.name \"\"")
        w("      !(kore.symbolDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&")
        w("        it.pat == (KoreAML.arityItem ⟨n, [], h.args.map regSrtK, regSrtK h.result, false, []⟩).pat")
        w("  | .next => " + ("it.pat == nextItem.pat" if sig_next else "false"))
        w("")
        w("/-- An item with its origin. -/")
        w("noncomputable def sigFromAtP (x : Item × TieSigAt) : Bool := sigFromAt x.1 x.2")
        w("")
        w(f"theorem sigFromAt_sound {{it : Item}} {{p : TieSigAt}} (h : sigFromAt it p = true) : {pred} it = true := by")
        w("  have hs : ∀ {it : Item}, surplusItem kore it = true → " + pred + " it = true := fun h => by")
        w(f"    simp only [{sn}sigFrom, h, Bool.or_true, Bool.true_or]")
        w("  cases p with")
        w("  | text j =>")
        w("    obtain ⟨x, hx, he⟩ := (Option.any_eq_true _ _).mp h")
        w(f"    simp only [{sn}sigFrom, Bool.or_eq_true, List.any_eq_true]")
        w("    exact " + ("Or.inl (Or.inl ⟨x, List.mem_of_getElem? hx, he⟩)" if sig_next else "Or.inl ⟨x, List.mem_of_getElem? hx, he⟩"))
        w("  | regSort s =>")
        w("    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h")
        w("    refine hs ?_")
        w("    unfold surplusItem")
        w("    exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr ⟨s, List.mem_range.mpr (of_decide_eq_true h1), h2⟩))")
        w("  | hook j =>")
        w("    obtain ⟨x, hx, he⟩ := (Option.any_eq_true _ _).mp h")
        w("    refine hs ?_")
        w("    unfold surplusItem")
        w("    exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨x, List.mem_of_getElem? hx, he⟩))")
        w("  | next =>")
        if sig_next:
            w("    simp only [sigFromN, Bool.or_eq_true]")
            w("    exact Or.inr h")
        else:
            w("    exact absurd h Bool.false_ne_true")
        w("")
        w(f"/-- `{pred}` holds of each item where `sigFromAtP` holds of each item with its origin. -/")
        w(pos_join("tieSigPos_all", "TieSigAt", "sigFromAtP", pred, "sigFromAt_sound"))
        w("")
        thms, body = by_ranges("sigE", "(sigItems c).zip sigPos", "sigFromAtP", sig_rs)
        body = "tieSigPos_all (Nat.le_of_eq (sig_sizes.trans sigPos_length.symm)) <|\n    " + body
    else:
        thms, body = by_ranges("sigE", "sigItems c", pred, sig_rs)
    w(thms)
    w("")
    w(f"theorem sig_sizes : (sigItems c).length = {head['nSig']} := by decide +kernel")
    w("")
    if sig_next:
        w("/-- **Every item of Γ's signature but next's arity has its origin**: the item of a declaration of")
        w("the text, or the sort constant of a registry sort or the arity of an interpreted hooked symbol that")
        w("the text does not declare at that shape. Next's arity at the configuration sort has none: the")
        w("text has no rule (`text_nextless`). -/")
        w("theorem sig_origin_but_next : (sigItems c).all (fun it =>")
        w("    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it ||")
        w("      it.pat == nextItem.pat) = true :=")
    else:
        w("/-- **Every item of Γ's signature has its origin**: the item of a declaration of the text, or the")
        w("sort constant of a registry sort or the arity of an interpreted hooked symbol that the text does not")
        w("declare at that shape. -/")
        w("theorem sig_origin : (sigItems c).all (fun it =>")
        w("    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=")
    w("  " + body)
    w("")
    w("kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c")
    w("")
    if decl_syms and not heads_plain:
        # read by `decl_counts`' parts and by the `declsE` ranges, which `--split` may put in two files:
        # repeated in each, as the head's literals are (with --heads-plain written before the absent section)
        mark("Head")
        gsym_block(True)
    mark("Decls")
    w("/-- Γ has a symbol under the name `n`. -/")
    w("noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n")
    w("")
    w("noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)")
    w("noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name")
    w("noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem")
    w("")
    w("/-- The item is one of `sigItems c`, pattern for pattern. -/")
    w("noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)")
    w("")
    if decl_syms:
        w("/-- `hasSym` read from the literal: the code of `n` is one of Γ's names' codes. -/")
        w("noncomputable def hasSymL (n : String) : Bool := gSymCodes.any (· == KoreAML.Distinct.strCode n)")
        w("")
        w("theorem hasSymL_eq : hasSymL = hasSym := by")
        w("  funext n")
        w("  unfold hasSymL hasSym")
        w("  rw [← gSymCodes_eq]")
        w("  simp only [List.any_map, Function.comp_def, symCode_beq]")
        w("")
        w("noncomputable def plainSymsL : List SymbolDecl :=")
        w("  kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSymL sd.name")
        w("noncomputable def declItemsL : List Item := plainSorts.map sortConstantItem ++ plainSymsL.map arityItem")
        w("")
        w("theorem plainSymsL_eq : plainSymsL = plainSyms := by unfold plainSymsL plainSyms; rw [hasSymL_eq]")
        w("theorem declItemsL_eq : declItemsL = declItems := by unfold declItemsL declItems; rw [plainSymsL_eq]")
        w("")
    dparts = [("decl_count_sorts", "kore.sortDecls.length"), ("decl_count_plain_sorts", "plainSorts.length"),
              ("decl_count_syms", "kore.symbolDecls.length"), ("decl_count_plain_syms", "plainSyms.length"),
              ("decl_count_param_syms", "(kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length"),
              ("decl_count_lacked_syms", "(kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length")]
    if decl_parts and split:
        mark("DeclCounts")
    if decl_parts:
        w("/-- The components of `decl_counts`, each its own decision" +
          (" (where they read Γ's symbols, on the literal `gSymCodes`)" if decl_syms else "") + ". -/")
        for (dn, de), dv in zip(dparts, dc):
            rw_ = {"decl_count_plain_syms": "rw [← plainSymsL_eq]; ",
                   "decl_count_lacked_syms": "rw [← hasSymL_eq]; "}.get(dn, "") if decl_syms else ""
            w(f"theorem {dn} : {de} = {dv} := by {rw_}decide +kernel")
        w("")
    w("/-- The declarations of the text: sorts, sorts without parameters, symbols, symbols without")
    w("parameters that Γ has, symbols with parameters, symbols without parameters that Γ lacks. -/")
    w("theorem decl_counts :")
    w("    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,")
    w("      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,")
    w(f"      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = ({', '.join(dc)}) := by")
    if decl_parts:
        w("  rw [" + ", ".join(dn for dn, _ in reversed(dparts)) + "]")
    elif decl_syms:
        w("  rw [← plainSymsL_eq, ← hasSymL_eq]")
        w("  decide +kernel")
    else:
        w("  decide +kernel")
    w("")
    if decl_parts and split:
        mark("Decls")
    dl = "declItemsL" if decl_syms else "declItems"
    if decl_pos:
        n_decl = int(head["nDecl"])
        w("/-- The position in `sigItems c` of each item of `declItems`, in its order. -/")
        w("def declPos : List Nat :=")
        w("  [" + wrap_nums([str(p) for p in head["declPos"]], 3) + "]")
        w("")
        w(f"theorem declPos_length : declPos.length = {n_decl} := rfl")
        w("")
        w(f"theorem decl_sizes : {dl}.length = {n_decl} := by decide +kernel")
        w("")
        w("/-- The item is the one of `sigItems c` at the position: one comparison. -/")
        w("noncomputable def inSigItemsAt (it : Item) (p : Nat) : Bool := ((sigItems c)[p]?).any (·.pat == it.pat)")
        w("")
        w("/-- An item with its position. -/")
        w("noncomputable def inSigItemsAtP (x : Item × Nat) : Bool := inSigItemsAt x.1 x.2")
        w("")
        w("theorem inSigItemsAt_sound {it : Item} {p : Nat} (h : inSigItemsAt it p = true) : inSigItems it = true := by")
        w("  obtain ⟨x, hx, he⟩ := (Option.any_eq_true _ _).mp h")
        w("  unfold inSigItems")
        w("  exact List.any_eq_true.mpr ⟨x, List.mem_of_getElem? hx, he⟩")
        w("")
        w("/-- `inSigItems` holds of each item where `inSigItemsAtP` holds of each item with its position. -/")
        w(pos_join("tieDeclPos_all", "Nat", "inSigItemsAtP", "inSigItems", "inSigItemsAt_sound"))
        w("")
        thms, body = by_ranges("declsE", f"{dl}.zip declPos", "inSigItemsAtP", decl_rs)
        body = "tieDeclPos_all (Nat.le_of_eq (decl_sizes.trans declPos_length.symm)) <|\n    " + body
    else:
        thms, body = by_ranges("declsE", dl, "inSigItems", decl_rs)
    w(thms)
    w("")
    if decl_syms:
        w("theorem decls_in_sig : declItems.all inSigItems = true := by")
        w("  rw [← declItemsL_eq]")
        w("  exact " + body.replace("\n    ", "\n      "))
    else:
        w("theorem decls_in_sig : declItems.all inSigItems = true :=")
        w("  " + body)
    w("")
    w("/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of")
    w("a symbol Γ has, for every H. -/")
    w("theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by")
    w("  intro it hit M _ I hI")
    w("  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit")
    w("  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1")
    w("  rw [← of_decide_eq_true he]")
    w("  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')")
    w("")
    if builtin_decls:
        w("/-- The symbol declarations of the text with a K builtin file's `Source`, without a `hook`")
        w("attribute and without sort parameters, that Γ has, by name. -/")
        w("def builtinDeclNames : List String :=")
        w("  [" + ",\n   ".join('"' + n + '"' for n in builtin_decls) + "]")
        w("")
        w("/-- Each names a symbol of Γ. -/")
        w("theorem builtinDeclNames_has : builtinDeclNames.all hasSym = true := by decide +kernel")
        w("")
        w("/-- **E for the symbol declarations named in `builtinDeclNames`**: Γ entails the G-arity item")
        w("of each such declaration without sort parameters, for every H. -/")
        w("theorem builtin_decls_entailed (H : HookParams) :")
        w("    ∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ builtinDeclNames → Γ (cH H) ⊧ (arityItem sd).pat :=")
        w("  fun sd hsd hp hn => decls_entailed H _ (List.mem_append_right _ (List.mem_map_of_mem")
        w("    (List.mem_filter.mpr ⟨hsd, by")
        w("      simp only [hp, List.isEmpty_nil, Bool.true_and]; exact List.all_eq_true.mp builtinDeclNames_has _ hn⟩)))")
        w("")
    # ---- consistency
    mark("Consistency")
    tp = "[]"
    if raw:
        w("/-! ## Consistency for every H satisfying the open generator's laws -/")
    elif agree:
        w(f"/-! ## Consistency for every H: the agreement of {' and '.join(f'`{x}`' for x in ob['agree_names'])} -/")
    else:
        w("/-! ## Consistency for every H -/")
    w("")
    w(f"def callOrder : List Nat := {call_order}")
    w("")
    w("theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel")
    tpo = "defn.totalParams" if tp_held else tp
    w(f"theorem total_named : c.totalObligationsRP callOrder {tpo} = [] := by decide +kernel")
    if not agree:
        w("theorem agree_named : c.agreeObligationsI = [] := by decide +kernel")
    w("theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel")
    w("")
    of_nil = ["    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)",
              "    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)",
              "    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)",
              "    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)"]
    if raw:
        w("/-- No function's fact is named: under every interpretation that satisfies the open generator's")
        w("laws, `FnFacts` holds. -/")
        w("theorem facts (H : HookParams) (hop : OpenLaws (cH H)) : FnFacts (cH H) callOrder [] :=")
        w("  FnFacts.of_nil_laws")
        w("\n".join(of_nil) + " hop")
        w("")
        w("/-- **Γ with the step's closure has a model, for every H that satisfies the open generator's laws**")
        w("(`OpenLaws`). -/")
        w("theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=")
        w("  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hop)")
        w("")
        vals = " and ".join(f"`{r}` a value at every {'pair' if len(k['args']) == 2 else 'list'} of "
                            f"{k['sort'] if len(set(k['args'])) == 1 and k['args'][0] == k['res'] else 'argument'} values"
                            for k, r, _ in rawd)
        w(f"/-- **`lawHooks c H` satisfies the laws and gives {vals}**,")
        w("for every H; so Γ with the step's closure has a model there. -/")
        w("theorem lawHooks_laws (H : HookParams) :")
        w("    OpenLaws (c.withHooks (lawHooks c H)) ∧ OpenTotal (c.withHooks (lawHooks c H)) :=")
        w("  ⟨openLaws_lawHooks c coreOK H, openTotal_lawHooks c coreOK H⟩")
        w("")
        w("theorem consistent_lawHooks (H : HookParams) : Consistent (c.withHooks (lawHooks c H)) :=")
        w("  consistent (lawHooks c H) (lawHooks_laws H).1")
        w("")
        if no_law and len(raw) == 1:
            w(f"/-- **{rnames} has no law: `OpenLaws` holds under every interpretation.** -/")
            w("theorem openLaws_any (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by")
            w("  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩")
            w("  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'")
            w("  rw [params_raw, List.mem_singleton] at hm")
            w("  simp only [Prod.mk.injEq] at hm")
            w("  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩")
            w("")
            w("/-- **Γ with the step's closure has a model, for every H.** -/")
            w("theorem consistent_any (H : HookParams) : Consistent (cH H) := consistent H (openLaws_any H)")
            w("")
    elif agree:
        al = "[" + ", ".join(map(str, agree)) + "]"
        w("/-- The functions whose agreement no decider confirms, the same under every H. -/")
        w(f"theorem agree_named : c.agreeObligationsI = {al} := by decide +kernel")
        w(f"theorem agree_namedH (H : HookParams) : (cH H).agreeObligationsI = {al} :=")
        w("  (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named")
        w("")
        w("/-- **The owed fact**: under H, the clauses of each function `agree_named` names agree")
        w("(`ClausesAgree`). -/")
        w("def AgreeOwed (H : HookParams) : Prop :=")
        w("  ∀ g ∈ (cH H).agreeObligationsI, ∀ fn, (cH H).lookupFn g = some fn → ClausesAgree (cH H) fn")
        w("")
        w("/-- **The facts the package names hold under every H where the agreement holds** (`FnFacts` at")
        w("the package's `callOrder`). -/")
        w("theorem facts (H : HookParams) (hag : AgreeOwed H) : FnFacts (cH H) callOrder [] :=")
        w("  ⟨fun g hg => by")
        w("    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg")
        w("    exact absurd hg List.not_mem_nil,")
        w("   fun g hg => by")
        w("    rw [Semantics.totalObligationsRP_withHooks _ H _ _, total_named] at hg")
        w("    exact absurd hg List.not_mem_nil,")
        w("   hag,")
        w("   fun p hp => by")
        w("    rw [Det.Semantics.matchObligationsL_withHooks _ H, match_named] at hp")
        w("    exact absurd hp List.not_mem_nil,")
        w("   openLaws_of_plain fun k hk => by")
        w("    simpa using List.all_eq_true.mp (by decide +kernel : c.params.all (fun k => !k.raw) = true) k hk⟩")
        w("")
        w("/-- **Γ with the step's closure has a model, for every H where the agreement holds.** -/")
        w("theorem consistent (H : HookParams) (hag : AgreeOwed H) : Consistent (cH H) :=")
        w("  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hag)")
        w("")
    else:
        if facts_kind == "FnFacts":
            w("theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel")
            w("theorem owed_clauses : c.owedClauses = [] := by decide +kernel")
            w("")
            w("/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/")
            w("theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=")
            w("  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),")
            w("   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩")
            w("")
            w(f"theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder {tpo} :=")
            w("  (FnFacts.of_nil")
            w("\n".join(of_nil))
            w("    (show c.params.all (fun k => !k.raw) = true by decide +kernel)).obligations (openDecidedH H)")
        else:
            w(f"theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder {tpo} :=")
            w("  FnObligations.of_nil")
            w("\n".join(of_nil))
        w("")
        if tp_held:
            w("theorem fnHypH (H : HookParams) (hH : ParamsTotal c defn.totalParams H) : FnHyp (cH H) :=")
            w("  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H hH (obl_nil H)")
            w("")
            w(f"/-- **{'`Γc`' if confined else 'Γ'} with the step's closure has a model, for every H total on the parameters the")
            w("text declares total** (`ParamsTotal`). -/")
            w("theorem consistent (H : HookParams) (hH : ParamsTotal c defn.totalParams H) : Consistent (cH H) :=")
            w("  consistent_of_fnHyp _ (coreOKH H) (fnHypH H hH)")
            w("")
            w("/-- A value of the result sort of the parameters the text declares total, exhibited by the")
            w("search over the definition's data (`Parse.exhibit?`). -/")
            w("noncomputable def totalWitnessV : GroundTerm :=")
            w("  ((c.params.find? fun k => defn.totalParams.contains k.sig.name).bind fun k =>")
            w("    Parse.exhibit? c k.sig.result).getD default")
            w("")
            w("/-- **The hypothesis is met**: the interpretation answering `totalWitnessV` everywhere is total on")
            w("the parameters the text declares total. -/")
            w("theorem paramsTotal_witness : ParamsTotal c defn.totalParams (ParamSchema.constH totalWitnessV) :=")
            w("  ParamSchema.paramsTotal_constH (by decide +kernel)")
            w("")
            w("theorem consistent_witness : Consistent (cH (ParamSchema.constH totalWitnessV)) :=")
            w("  consistent _ paramsTotal_witness")
            w("")
        else:
            w("theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H")
            w("  ParamsTotal.nil (obl_nil H)")
            w("")
            w(f"/-- **{'`Γc`' if confined else 'Γ'} with the step's closure has a model, for every H.** -/")
            w("theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)")
            w("")
    if fnfun_gen:
        w(fnfun_section_fnhyp(fnfun_idx, fnfun_user) if fnfun_fh else fnfun_section(fnfun_idx, fnfun_chunk))
    mark("Fns")
    if fn_align:
        w(alpha_block())
    w("/-! ## Γ under every interpretation reads the same equations and rules -/")
    w("")
    w("kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c")
    w("kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c")
    w("")
    w("theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))")
    w("")
    if fn_align:
        w(fn_align_section(fn_text, fn_nonlit))
    if fn_full:
        w(f"/-! ## Function equations ({len(fn_user)} sentences"
          + (f", and {numword(len(fn_pre))} of the prelude" if fn_pre else "") + ") -/")
        w("")
        w("/-- The axioms of Γ's equations, in `fnItems`'s order. -/")
        w("noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=")
        w("  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun")
        w("    | .axiom a => some a")
        w("    | _ => none")
        w("")
        w('theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl')
        w("")
        w(f"/-- The text sentences of Γ's {len(fn_text)} equations, in `fnItems`'s order. -/")
        w("noncomputable def fnText : List AxiomDecl :=")
        w("  " + ax_list(fn_text, pre={i: pre_mods[m] for i, m in fn_pre.items()}))
        w("")
        # the heartbeats of each block's decision count in the theorem's budget: each of the K + 1
        # decisions gets the budget of the single one
        w(f"set_option maxHeartbeats {1000000 * (nfn // fn_blocks + 1) if fn_blocks else 1000000} in")
        if fn_blocks:
            w("/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (a kernel")
            w(f"decision per block of {fn_blocks} equations, each with the budget of the single one). -/")
        else:
            w("/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel")
            w("decision). -/")
        w("theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by")
        w("  rw [fnItems_eq, List.map_map]")
        w(f"  exact (by decide_map_blocks {fn_blocks} {nfn // fn_blocks} :" if fn_blocks else "  exact (by decide +kernel :")
        w('    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))')
        w("")
        if fn_pre:
            for m, pn in pre_mods.items():
                w(f"/-- The axioms of the prelude module {m}, in text order. -/")
                w(f'theorem {pn[:1].lower() + pn[1:]}_eq : kore.axiomDecls.filter (·.module == "{m}") = {pn}.all := by kernel_rfl')
                w("")
            w("/-- **`fnText`'s user-module sentences are the account's function-equation class**: the same")
            w("indices, each once; its other sentences are the prelude's, which no user sentence is. -/")
            w("theorem fns_account :")
            w(f'    (classOf "function equation").isPerm ((fnText.filter (·.module == "{um}")).map (·.index)) = true ∧')
            w(f'    (fnText.filter (·.module != "{um}")).map (fun ad => (ad.index, ad.module)) =')
            w("      [" + ", ".join(f'({i}, "{fn_pre[i]}")' for i in fn_text if i in fn_pre) + "] := by decide +kernel")
        else:
            w("/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/")
            w('theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel')
        w("")
        w("/-- **E for the equations**: Γ entails each, for every H. -/")
        w("theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by")
        w("    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩")
        w("  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem")
        w("  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))")
        w("")
        w("/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/")
        w("theorem fns_from_text (H : HookParams) :")
        w("    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →")
        w("      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by")
        w("  intro j it hj")
        w("  rw [fnItems_withHooks] at hj")
        w("  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl")
        w("  rw [fn_shape, List.getElem?_map] at h1")
        w("  cases hf : fnText[j]? with")
        w("  | none => rw [hf] at h1; cases h1")
        w("  | some ad =>")
        w("    rw [hf] at h1")
        w("    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩")
        w("    have he : (trS ad).pat = it.pat := Option.some.inj h1")
        w("    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)")
        w("")
        w("/-- The priority each function sentence's attributes state is the priority of the clause whose")
        w("item is the sentence's translation, item by item in `fnItems`'s order. -/")
        w("theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =")
        w("    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel")
        w("")
    mark("Rules")
    if rules_full and nrules:
        w(ens_section("/-! ## The rule (sentence 155): W1 -/", "noncomputable def r0 : Rule").replace(
            "/-! ## The rule (sentence 155): W1 -/", f"/-! ## The rules ({nrules} sentences): W1 -/"))
        for j, i in rule_map:
            w(f"noncomputable def r{j} : Rule := c.rules[{j}]'(by decide +kernel)")
        w("")
        w("theorem ruleItems_eq : ruleItems c = [" + ",\n    ".join(
            f"trAxiom [] [] (kAx (prioRuleK c r{j}))" for j, _ in rule_map) + "] := by kernel_rfl")
        w("")
        w("/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/")
        w("noncomputable def ruleText : List AxiomDecl :=")
        w("  " + ax_list(rule_text))
        w("")
        w("/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/")
        w('theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel')
        w("")
        if comp_map:
            w(RULE_COMP_SECTION)
            w("/-- The priority each rule sentence's attributes state is its rule's priority, in `ruleItems`'")
            w("order: the competitors of a rule (the rules of a smaller priority, whose `applies` Γ's item")
            w("negates) are the rules whose sentences state a smaller priority. -/")
            w("theorem rule_prios : ruleText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) = c.rules.map (·.prio) := by")
            w("  decide +kernel")
            w("")
        comp_js = {j for j, _ in comp_map}
        for j, i in rule_map:
            if j in comp_js:
                w(f"theorem rule{j}_parts : (ruleCompParts (prioRuleK c r{j})).isSome = true := by decide +kernel")
                w(f"/-- Γ's item of rule {j} without its premises `¬ ⋁ competitors` and `⌈rhs ∧ ens⌉` is the text's")
                w(f"sentence {i}. -/")
                w(f"theorem rule{j}_text : (trS U.ax{i}).pat = minusComp (prioRuleK c r{j}) := by decide +kernel")
                w(f"/-- **W1 for rule {j}**: Γ's item is a consequence of sentence {i}. -/")
                w(f"theorem rule{j}_from_text : itemsPremises [trS U.ax{i}] ⊧ (trAxiom [] [] (kAx (prioRuleK c r{j}))).pat := by")
                w("  intro M _ I hI")
                w("  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)")
                w(f"  refine item_of_minusComp hD ?_")
                w(f"  rw [← rule{j}_text]")
                w(f"  exact hI _ (Or.inl ⟨trS U.ax{i}, List.mem_singleton_self _, rfl⟩)")
                w("")
                continue
            w(f"theorem rule{j}_parts : (ruleParts (prioRuleK c r{j})).isSome = true := by decide +kernel")
            w(f"theorem rule{j}_table : tableOf [] (prioRuleK c r{j}) = tableOf [] (dropThird (prioRuleK c r{j})) := by decide +kernel")
            w(f"theorem rule{j}_free : (freeOf [] (prioRuleK c r{j})).eraseDups = (freeOf [] (dropThird (prioRuleK c r{j}))).eraseDups := by")
            w("  decide +kernel")
            w(f"/-- Γ's item of rule {j} without its premise `⌈rhs ∧ ens⌉` is the text's sentence {i}. -/")
            w(f"theorem rule{j}_text : (trS U.ax{i}).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r{j})))).pat := by decide +kernel")
            w(f"/-- **W1 for rule {j}**: Γ's item is a consequence of sentence {i}. -/")
            w(f"theorem rule{j}_from_text : itemsPremises [trS U.ax{i}] ⊧ (trAxiom [] [] (kAx (prioRuleK c r{j}))).pat := by")
            w("  intro M _ I hI")
            w("  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)")
            w(f"  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule{j}_parts")
            w("  obtain ⟨C, l, t, x, r⟩ := q")
            w(f"  refine rewrite_weaken hD hq rule{j}_table rule{j}_free ?_")
            w(f"  rw [← rule{j}_text]")
            w(f"  exact hI _ (Or.inl ⟨trS U.ax{i}, List.mem_singleton_self _, rfl⟩)")
            w("")
        w("set_option maxHeartbeats 4000000 in")
        w("/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a")
        w("consequence of a text sentence of `ruleText`, for every H. -/")
        w("theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by")
        w("  intro it hit")
        w("  rw [ruleItems_withHooks, ruleItems_eq] at hit")
        w("  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit")
        w("  rcases hit with " + " | ".join(["rfl"] * nrules))
        for k, (j, i) in enumerate(rule_map):
            mem = "List.mem_cons_self"
            for _ in range(k):
                mem = f"List.mem_cons_of_mem _ ({mem})"
            w(f"  · exact ⟨U.ax{i}, {mem}, rule{j}_from_text⟩")
        w("")
    # ---- no junk
    mark("NoJunk")
    w("/-! ## No junk -/")
    w("")
    if nj_triv:
        w("/-- `\\or{S}(\\top{S}(), \\bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/")
        w("def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)")
        w("")
        w("theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}")
        w("    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by")
        w("  intro e m")
        w("  unfold orTopBot")
        w("  rw [interpret_impl]")
        w("  intro _")
        w("  rw [interp_equal hD]")
        w("  intro a")
        w("  rw [interp_sOr, interp_sTop hD hS]")
        w("  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩")
        w("")
        for i, s in nj_triv:
            w(f'theorem nj{i} : (trS U.ax{i}).pat = orTopBot (sym (.sort "{s}")) := by decide +kernel')
        w("")
        w("/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by")
        w("Γ for every H. -/")
        w("theorem nojunk_trivial_entailed (H : HookParams) :")
        w(f"    ∀ ad ∈ {ax_list([i for i, _ in nj_triv], 6)}, Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  have hD := defOK hI")
        w("  simp only [List.mem_cons, List.not_mem_nil, or_false] at had")
        w("  rcases had with " + " | ".join(["rfl"] * len(nj_triv)))
        for i, _ in nj_triv:
            w(f"  · rw [nj{i}]; exact orTopBot_valid hD rfl")
        w("")
    nj_big = [i for i, e in nj_sorts if nojunk_blocks and e["ngens"] > nojunk_blocks]
    if (nojunk_eq and nj_items) or (nojunk_blocks and nj_kitem) or nj_big:
        w(NJ_ALIAS.replace("@ALIASES@", ", ".join(lean_str(a) for a in head["aliases"])))
    if (nojunk_blocks and nj_kitem) or nj_big:
        w(NJ_TR)
    if nj_items and nojunk_eq:
        miss = [i for i in nj_items if not head["njEq"].get(i)]
        if miss:
            raise Refused(f"{name}: --nojunk-eq: the no-junk sentences {miss} are constructor items of Γ but the probe "
                          f"finds no sort whose item over `Semantics.gens` they are")
        w("/-- The no-junk sentences that are Γ's constructor items, each with the sort whose no-junk item")
        w("over `Semantics.gens` it is. -/")
        w("noncomputable def njEq : List (AxiomDecl × Srt) :=")
        w("  [" + wrap_nums([f"(U.ax{i}, {head['njEq'][i][0][0]})" for i in nj_items], 3) + "]")
        w("")
        w("/-- The sentence `p.1` translates (with the alias names written out) to the no-junk item of the sort")
        w("`p.2` over `Semantics.gens`, and `p.2` is a constructor sort with generators. -/")
        w("noncomputable def njEqB (p : AxiomDecl × Srt) : Bool :=")
        w("  decide ((trAxiom kore.symbolDecls aliasLit p.1).pat =")
        w("      (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat) &&")
        w("    decide (p.2 ∈ consSorts c) && !(c.gens p.2).isEmpty")
        w("")
        if chunk and len(nj_items) > chunk:
            thms, body = by_ranges("njEqE", "njEq", "njEqB", ranges(len(nj_items), 0, chunk), "tieAll", True)
            w(thms)
            w("theorem njEq_all : njEq.all njEqB = true :=")
            w("  " + body)
        else:
            w("theorem njEq_all : njEq.all njEqB = true := by decide +kernel")
        w("")
        w("/-- A sentence `njEqB` holds of is Γ's no-junk item of its sort, an item of `consItemsK c`")
        w("(`tnjItem_any_of_eq`). -/")
        w("theorem njEq_any {l : List (AxiomDecl × Srt)} (h : l.all njEqB = true) :")
        w("    ∀ ad ∈ l.map (·.1), (consItemsK c).any (·.pat == (trS ad).pat) = true := by")
        w("  intro ad had")
        w("  obtain ⟨⟨ad', N⟩, hm, rfl⟩ := List.mem_map.mp had")
        w("  have hb := List.all_eq_true.mp h _ hm")
        w("  simp only [njEqB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hb")
        w("  obtain ⟨⟨he, hN⟩, hg⟩ := hb")
        w("  rw [← aliasLit_eq] at he")
        w("  exact tnjItem_any_of_eq hN hg he")
        w("")
        w("/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of")
        w("one of Γ's constructor items, its sort's no-junk item (`njEq_any`). -/")
        w(f"theorem nojunk_items : ∀ ad ∈ {ax_list(nj_items, 6)},")
        w("    (consItemsK c).any (·.pat == (trS ad).pat) = true :=")
        w("  njEq_any njEq_all")
        w("")
    elif nj_items:
        w("set_option maxHeartbeats 1000000 in")
        w("/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of")
        w("one of Γ's constructor items. -/")
        w(f"theorem nojunk_items : ∀ ad ∈ {ax_list(nj_items, 6)},")
        w("    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel")
        w("")
    if nj_items:
        w("kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c")
        w("")
        w("/-- **E for those**: Γ entails each, for every H. -/")
        w(f"theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ {ax_list(nj_items, 6)},")
        w("    Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)")
        w("  rw [← of_decide_eq_true he]")
        w("  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)")
        w("")
    for i in nj_kitem:
        w("/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same")
        w("generators as `Semantics.gens` lists, in another order. -/")
        gk = "((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))"
        if nojunk_blocks:
            tabs = (head["tabT"].get(i), head["tabI"])
            if not tabs[0] or not tabs[1] or not head["kGens"] or \
                    any(k[2] == "?" for k in tabs[0] + tabs[1] if k[0] != "S"):
                raise Refused(f"{name}: --nojunk-blocks: the probe gives no table of KItem's no-junk sentence "
                              f"{i} or of its item, or a variable of a sort that is no sort constructor "
                              f"without arguments")
            kn = lean_str(head["kitemName"])
            w(f"theorem nojunk_kitem_name : c.sortName Srt.kitem = {kn} := by decide +kernel")
            w("")
            w("/-- KItem's generators in the text's order (`gensInOrder`), written out. -/")
            w("def nojunk_kitem_gens : List KoreAML.Gen :=")
            w("  [" + wrap_nums([gen_lit(g) for g in head["kGens"]], 3) + "]")
            w(f"theorem nojunk_kitem_gens_eq : {gk} = nojunk_kitem_gens := by decide +kernel")
            w("")
            thms, proof = nj_blocks("nojunk_kitem", i, kn, "nojunk_kitem_gens", len(head["kGens"]) + 1,
                                    nojunk_blocks, tabs)
            w(thms)
        w(f"theorem nojunk_kitem_order : (trS U.ax{i}).pat =")
        w(f"    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) {gk}).pat := by")
        if nojunk_blocks:
            w("  rw [nojunk_kitem_name, nojunk_kitem_gens_eq]")
            w(proof)
        else:
            w("  decide +kernel")
        w("theorem nojunk_kitem_members :")
        w("    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by")
        w("  decide +kernel")
        w("")
        w(f"/-- **E for KItem's no junk ({i})**, for every H (`noJunkItem_of_subset`). -/")
        w(f"theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by")
        w("  intro M _ I hI")
        w("  rw [nojunk_kitem_order]")
        w("  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))")
        w("    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_")
        w("  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)")
        w("    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)")
        w("")
    nj_names = []
    for i, e in nj_sorts:
        sec, nn = nojunk_sort_section(i, e, sn, rawd, e["srt"] in nj_sort_new, nojunk_blocks if i in nj_big else 0)
        w(sec)
        nj_names += nn
    # ---- cons
    mark("Cons")
    if cons_text:
        w("/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/")
        w("")
        dec = "tchConsB" if cons_head else "tieConsB"
        w(f"/-- The constructor sentences `{dec}` decides, in text order. -/")
        w("noncomputable def consText : List AxiomDecl :=")
        w("  " + ax_list(cons_text))
        w("")
        checked = "cons_checked_hd" if cons_head else "cons_checked"
        if chunk and len(cons_text) > chunk:
            thms, body = by_ranges("consE", "consText", f"(fun ad => {dec} c ad.ax)", ranges(len(cons_text), 0, chunk), "tieAll", True)
            w(thms)
            w(f"theorem {checked} : consText.all (fun ad => {dec} c ad.ax) = true :=")
            w("  " + body)
        else:
            w(f"theorem {checked} : consText.all (fun ad => {dec} c ad.ax) = true := by decide +kernel")
        if cons_head:
            w("")
            w("theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := tchConsB_all cons_checked_hd")
        w("")
        if chunk and len(cons_text) > chunk:
            pr = "(fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))"
            thms, body = by_ranges("consT", "consText", pr, ranges(len(cons_text), 0, chunk), "tieAll", True)
            w(thms)
            w(f"theorem cons_trS : consText.all {pr} = true :=")
            w("  " + body)
        else:
            w("theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by")
            w("  decide +kernel")
        w("")
        w("/-- **E for the constructor sentences**: Γ entails each, for every H. -/")
        w("theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]")
        w("  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)")
        w("  exact tieCons_entailed (c := cH H) (a := ad.ax)")
        w("    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI")
        w("")
    # ---- idem
    mark("Rest")
    if ovl_eq:
        w(ovl_eq_section(ovl_eq))
    if ovl_nc:
        w(ovl_nc_section(ovl_nc))
    if tok_omit:
        w(tok_omit_section(tok_omit[0], tok_sorts))
    if ovl_fn:
        w(ovl_fn_section(ovl_fn, ovl_fn_rows, ovl_fn_gens))
        w(HAND_SECTIONS["ovlfn"] + " (by hand) -/")
        w("")
        if ovl_fn_hand["refuted"]:
            w(ovl_fn_refuted_section())
    if idem is not None:
        sec = ens_section("/-! ## Set idempotence (61): refuted -/", "/-! ## Consistency for every H -/",
                          IDEM_DROP).replace("@I@", str(idem))
        if raw:
            for a, b in IDEM_RAW:
                if a not in sec:
                    raise Refused(f"test/TieEns.lean has changed: no {a[:60]!r} in its idempotence section")
                sec = sec.replace(a, b)
        w(sec)
    if own_idem:
        w(own_idem_section(own_idem))
    if lib166 is not None:
        w(ens_section("/-! ## Library sample: sentence 166", "/-! ## Symbols the text's sentences apply").replace("@I@", str(lib166)))
        w(ens_section("theorem shapesOK_c", "/-- The symbols the rule's sentence applies. -/").replace("@I@", str(lib166)))
    if law_idx:
        w(law_section(law_idx))
    if open_law:
        w(openlaw_section(open_law, rnames, need_rfl=not nj_items))
    if open_fun:
        w(open_functional_section(open_fun, rnames))
    if param_fun:
        w(param_functional_section(param_fun, total_names, len(idx), chunk))
    if param_lem:
        w(param_lemma_section(param_lem, reads_h))
    if user_lem or user_lem_v:
        w(user_lemma_section(user_lem, user_lem_v))
    if fn_pair:
        mark("Fns")
        wi = pair_text[pair_w]
        w(pair_section(pair_w, wi, sents[wi]["prio"], "non-executable{}()" in raws.get(wi, ""),
                       len(by_class["function equation"])))
        mark("Rest")
    if fn_pairs:
        mark("Fns")
        w(pairs_section([(j, pair_text[j], sents[pair_text[j]]["prio"]) for j in pair_ws],
                        [(j, pair_text[j]) for j in pair_ac], len(by_class["function equation"]),
                        len(by_class["priority equation"])))
        mark("Rest")
    if fn_rds:
        mark("Fns")
        w(readings_section([(j, pair_text[j], sents[pair_text[j]]["prio"]) for j in pair_ws],
                           [(j, pair_text[j]) for j in pair_ac], [(j, pair_text[j]) for j in pair_rd],
                           [(j, pair_text[j]) for j in pair_un], len(by_class["function equation"]),
                           len(by_class["priority equation"]), pair_cut_l, confined))
        mark("Rest")
    if gamma:
        w(GAMMA_ALIGN if fn_align else GAMMA_RULES if nrules else GAMMA)
    cnames = []
    if confined:
        sec, cnames = gamma_c_section(gamma, fn_align, nrules, fn_any, nj_triv, nj_items, nj_kitem, cons_text, idem,
                                      own_idem, ovl_eq, ovl_nc, tok_omit, tok_sorts, ovl_fn, ovl_fn_rows)
        w(sec)
    w(f"end KCore.{ns}")
    w("")
    names = ["params_raw" if raw else "noRaw", "readsConfined_c", "userAxioms_eq", "coreOK"] + (["wf_defn"] if wf_ok else []) + \
        ["account", "account_sizes", "account_classes", "account_absent", "absent_closed"] + \
        (["absent_proj_below_c", "absent_proj_below"] if abs_proj else []) + ["lists_in_account"] + \
        ["attrs_agree"] + (["decl_counts"] if decl_parts else []) + \
        ["sig_origin_but_next" if head["sigAll"] != "true" else "sig_origin", "decls_entailed",
         "consistent"] + (["text_nextless"] if head["sigAll"] != "true" else []) + \
        (["builtin_decls_entailed"] if builtin_decls else [])
    if fn_full:
        names += [n[:1].lower() + n[1:] + "_eq" for n in pre_mods.values()]
        names += ["fn_shape", "fns_account", "fns_entailed", "fns_from_text", "fn_prios"]
    if nj_triv:
        names.append("nojunk_trivial_entailed")
    if nj_items:
        names.append("nojunk_items_entailed")
    if nj_kitem:
        names.append("nojunk_kitem_entailed")
    if cons_text:
        names.append("cons_entailed")
    if ovl_eq:
        names += ["ovleq_account", "ovleq_entailed"]
    if ovl_nc:
        names += ["ovlnc_index", "ovlnc_refuted"]
    if tok_omit:
        names += ["tokkitem_index", "tokkitem_sorts_named", "tokkitem_sub", "tokkitem_text", "tokkitem_ok",
                  "tokkitem_entails_item", "tokkitem_item_in_gamma", "tokkitem_holds_iff_empty"]
        names += (["tokkitem_exhibit", "tokkitem_refuted"] if any(e["valued"] for e in tok_sorts) else
                  ["tokkitem_nonempty_in_text", "tokkitem_refuted_with_nonempty"])
    if ovl_fn:
        names += ["ovlfn_index"] + [f"ovlfn_{n}_{i}" for i in ovl_fn for n in ("text", "item_in_gamma", "entails_item")]
        names += ovl_fn_hand["names"] + (["ovlfn_refuted_sub"] if ovl_fn_hand["refuted"] else [])
    if rules_full and nrules:
        names += ["rules_account", "rule_from_text"]
    if comp_map:
        names += ["rule_prios"]
    if idem is not None:
        names.append("idem_refuted")
    names += [f"own_idem_refuted_{i}" for i, _, _ in own_idem]
    if lib166 is not None:
        names += ["lib166", "lib166_at_values"]
    if gamma and not fn_align:
        names += ["gamma_origin", "gamma_from"]
    after = []
    if held_total:
        after += (["held_named"] if ob.get("held") else []) + (["total_named"] if ob.get("total") else []) + \
            (["fnHypH"] if fnhyp_hand else []) + (["not_fnHypH"] if notfnhyp_hand else []) + \
            (["fnFun_indices", "fnFun_account", "fnFun_checked", "fnFun_trS", "fnFun_at_values",
              "fnFun_at_values_step"] if fnfun_hand else [])
    elif agree:
        after += ["agree_named"] + (["agree"] if "consistency" in hand else []) + ["facts"]
    if fnfun_gen:
        after += ["fnFun_indices", "fnFun_account", "fnFun_checked", "fnFun_trS", "fnFun_at_values",
                  "fnFun_at_values_step"]
    if tp_held:
        after += ["total_named", "paramsTotal_witness", "consistent_witness"]
    if fn_align:
        after += ["fn_shape_but_owise", "owise_not_literal", "fn_align", "fns_account", "fns_entailed",
                  "fns_from_text", "fn_prios"] + (["gamma_origin", "gamma_from"] if gamma else [])
    k = names.index("consistent") + 1
    names[k:k] = after
    if law_idx:
        names += ["law_indices", "law_text", "law_not_item", "law_account"]
    if raw:
        names += ["names", "facts", "lawHooks_laws", "consistent_lawHooks"] + (["openLaws_any", "consistent_any"] if no_law and len(raw) == 1 else [])
    names += nj_names
    if open_law:
        names += ["openlaw_item", "openlaw_cons", "openlaw_entailed", "openlaw_account"]
    if open_fun:
        names.append("open_functional_not_item")
    if param_fun:
        names += ["total_params", "paramfunctional_account", "paramfunctional_heads"]
    if param_lem:
        names += ["paramlemma_account", "paramlemma_heads"] + (["paramlemma_reads_h"] if reads_h else []) + \
            ["ParamLemmaWitnessAtValues"]
    if user_lem or user_lem_v:
        names += ["userlemma_account", "UserLemmaEntailed", "UserLemmaAtValues"]
    if facts_kind == "FnFacts" and not agree and not raw and not held_total:
        names += ["owed_rules", "owed_clauses", "openDecidedH"]
    names += cnames
    pair_names = ["fns_account", "aW_narrowed", "w_text", "w_differs", "w1", "shape", "fns_entailed",
                  "fns_from_text", "fn_prios", "gamma_from"] if fn_pair else []
    if fn_pairs:
        pair_names = ["fns_account"] + [n.format(j) for j in pair_ws for n in
                                        ("prio{}_narrowed", "prio{}_text", "prio{}_differs", "prio{}_w1")] + \
            [n.format(j) for j in pair_ac for n in ("ac{}_same", "ac{}_differs", "ac{}_iff", "ac{}_entailed")] + \
            ["shape", "fns_entailed", "fns_from_text", "fn_prios", "gamma_from"]
    if fn_rds:
        pair_names = readings_names(pair_ws, pair_ac, pair_rd, pair_un, pair_cut_l)
    for block in (names, pair_names):
        for n in block:
            w(f"#check @KCore.{ns}.{n}")
        for n in block:
            w(f"#print axioms KCore.{ns}.{n}")
    blocks = (names, pair_names)
    names = names + pair_names
    offs = [0]
    for x in L:
        offs.append(offs[-1] + len(x) + 1)
    marks = [(offs[k], m) for k, m in marks]
    lean = "\n".join(L) + "\n"
    for sec, text in hand.items():
        start = HAND_SECTIONS[sec]
        a = lean.index("\n" + start) + 1
        b = (lean.index("\n/-! ## ", a) if "\n/-! ## " in lean[a:] else lean.index("\nend KCore.", a)) + 1
        new = text.rstrip("\n") + "\n\n"
        if split and any(a < o < b for o, _ in marks):
            raise Refused(f"{name}: --split: a section starts inside the hand-written {sec} section")
        marks = [(o if o <= a else o + len(new) - (b - a), m) for o, m in marks]
        lean = lean[:a] + new + lean[b:]
    owed = ([f"the agreement of {', '.join(ob['agree_names'])} (AgreeOwed)"] if agree and "consistency" not in hand else [])
    if held_total and not fnhyp_hand and not fnfun_any:
        owed.append("FnHyp, the hypothesis the function functional sentences are owed under (not stated: the "
                    "consistency section shows `consistent` without it)")
    if param_lem:
        owed.append(f"one H at which FnHyp holds and the parameter lemmas {', '.join(map(str, param_lem))} "
                    f"hold at values (ParamLemmaWitnessAtValues)")
    if user_lem:
        owed.append(f"Γ entails the user lemmas {', '.join(map(str, user_lem))} for every H (UserLemmaEntailed)")
    if user_lem_v:
        owed.append(f"the user lemmas {', '.join(map(str, user_lem_v))} hold at values for every H (UserLemmaAtValues)")
    if ovl_fn_hand.get("hypothesis"):
        owed.append(f"the sentence{'s' if len(ovl_fn_hand['hypothesis']) > 1 else ''} "
                    f"{', '.join(map(str, ovl_fn_hand['hypothesis']))} of a function-overloaded symbol "
                    f"at covered arguments, under the hypotheses on H the hand section names (OvlFnHyp<i>)")
    cut_not = [i for _, i, k in pair_cut_l if k["kind"] == "notCond"]
    if cut_not:
        owed.append(f"Bool closed in the model (`boolClosed`), a premise of the sentence{'s' if len(cut_not) > 1 else ''} "
                    f"{', '.join(map(str, cut_not))} read through `notAsCondition` (cut<j>_iff, cut<j>_entailed)")
    summary = dict(fixture=name, sentences=len(idx), mapped=len(mapped), unmapped=len(unmapped),
                   classes={c_: len(by_class[c_]) for c_ in classes_list}, fn_full=fn_full, fn_prelude=sorted(fn_pre), fn_align=fn_align,
                   fn_pair=fn_pair, **({"fn_pairs": dict(w1=pair_ws, ac=pair_ac)} if fn_pairs else {}),
                   **({"fn_readings": dict(w1=pair_ws, ac=pair_ac, or_empty=pair_rd, untied=pair_un,
                                           **({"cut": {j: dict(sentence=i, **k) for j, i, k in pair_cut_l}}
                                              if pair_cut_l else {}))} if fn_rds else {}),
                   cons=len(cons_text), nojunk=[len(nj_triv), len(nj_items), len(nj_kitem), len(nj_sorts)],
                   idem=idem, own_idem=[i for i, _, _ in own_idem], lib166=lib166, gamma=gamma, laws=law_idx, open_generators=[k["name"] for k in raw],
                   confined=confined, uncovered=uncovered, owed=owed, theorems=names,
                   **({"tok_kitem_apart": dict(sentence=tok_omit[0], sorts=[e["sort"] for e in tok_sorts],
                                               valued=[e["sort"] for e in tok_sorts if e["valued"]])}
                      if tok_omit else {}),
                   **({"ovl_fn_apart": dict(sentences=ovl_fn, kinds={i: ovl_fn_rows[i]["kind"] for i in ovl_fn},
                                            joint={i: ovl_fn_rows[i]["jf"] for i in ovl_fn if ovl_fn_rows[i]["jf"] != i},
                                            at_values=ovl_fn_hand["at_values"], refuted=ovl_fn_hand["refuted"],
                                            hypothesis=ovl_fn_hand["hypothesis"])}
                      if ovl_fn else {}),
                   law_search=[dict(law=law_idx[r["j"]], searched=r["searched"], valuations=r["tried"], refuted=False)
                               for r in head["lawRef"]])
    if split:
        summary["split_files"], summary["split"] = split_tie(ns, lean, marks, text_rel, cmd, blocks)
    return ns, lean, summary


# the files of `--split` beside the first, in this order; a file holds the sections `generate` marks
# with its name (`mark`), and the declarations of the later sections that read their decisions
SPLIT_PARTS = ["Attrs", "Sig", "Decls", "Fns", "Rules", "NoJunk", "Cons", "Absent", "DeclCounts"]
# the marks of the first file: `Head` and `Consistency` may be repeated where a part reads them, the
# account's decisions may not, `Rest` (the sections after the constructors) follows what it reads
SPLIT_FIRST = ["Head", "Account", "Consistency", "Rest"]
SPLIT_DECL = re.compile(r"(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                        r"(theorem|lemma|def|abbrev|instance|kernel_rfl|inductive)\s+([^\s:({\[]+)")
SPLIT_DECIDES = re.compile(r"\bdecide(?:_cheap\b|_map_blocks\b|_all_blocks\b|\s*\+kernel\b)|\bby\s+decide\b")
SPLIT_IDENT = re.compile(r"(?<![\w'.!?])([^\W\d][\w'!?]*)")


def split_depth(line):
    """The brackets the line opens and does not close (strings and `--` comments dropped)."""
    t = re.sub(r"--.*", "", re.sub(r'"(?:[^"\\]|\\.)*"', "", line))
    return sum(t.count(x) for x in "([{⟨") - sum(t.count(x) for x in ")]}⟩")


def split_chunks(text):
    """The declarations of `text` (a part of the tie between the literals and `end`), in order, each
    `(text, names, kind)`: kind "decl" for a declaration with the `set_option ... in` lines and the
    doc comment before it, "note" for a comment by itself. The chunks concatenate to `text`."""
    lines = text.split("\n")
    out, i, n = [], 0, len(lines)
    while i < n and lines[i] == "":
        i += 1
    if i:
        out.append(["\n".join(lines[:i]) + "\n", [], "note"])
    while i < n:
        a = i
        pre_doc = False
        while True:
            s = lines[i]
            if s.startswith("/-"):
                depth = 0
                while True:
                    depth += lines[i].count("/-") - lines[i].count("-/")
                    i += 1
                    if depth <= 0 or i >= n:
                        break
                if s.startswith("/--"):
                    pre_doc = True
                    if i < n and (lines[i].startswith("set_option ") or SPLIT_DECL.match(lines[i])):
                        continue
                kind = "doc" if pre_doc else "note"
                break
            if re.match(r"set_option \S+ \S+ in$", s) or s.startswith("--"):
                i += 1
                continue
            m = re.match(r"section (\S+)$", s)
            if m:
                try:
                    i = lines.index(f"end {m[1]}", i) + 1
                except ValueError:
                    raise Refused(f"--split: no `end {m[1]}` for `{s}`")
                while i < n and lines[i] == "":
                    i += 1
                kind = "decl"
                break
            if SPLIT_DECL.match(s):
                depth = split_depth(s)
                i += 1
                while i < n and (lines[i].startswith((" ", "\t")) or lines[i] == "" or depth > 0):
                    depth += split_depth(lines[i])
                    i += 1
                kind = "decl"
                break
            raise Refused(f"--split: a line of the tie that is no declaration, comment or `set_option ... in`: {s[:80]!r}")
        while kind != "decl" and i < n and lines[i] == "":
            i += 1
        if kind == "doc":
            raise Refused(f"--split: a doc comment not followed by a declaration: {lines[a][:80]!r}")
        body = "\n".join(lines[a:i]) + ("\n" if i < n else "")
        names = [m[2].strip("«»") for l in lines[a:i] for m in [SPLIT_DECL.match(l)] if m] if kind == "decl" else []
        out.append([body, names if lines[a].startswith("section ") else names[:1], kind])
    if "".join(c[0] for c in out) != text:
        raise Refused("--split: the declarations of the tie do not make up its text")
    return out


def split_refs(body):
    """The identifiers a declaration's code names (comments and strings dropped), first components only."""
    s = re.sub(r"/-.*?-/", " ", body, flags=re.S)
    s = re.sub(r"--[^\n]*", " ", s)
    s = re.sub(r'"(?:[^"\\]|\\.)*"', " ", s)
    return set(SPLIT_IDENT.findall(s))


def split_tie(ns, lean, marks, text_rel, cmd, blocks):
    """The files of `--split`: `{file stem: text}`, the first `ns`, and the report (what each part
    repeats; the parts merged because one reads another's decision). `marks`: `(offset, mark)`
    in `lean`, each at the start of a line, in order; `blocks`: the lists of names the single file
    checks and prints, each block in turn."""
    end = f"end KCore.{ns}"
    a = lean.index("\nimport KcoreSpec\n") + 1
    b = lean.index("noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H\n")
    b = lean.index("\n", b) + 1
    while lean[b:b + 1] == "\n":
        b += 1
    e = lean.index("\n" + end + "\n") + 1
    header, preamble = lean[:a], lean[a:b]
    bounds = [(max(o, b), m) for o, m in marks if o < e]
    if bounds[0][0] != b:
        bounds.insert(0, (b, "Head"))
    chunks = []
    for (o, m), (o2, _) in zip(bounds, bounds[1:] + [(e, None)]):
        if o2 > o:
            for body, names, kind in split_chunks(lean[o:o2]):
                chunks.append(dict(body=body, names=names, kind=kind, mark=m))
    defs = {}
    for k, ch in enumerate(chunks):
        for x in ch["names"]:
            defs.setdefault(x, k)
    for k, ch in enumerate(chunks):
        ch["refs"] = {defs[x] for x in split_refs(ch["body"]) if x in defs} - {k} if ch["kind"] == "decl" else set()
        ch["decides"] = ch["kind"] == "decl" and bool(SPLIT_DECIDES.search(re.sub(r"/-.*?-/", " ", ch["body"], flags=re.S)))
    clos = {}

    def closure(k):
        if k not in clos:
            seen, todo = set(), list(chunks[k]["refs"])
            while todo:
                j = todo.pop()
                if j not in seen:
                    seen.add(j)
                    todo += chunks[j]["refs"]
            clos[k] = seen
        return clos[k]

    file_of = lambda m: ns if m in SPLIT_FIRST else ns + m
    parent = {}

    def find(f):
        while parent.get(f, f) != f:
            f = parent[f]
        return f

    def union(fs):
        fs = sorted({find(f) for f in fs}, key=lambda f: (f != ns, [ns + p for p in SPLIT_PARTS].index(f) if f != ns else 0))
        for f in fs[1:]:
            parent[f] = fs[0]
        return fs[0]

    heavy = lambda j: chunks[j]["decides"] and chunks[j]["mark"] not in ("Head", "Consistency", "Rest")
    home = {}
    for _ in range(len(SPLIT_PARTS) + 2):
        changed = False
        for k, ch in enumerate(chunks):
            if ch["kind"] != "decl":
                continue
            own = None if ch["mark"] == "Rest" else find(file_of(ch["mark"]))
            hs = {find(home.get(j, file_of(chunks[j]["mark"]))) for j in closure(k) if heavy(j)}
            if own is not None:
                hs.add(own)
            h = union(hs) if hs else ns
            if home.get(k) != h:
                home[k], changed = h, True
        if not changed:
            break
    # a declaration of the later sections that reads no decision goes where all its readers are
    readers = {k: [j for j, ch in enumerate(chunks) if k in ch["refs"]] for k in home}
    for k in sorted(home, reverse=True):
        rs = {find(home[j]) for j in readers[k]}
        if chunks[k]["mark"] == "Rest" and find(home[k]) == ns and len(rs) == 1 and ns not in rs:
            home[k] = rs.pop()
    nxt = None
    for k in range(len(chunks) - 1, -1, -1):
        if chunks[k]["kind"] == "decl":
            nxt = home[k] = find(home[k])
        else:
            home[k] = nxt if nxt is not None and chunks[k]["mark"] == chunks[k + 1]["mark"] else find(file_of(chunks[k]["mark"]))
    files = [f for f in [ns] + [ns + p for p in SPLIT_PARTS] if find(f) == f and any(home[k] == f for k in home)]
    if ns not in files:
        files.insert(0, ns)
    merged = sorted({ns + p for p in SPLIT_PARTS if find(ns + p) != ns + p})
    owner = {x: home[k] for x, k in defs.items()}
    out, report = {}, {"merged": {m: find(m) for m in merged}, "repeats": {}}
    for f in files:
        own = [k for k in range(len(chunks)) if home[k] == f]
        need = set().union(*[closure(k) for k in own]) - set(own) if own else set()
        body = "".join(chunks[k]["body"] for k in range(len(chunks)) if k in need or k in set(own))
        if not body.endswith("\n\n"):
            body += "\n"
        rep = [x for k in sorted(need) for x in chunks[k]["names"]]
        dec = [x for k in sorted(need) if chunks[k]["decides"] for x in chunks[k]["names"]]
        if f != ns or rep:
            report["repeats"][f] = dict(names=rep, decided=dec)
        tail = [end, ""]
        for blk in blocks:
            mine = [x for x in blk if owner.get(x, ns) == f]
            tail += [f"#check @KCore.{ns}.{x}" for x in mine] + [f"#print axioms KCore.{ns}.{x}" for x in mine]
        if f == ns:
            parts = ", ".join(f"`test/{g}.lean`" for g in files[1:])
            para = (f"Written with `--split`: this file holds the literals, the names, `wf`, the account, the "
                    f"consistency and the sections that read none of the other files' decisions; the other sections "
                    f"are in {parts}, in this namespace, each of which repeats the literals and the definitions and "
                    f"facts it reads, as a test file imports no test file.")
            head = header[:header.rindex("-/")] + (
                textwrap.fill(para, width=100, initial_indent="  ", subsequent_indent="  ", break_on_hyphens=False,
                              break_long_words=False) + "\n" if files[1:] else "") + header[header.rindex("-/"):]
        else:
            head = (f"/-\n  Part {f[len(ns):]} of the tie (C14) on `{text_rel}`, test/{ns}.lean: the sections\n"
                    f"  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one\n"
                    f"  repeats the literals and the definitions and facts it reads. Written by\n"
                    f"  `test/constructs/tiegen.py {cmd} --split`; run from the package root:\n"
                    f"  `lake env lean -j1 test/{f}.lean`.\n-/\n")
        out[f] = head + preamble + body + "\n".join(tail) + "\n"
    return out, report


# the sections a hand-written text may take the place of (`--hand NAME=FILE`), by their first line
HAND_SECTIONS = {"consistency": "/-! ## Consistency for every H",
                 "ovlfn": "/-! ## Sentences of a function-overloaded symbol: the covered part"}

NEX_TIE = os.path.join(KS, "test/NonExecOwiseTie.lean")


def fnfun_section(idx, chunk=0):
    """The function functional sentences, each a sort predicate's `functional` sentence as written, at
    values in every model of `Γc` for every H (`LibEv.sortPredFun_evC_withHooks`). `chunk`: `fnFun_checked`
    and `fnFun_trS` decided by ranges of that many sentences (0: one decision each)."""
    t = fnfun_text(idx)
    if chunk:
        rs = ranges(len(idx), chunk, chunk)
        trp = "(fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))"
        for old, prefix, stmt, pred in (
                ("theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel\n", "fnFunE",
                 "theorem fnFun_checked : fnFunText.all fnFunOK = true :=", "fnFunOK"),
                ("theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by\n  decide +kernel\n",
                 "fnFunTrE", f"theorem fnFun_trS : fnFunText.all {trp} = true :=", trp)):
            thms, body = by_ranges(prefix, "fnFunText", pred, rs, lem="tieAll")
            assert t.count(old) == 1
            t = t.replace(old, f"{thms}\n\n{stmt}\n  {body}\n")
    return t


def fnfun_text(idx):
    n = len(idx)
    return f"""/-! ## Function functional ({n}): the sort predicates' `functional` sentences, at values in every model of Γc -/

/- The class holds the `functional` sentences of {n} sort predicates `isX`,
`\\exists{{R}}(Val:SortBool{{}}, \\equals{{SortBool{{}}, R}}(Val:SortBool{{}}, LblisX{{}}(K0:SortK{{}})))`. KCore builds
the sort predicates (`Semantics.sortPreds`): each has a value at every K, and a model of `Γc` reads
its application at a value's element as that value's element (`LibEv.sortPredFun_evC`, under
`coreOK`, the clauses' predicates `\\top`, no `\\exists` in a clause, and no condition over a
variable the patterns leave open). So each sentence holds in every model of `Γc`, and of `Γc` with
the step's closure, at every valuation sending K0 to a value, for every H, from the sort predicates'
own results and without `FnHyp`. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [{wrap_nums(idx, 3)}]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- **`fnFunText` is the account's function functional class**: the same indices, each once. -/
theorem fnFun_account : (classOf "function functional").isPerm (fnFunText.map (·.index)) = true := by
  decide +kernel

/-- The sentence is the `functional` sentence of a sort predicate of `c`, over the one sort
variable `R`, with its variables' sorts the registry's. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the {n} reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\\top`, no clause binds a variable by `\\exists`, and no clause has
a condition over a variable its patterns leave open. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => !cl.reqOpen) = true := by
  decide +kernel

theorem fnFun_noWitH (H : HookParams) : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = false := by
  intro fn hfn cl hcl
  have h := List.all_eq_true.mp (List.all_eq_true.mp fnFun_clauses.2.2 fn hfn) cl hcl
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  simp [Clause.needsWitness, h]

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), without `FnHyp`. -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany⟩ := hok
  obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
  exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2.1)
    (fun fn hfn cl hcl hw => absurd hw (by rw [fnFun_noWitH H fn hfn cl hcl]; decide)) hfn hfp.2 ad hfp.1 hsv

/-- The same in every model of `Γc` with the step's closure, the theory `Consistent` asks a model of. -/
theorem fnFun_at_values_step (H : HookParams) : ∀ ad ∈ fnFunText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H)) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => fnFun_at_values H ad had M hM I (fun φ hφ => hI φ (Or.inl hφ))
"""


def fnfun_section_fnhyp(idx, user):
    """The function functional sentences where the tie states `FnHyp` for every H (`fnHypH`): each a
    sort predicate's `functional` sentence, at values in every model of `Γc` from the sort predicates'
    results (`LibEv.sortPredFun_evC_withHooks`), or that of a function of the text declared total,
    from the values `FnHyp` gives it (`LibEv.fnFun_evC_withHooks`); the clauses' conditions are
    decided where `needsWitness` holds by `FnHyp`'s `OpenDecided`."""
    n, u = len(idx), len(user)
    if user:
        kinds = (f"{n - u} of sort predicates `isX` (KCore builds them, `Semantics.sortPreds`) and {u} of "
                 f"functions of the text declared total ({', '.join(map(str, user))})")
        ok = """noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    ((c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig) ||
      c.fns.any fun fn => fn.total && decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunRegS c fn.sig)"""
        okdoc = """/-- The sentence is the `functional` sentence of a sort predicate of `c`, with its variables' sorts
the registry's, or of a function of `c` declared total, with its variables' sorts sorts of `c`, over
the one sort variable `R`. -/"""
        prf = """  simp only [fnFunOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany | hany⟩ := hok
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
      (fnHypH H).2.2.2.2.1.2 hfn hfp.2 ad hfp.1 hsv
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.fnFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
      (fnHypH H) hfn hfp.1.1 hfp.2 ad hfp.1.2 hsv"""
    else:
        kinds = "each that of a sort predicate `isX` (KCore builds them, `Semantics.sortPreds`)"
        ok = """noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig"""
        okdoc = """/-- The sentence is the `functional` sentence of a sort predicate of `c`, over the one sort
variable `R`, with its variables' sorts the registry's. -/"""
        prf = """  simp only [fnFunOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany⟩ := hok
  obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
  exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
    (fnHypH H).2.2.2.2.1.2 hfn hfp.2 ad hfp.1 hsv"""
    com = textwrap.fill(
        f"The class holds {n} `functional` sentences, `\\exists{{R}}(Val:S, \\equals{{S, R}}(Val:S, f(K0, …)))`: "
        f"{kinds}. A model of `Γc` reads the application of a function with a value at every argument list of "
        "its sorts, at values' elements, as that value's element (`LibEv.fnFun_evC`, under `coreOK`, the "
        "clauses' predicates `\\top`, no `\\exists` in a clause, and the clauses' conditions decided where "
        "`needsWitness` holds). A sort predicate has those values from its own clauses "
        "(`LibEv.sortPredFun_evC`)" + ("; a function declared total has them from `FnHyp` "
                                       "(`LibEv.fnFun_evC_withHooks`)" if user else "") +
        ". `FnHyp`, which the tie states for every H (`fnHypH`), decides the conditions (its `OpenDecided`). "
        "So each sentence holds in every model of `Γc`, and of `Γc` with the step's closure, at every valuation "
        "sending its variables to values, for every H.", 100, initial_indent="/- ", break_long_words=False,
        break_on_hyphens=False) + " -/"
    return f"""/-! ## Function functional ({n}): the `functional` sentences, at values in every model of Γc, from `FnHyp` -/

{com}

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [{wrap_nums(idx, 3)}]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- **`fnFunText` is the account's function functional class**: the same indices, each once. -/
theorem fnFun_account : (classOf "function functional").isPerm (fnFunText.map (·.index)) = true := by
  decide +kernel

{okdoc}
{ok}

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the {n} reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\\top` and no clause binds a variable by `\\exists`. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true := by
  decide +kernel

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), from `FnHyp` (`fnHypH`). -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
{prf}

/-- The same in every model of `Γc` with the step's closure, the theory `Consistent` asks a model of. -/
theorem fnFun_at_values_step (H : HookParams) : ∀ ad ∈ fnFunText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H)) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => fnFun_at_values H ad had M hM I (fun φ hφ => hI φ (Or.inl hφ))
"""


def pair_section(j, i, prio, nonexec, nfe):
    """The function equations where Γ's item `j` is sentence `i` with the premise that the clauses of
    a smaller priority that are not `aside` do not apply (W1), and every other item is its sentence's
    translation (`TiePair.shapeB`), with the converse over Γ's content (`TiePair.gamma_from`)."""
    nx = ", the `non-executable` one" if nonexec else ""
    intro = textwrap.fill(
        f"`fnItems`'s item {j} is the equation of the clause of priority {prio}{nx}: Γ holds it under the "
        f"negation of the clauses of a smaller priority that are not `aside` (`prioEquation`, "
        f"`competingEquation`), a premise the sentence does not state. Sentence {i} entails it (`w1`, the "
        f"direction of the class priority equation) and is the item without that premise (`w_text`); it "
        f"is not the item (`w_differs`). Every other item is the translation of its function sentence "
        f"(`shape`). -/", width=100, break_on_hyphens=False, break_long_words=False)
    return f'''/-! ## Function equations ({nfe} sentences) and the priority equation (sentence {i})

{intro}

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

/-- Γ's axiom of the narrowed equation. -/
noncomputable def aW : Kore.Axiom := ((TiePair.fnAxioms c)[{j}]?).getD ⟨[], .top KoreAML.R, []⟩

theorem aW_at : (TiePair.fnAxioms c)[{j}]? = some aW := by decide +kernel

/-- Γ's item of it. -/
noncomputable def gW : P := (trAxiom [] [] ⟨0, "kernel", aW⟩).pat

theorem gW_at : (TiePair.gammaPats c)[{j}]? = some gW := TiePair.gammaPats_at aW_at

kernel_rfl fnText_W : fnText[{j}]? = some U.ax{i}

/-- Its premise has the negated conjunct. -/
theorem aW_narrowed : (TiePair.negParts aW.pattern).isSome = true := by decide +kernel

/-- **Γ's item without the priority premise is the text's sentence {i}** (`TiePair.minusNeg`, up to
the indices of its variables: `TiePair.sameB`; kernel). -/
theorem w_text : TiePair.sameB (TiePair.minusNeg aW) (trS U.ax{i}).pat = true := by decide +kernel

/-- **Γ's item is not the sentence.** -/
theorem w_differs : gW ≠ (trS U.ax{i}).pat := by decide +kernel

/-- **W1**: the text's sentence {i} entails Γ's item, in every model of definedness. -/
theorem w1 : TiePair.Texts [(trS U.ax{i}).pat] ⊧ gW :=
  fun {{M}} _ {{I}} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and for
sentence {i} Γ's item. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set {j} gW

/-- **Each of Γ's equations but item {j} is the translation of its text sentence** (kernel); item
{j} is `gW`. -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each sentence of `fnText` but sentence {i}, for
every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad → j ≠ {j} →
    Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hne
  refine TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (i := j) ?_)
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_map, hj]; rfl

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText`; item {j} by W1, the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  by_cases hJ : j = {j}
  · subst hJ
    refine ⟨U.ax{i}, fnText_W, ?_⟩
    have hg : (TiePair.gammaPats (cH H))[{j}]? = some it.pat := by
      unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
    rw [TiePair.gammaPats_withHooks, gW_at] at hg
    rw [← Option.some.inj hg]
    intro M _ I hI
    exact w1 hI
  · obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
    unfold textPats at ht
    rw [List.getElem?_set_ne (Ne.symm hJ), List.getElem?_map] at ht
    cases hf : fnText[j]? with
    | none => rw [hf] at ht; cases ht
    | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (sentence {i} through
W1), Γ's rule items and the five parts Γ defines by predicates (`TiePair.Pre`), for every H. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → TiePair.Pre (cH H) textPats ⊧ φ :=
  TiePair.gamma_from (shapeH H)
'''


def pairs_section(ws, acs, nfe, npe):
    """The function equations where Γ's items `ws` (each `(j, i, prio)`: item `j`, sentence `i`) are
    their sentences with the premise that the clauses of a smaller priority that are not `aside` do
    not apply (W1), the items `acs` (each `(j, i)`) are their sentences up to the order of the
    operands of sorted disjunctions and the names of variables (`TieAlpha.acEqB`), and every other
    item is its sentence's translation (`TiePair.shapeB`), with the converse over Γ's content."""
    at = sorted([j for j, _, _ in ws] + [j for j, _ in acs])
    wjs = [j for j, _, _ in ws]
    wl = ", ".join(f"{j} (sentence {i}, priority {p})" for j, i, p in ws)
    al = ", ".join(f"{j} (sentence {i})" for j, i in acs)
    parts = []
    if ws:
        parts.append(f"Γ's item{'s' if len(ws) > 1 else ''} {wl} {'are' if len(ws) > 1 else 'is'} the clause's "
                     f"equation under the negation of the clauses of a smaller priority that are not `aside` "
                     f"(`prioEquation`, `competingEquation`), a premise the sentence does not state: the sentence "
                     f"entails the item (`prio<j>_w1`, the direction of the class priority equation) and is the item "
                     f"without that premise (`prio<j>_text`); it is not the item (`prio<j>_differs`).")
    if acs:
        parts.append(f"Γ's item{'s' if len(acs) > 1 else ''} {al} and {'their sentences' if len(acs) > 1 else 'its sentence'} "
                     f"agree up to the order of the operands of their sorted disjunctions and the names of their "
                     f"variables (`ac<j>_same`, `TieAlpha.acEqB`): a sorted disjunction is, in every model, the union "
                     f"of its operands within the sort, whatever their order, and the index of a variable is a name, "
                     f"so the two are satisfied by the same interpretations (`ac<j>_iff`). Such an item is not its "
                     f"sentence as written (`ac<j>_differs`).")
    parts.append("Every other item is the translation of its function sentence (`shape`). -/")
    intro = "\n\n".join(textwrap.fill(x, width=100, break_on_hyphens=False, break_long_words=False) for x in parts)
    out = [f"/-! ## Function equations ({nfe} sentences) and priority equations ({npe} sentences)", "", intro, "",
           "/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority",
           "(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/",
           "noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all", "",
           "/-- **`fnText` is the account's function-equation and priority-equation classes**: the same",
           "indices, each once. -/",
           "theorem fns_account :",
           '    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by',
           "  decide +kernel", ""]
    if acs:
        out += ["/-- A model of Γ satisfies each of Γ's equations. -/",
                "theorem fnItem_sat {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))",
                "    {j : Nat} {g : P} (hg : (TiePair.gammaPats c)[j]? = some g) : I ⊧ᴵ g := by",
                "  obtain ⟨it, hit, rfl⟩ : ∃ it ∈ fnItems c, it.pat = g := by",
                "    unfold TiePair.gammaPats at hg",
                "    rw [List.getElem?_map] at hg",
                "    cases h : (fnItems c)[j]? with",
                "    | none => rw [h] at hg; cases hg",
                "    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩",
                "  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))", ""]
    for j, i, p in ws:
        out += [f"/-- Γ's axiom of item {j} (sentence {i}, priority {p}). -/",
                f"noncomputable def prioAx{j} : Kore.Axiom := ((TiePair.fnAxioms c)[{j}]?).getD ⟨[], .top KoreAML.R, []⟩",
                f"theorem prioAx{j}_at : (TiePair.fnAxioms c)[{j}]? = some prioAx{j} := by decide +kernel",
                f"noncomputable def prioItem{j} : P := (trAxiom [] [] ⟨0, \"kernel\", prioAx{j}⟩).pat",
                f"theorem prioItem{j}_at : (TiePair.gammaPats c)[{j}]? = some prioItem{j} := TiePair.gammaPats_at prioAx{j}_at",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                "/-- Its premise has the negated conjunct, the clauses of a smaller priority. -/",
                f"theorem prio{j}_narrowed : (TiePair.negParts prioAx{j}.pattern).isSome = true := by decide +kernel",
                f"/-- **Γ's item without the priority premise is the text's sentence {i}** (`TiePair.minusNeg`, up",
                "to the indices of its variables: `TiePair.sameB`; kernel), and it is not the sentence. -/",
                f"theorem prio{j}_text : TiePair.sameB (TiePair.minusNeg prioAx{j}) (trS U.ax{i}).pat = true := by decide +kernel",
                f"theorem prio{j}_differs : prioItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel",
                f"/-- **W1**: the text's sentence {i} entails Γ's item {j}, in every model of definedness. -/",
                f"theorem prio{j}_w1 : TiePair.Texts [(trS U.ax{i}).pat] ⊧ prioItem{j} :=",
                f"  fun {{M}} _ {{I}} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) prio{j}_text",
                "    (hI _ (Or.inl (List.mem_singleton_self _)))", ""]
    for j, i in acs:
        out += [f"/-- Γ's item {j} (sentence {i}). -/",
                f"noncomputable def acItem{j} : P := (TiePair.gammaPats c).getD {j} ⊥",
                f"theorem acItem{j}_at : (TiePair.gammaPats c)[{j}]? = some acItem{j} := by decide +kernel",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                f"/-- **Γ's item {j} and sentence {i} agree** up to the order of the operands of their sorted",
                "disjunctions and the names of their variables (`TieAlpha.acEqB`; kernel), and the item is not the",
                "sentence as written. -/",
                f"theorem ac{j}_same : TieAlpha.acEqB acItem{j} (trS U.ax{i}).pat = true := by decide +kernel",
                f"theorem ac{j}_differs : acItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel",
                f"/-- **Sentence {i} and Γ's item {j} are satisfied by the same interpretations.** -/",
                f"theorem ac{j}_iff {{M : Type}} {{I : Interpretation KoreAML.Sym M}} : (I ⊧ᴵ (trS U.ax{i}).pat) ↔ (I ⊧ᴵ acItem{j}) :=",
                f"  (TieAlpha.acEqB_sat ac{j}_same).symm", ""]
    for j, i in acs:
        out += [f"/-- **E for sentence {i}**: Γ entails it, for every H (`ac{j}_iff`). -/",
                f"theorem ac{j}_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by",
                "  intro M _ I hI",
                f"  exact ac{j}_iff.mpr (fnItem_sat hI acItem{j}_at)", ""]
    item = {j: f"prioItem{j}" for j, _, _ in ws} | {j: f"acItem{j}" for j, _ in acs}
    tp = "(fnText.map (trS · |>.pat))"
    for j in at:
        tp = f"({tp}.set {j} {item[j]})"
    sl = ", ".join(map(str, at))
    hs = ", ".join(f"h{j}" for j in at)
    ne = ", ".join(f"List.getElem?_set_ne (Ne.symm h{j})" for j in reversed(at))
    split_hn = (f"  obtain ⟨{hs}⟩ := hn" if len(at) > 1 else f"  have h{at[0]} := hn")
    out += ["/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's",
            f"item at {'positions' if len(at) > 1 else 'position'} {sl}. -/",
            f"noncomputable def textPats : List P := {tp[1:-1]}", "",
            "/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's",
            "items (kernel). -/",
            "theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel", "",
            "theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by",
            "  rw [TiePair.gammaPats_withHooks]; exact shape", "",
            "/-- The positions set to Γ's items. -/",
            f"def pairSetAt : List Nat := [{sl}]", "",
            "theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :",
            "    textPats[j]? = some (trS ad).pat := by",
            "  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn",
            split_hn,
            "  unfold textPats",
            f"  rw [{ne}, List.getElem?_map, hj]",
            "  rfl", "",
            ]
    wl2 = ", ".join(map(str, wjs))
    out += [f"/-- **E for the function equations**: Γ entails each sentence of `fnText`"
            + (f" but the narrowed ones (items {wl2})" if ws else "") + ", for every H"
            + ("; " + ", ".join(f"item {j}" for j, _ in acs) + " through " + ", ".join(f"`ac{j}_iff`" for j, _ in acs) if acs else "")
            + ". -/",
            "theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →",
            f"    j ∉ ([{wl2}] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by",
            "  intro j ad hj hn"]
    for j, i in acs:
        out += [f"  by_cases h{j} : j = {j}",
                f"  · subst h{j}",
                f"    rw [fnText_at{j}] at hj",
                f"    rw [← Option.some.inj hj]",
                f"    exact ac{j}_entailed H"]
    out += ["  have hn' : j ∉ pairSetAt := by",
            "    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢",
            "    omega",
            "  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))", ""]
    out += ["/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of",
            "`fnText`" + ("; the narrowed ones by W1" if ws else "") + ("; " + ", ".join(f"item {j}" for j, _ in acs) + " by "
            + ", ".join(f"`ac{j}_iff`" for j, _ in acs) if acs else "") + "; the others by their translation. -/",
            "theorem fns_from_text (H : HookParams) :",
            "    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →",
            "      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by",
            "  intro j it hj",
            "  have hg : (TiePair.gammaPats c)[j]? = some it.pat := by",
            "    rw [← TiePair.gammaPats_withHooks c H]",
            "    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl",
            "  have pick : ∀ {i : Nat} {g : P} {ad : AxiomDecl}, (TiePair.gammaPats c)[i]? = some g → fnText[i]? = some ad →",
            "      (TiePair.Texts [(trS ad).pat] ⊧ g) → j = i →",
            "      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by",
            "    intro i g ad hgi hti hent hji",
            "    subst hji",
            "    rw [hgi] at hg",
            "    exact ⟨ad, hti, (Option.some.inj hg) ▸ hent⟩"]
    for j in at:
        out.append(f"  by_cases h{j} : j = {j}")
        if j in wjs:
            out.append(f"  · exact pick prioItem{j}_at fnText_at{j} prio{j}_w1 h{j}")
        else:
            out.append(f"  · exact pick acItem{j}_at fnText_at{j}")
            out.append(f"      (fun {{M}} _ {{I}} hI => ac{j}_iff.mp (hI _ (Or.inl (List.mem_singleton_self _)))) h{j}")
    out += ["  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj",
            "  unfold textPats at ht",
            f"  rw [{ne}, List.getElem?_map] at ht",
            "  cases hf : fnText[j]? with",
            "  | none => rw [hf] at ht; cases ht",
            "  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩", "",
            "/-- The priority each function sentence's attributes state is the priority of the clause whose",
            "item it gives, item by item in `fnItems`'s order. -/",
            "theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =",
            "    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel", "",
            "/-! ## The converse over Γ's content -/", "",
            "/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to",
            "Γ's through their sentences), Γ's rule items and the five parts Γ defines by predicates",
            "(`TiePair.Pre`), for every H. -/",
            "theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → TiePair.Pre (cH H) textPats ⊧ φ :=",
            "  TiePair.gamma_from (shapeH H)", ""]
    return "\n".join(out) + "\n"


def cut_form(k):
    """The kind of a cut item (`fnCut`): `andApp` at the equation's own premise, `andApp` under a
    competitor's negation, or `notCond`."""
    return "not" if k["kind"] == "notCond" else "own" if k["place"] == ("own",) else "under"


def cut_lits(k):
    """The Lean literals of a cut item's `TieCutEq.Cut` and `TieCutEq.Place`."""
    kl = ".notCond" if k["kind"] == "notCond" else f"(.andApp [{', '.join(map(str, k['path']))}])"
    pl = ".own" if k["place"] == ("own",) else f"(.under {k['place'][1]} {k['place'][2]})"
    return kl, pl


def cut_in_entailed(k, confined):
    """Whether `fns_entailed` (over Γ) holds the cut item's sentence: an `andApp` cut, the one at the
    equation's own premise only on a text whose theory is Γ (its entailment reads the constructors'
    facts, which a model of the theory has)."""
    return cut_form(k) == "under" or (cut_form(k) == "own" and not confined)


def readings_header(by_class, pair_text, ws, acs, rds, uns, cuts=(), confined=False):
    """The header's paragraph of the function equations `readings_section` ties."""
    nfe, npe = len(by_class["function equation"]), len(by_class["priority equation"])
    lst = lambda js: ", ".join(f"{j} ({pair_text[j]})" for j in js)
    pl = lambda js, a, b: a if len(js) > 1 else b
    txt_ = (f"Function equations ({nfe}) and priority equations ({npe}), in the order `fnText` lists them "
            f"(`fns_account`): each of Γ's items but {', '.join(map(str, sorted(ws + acs + rds + uns + [j for j, _, _ in cuts])))} is the "
            f"translation of one sentence (`shape`), so Γ entails it (`fns_entailed`).")
    if ws:
        txt_ += (f" Item{pl(ws, 's', '')} {lst(ws)} (sentence in parentheses) {pl(ws, 'are', 'is')} the clause "
                 f"under the negation of the clauses of a smaller priority that are not `aside`, which the sentence "
                 f"entails (`prio<j>_w1`, W1) and is without that premise (`prio<j>_text`).")
    if acs:
        txt_ += (f" Item{pl(acs, 's', '')} {lst(acs)} and {pl(acs, 'their sentences', 'its sentence')} agree up to "
                 f"the order of the operands of their sorted disjunctions and the names of their variables "
                 f"(`ac<j>_same`, `TieAlpha.acEqB`), so they are satisfied by the same interpretations (`ac<j>_iff`) "
                 f"and Γ entails the sentence.")
    if rds:
        txt_ += (f" Item{pl(rds, 's', '')} {lst(rds)} {pl(rds, 'are', 'is')} the equation whose right side's first "
                 f"conjunct the sentence writes with an alternative that holds nothing (`\\bottom`, or an application "
                 f"with a `\\bottom` argument: `TieRhs.emptyAltOf`, `TieRhs.emptyB`), which the reader drops "
                 f"(`orBottom`): the sentence is the item so written (`rd<j>_text`, up to the indices of its "
                 f"variables; `rd<j>_ok`), the two hold in the same models of definedness (`rd<j>_iff`, "
                 f"`TieRhs.orEmptyOK_iff`), so Γ entails the sentence (`rd<j>_entailed`) and it gives the item.")
    if cuts:
        cjs = [j for j, _, _ in cuts]
        txt_ += (f" Item{pl(cjs, 's', '')} {lst(cjs)} {pl(cjs, 'are equations', 'is the equation')} whose premise Γ writes "
                 f"through a cut of the clause's `requires` (`andUnderAppCut`, `notAsCondition`): each sentence is its "
                 f"item with the premise as the text writes it (`cut<j>_same`, `TieCutEq.textItem`, up to the names "
                 f"of its variables).")
        for j, i, k in cuts:
            f = cut_form(k)
            if f == "own":
                txt_ += (f" Item {j}: the sentence gives the item in every model of definedness (`cut{j}_from_text`), "
                         f"and {'Γc' if confined else 'Γ'} entails the sentence (`cut{j}_entailed`, its models "
                         f"having the constructors' facts).")
            elif f == "under":
                txt_ += (f" Item {j}, the cut premise a competitor's under the negation: Γ entails the sentence "
                         f"(`cut{j}_entailed`, definedness only) and the sentence gives the item in a model with the "
                         f"constructors' facts (`cut{j}_from_text`), which `fns_from_text` leaves out.")
            else:
                txt_ += (f" Item {j}: the two hold in the same models with the constructors' facts in which every "
                         f"element of Bool is `true` or `false` (`cut{j}_iff`; `boolClosed`, a premise named there, "
                         f"is not Γ's), so the sentence holds in a model of the theory in which Bool is closed "
                         f"(`cut{j}_entailed`); `fns_entailed` and `fns_from_text` leave it out.")
    if uns:
        txt_ += (f" Item{pl(uns, 's', '')} {lst(uns)} {pl(uns, 'are', 'is')} not {pl(uns, 'their sentences', 'its sentence')} "
                 f"(`un<j>_differs`) and no reading here ties {pl(uns, 'them', 'it')}: {pl(uns, 'those sentences are', 'the sentence is')} "
                 f"`uncovered`, and `fns_entailed` and `fns_from_text` leave {pl(uns, 'them', 'it')} out.")
    txt_ += " `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the clauses')."
    return textwrap.fill(txt_, width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False,
                         break_long_words=False)


def readings_gamma_header(pair_text, ws, acs, rds, uns, cuts=()):
    """The header's paragraph of `readings_section`'s converse over Γ's content."""
    cno = [j for j, _, k in cuts if cut_form(k) != "own"]
    via = (([f"{', '.join(str(pair_text[j]) for j in ws)} through W1"] if ws else [])
           + [f"{pair_text[j]} through `ac{j}_iff`" for j in acs] + [f"{pair_text[j]} through `rd{j}_iff`" for j in rds]
           + [f"{i} through `cut{j}_from_text`" for j, i, k in cuts if cut_form(k) == "own"])
    txt_ = ("The converse over Γ's content: each premise is a consequence of the function sentences"
            + (f" ({', '.join(via)})" if via else "")
            + (f", Γ's own item{'s' if len(uns) > 1 else ''} {', '.join(map(str, uns))} (whose sentence"
               f"{'s are' if len(uns) > 1 else ' is'} uncovered)" if uns else "")
            + (f", Γ's own item{'s' if len(cno) > 1 else ''} {', '.join(map(str, cno))} (whose sentence"
               f"{'s give' if len(cno) > 1 else ' gives'} it with the constructors' facts: `cut<j>_from_text`, "
               f"`cut<j>_iff`)" if cno else "")
            + ", Γ's rule items, the five parts Γ defines by predicates, or definedness (`gamma_from`).")
    return textwrap.fill(txt_, width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False,
                         break_long_words=False)


def readings_names(ws, acs, rds, uns, cuts=()):
    """The theorems `readings_section` states, in its order."""
    dirs = {"own": ("cut{}_from_text", "cut{}_entailed"), "under": ("cut{}_entailed", "cut{}_from_text"),
            "not": ("cut{}_iff", "cut{}_entailed")}
    return (["fns_account"] + [n.format(j) for j in ws for n in
                               ("prio{}_narrowed", "prio{}_text", "prio{}_differs", "prio{}_w1")] +
            [n.format(j) for j in acs for n in ("ac{}_same", "ac{}_differs", "ac{}_iff", "ac{}_entailed")] +
            [n.format(j) for j in rds for n in ("rd{}_ok", "rd{}_text", "rd{}_differs", "rd{}_iff", "rd{}_entailed")] +
            [n.format(j) for j, _, k in cuts for n in
             ("cut{}_shape", "cut{}_facts", "cut{}_same", "cut{}_differs") + dirs[cut_form(k)]] +
            [f"un{j}_differs" for j in uns] +
            ["shape", "fns_entailed", "fns_from_text", "fn_prios", "gamma_from"])


def readings_section(ws, acs, rds, uns, nfe, npe, cuts=(), confined=False):
    """`pairs_section` with two more kinds of Γ's items beside the narrowed ones `ws` and those `acs`
    equal up to the operands' order and the variables' names: the items `rds` (each `(j, i)`: item
    `j`, sentence `i`), whose sentence writes an alternative that holds nothing beside the right
    side's first conjunct (`TieRhs.orEmptyOK_iff`, every model of definedness: E and its converse),
    and the items `uns`, which no reading here ties: their sentences are left out of `fns_entailed`
    and `fns_from_text` (uncovered), and the premise set holds Γ's item there. And the items `cuts`
    (each `(j, i, k)`, `k` the probe's `fnCut`), whose premise Γ writes through a cut of the clause's
    `requires` (`TieCutEq`): each direction is stated over what it reads, definedness, the
    constructors' facts of a model of the theory (Γ, or `Γc` on a text that reads a confined sort), and
    for `notCond` the closure of Bool as a named premise; the sentences whose direction reads more than
    definedness are left out of `fns_entailed` or `fns_from_text`."""
    at = sorted([j for j, _, _ in ws] + [j for j, _ in acs] + [j for j, _ in rds] + [j for j, _ in uns] +
                [j for j, _, _ in cuts])
    wjs = [j for j, _, _ in ws]
    ujs = [j for j, _ in uns]
    parts = []
    if ws:
        wl = ", ".join(f"{j} (sentence {i}, priority {p})" for j, i, p in ws)
        parts.append(f"Γ's item{'s' if len(ws) > 1 else ''} {wl} {'are' if len(ws) > 1 else 'is'} the clause's "
                     f"equation under the negation of the clauses of a smaller priority that are not `aside` "
                     f"(`prioEquation`, `competingEquation`), a premise the sentence does not state: the sentence "
                     f"entails the item (`prio<j>_w1`, the direction of the class priority equation) and is the item "
                     f"without that premise (`prio<j>_text`); it is not the item (`prio<j>_differs`).")
    if acs:
        al = ", ".join(f"{j} (sentence {i})" for j, i in acs)
        parts.append(f"Γ's item{'s' if len(acs) > 1 else ''} {al} and {'their sentences' if len(acs) > 1 else 'its sentence'} "
                     f"agree up to the order of the operands of their sorted disjunctions and the names of their "
                     f"variables (`ac<j>_same`, `TieAlpha.acEqB`), so the two are satisfied by the same "
                     f"interpretations (`ac<j>_iff`). Such an item is not its sentence as written (`ac<j>_differs`).")
    if rds:
        rl = ", ".join(f"{j} (sentence {i})" for j, i in rds)
        parts.append(f"Γ's item{'s' if len(rds) > 1 else ''} {rl} {'are' if len(rds) > 1 else 'is'} the equation whose "
                     f"right side `\\and{{s'}}(x, y)` the sentence writes `\\and{{s'}}(\\or{{s}}(p, x), y)` or "
                     f"`\\and{{s'}}(\\or{{s}}(x, p), y)`, with an alternative p that holds nothing: `\\bottom{{S}}()`, or "
                     f"an application one of whose arguments is `\\bottom{{S}}()`, an application holding the "
                     f"elements its function part gives at an element of each argument (`TieRhs.emptyB`, "
                     f"`TieRhs.tr_empty`). The reader drops such an alternative (`orBottom`, `Parse.dropEmptyAlts`). "
                     f"The sentence is the item so written (`rd<j>_text`, `TieRhs.orEmptyIn`, up to the indices of "
                     f"its variables), with one variable table, guard list and sort (`rd<j>_ok`), so the two hold in "
                     f"the same models of definedness (`rd<j>_iff`, `TieRhs.orEmptyOK_iff`): Γ entails the sentence "
                     f"(`rd<j>_entailed`) and the sentence entails the item. It is not the item as written "
                     f"(`rd<j>_differs`).")
    if uns:
        ul = ", ".join(f"{j} (sentence {i})" for j, i in uns)
        parts.append(f"Γ's item{'s' if len(uns) > 1 else ''} {ul} {'are' if len(uns) > 1 else 'is'} not "
                     f"{'their sentences' if len(uns) > 1 else 'its sentence'} (`un<j>_differs`), and no reading here "
                     f"gives {'them' if len(uns) > 1 else 'it'} from the sentence or the sentence from "
                     f"{'them' if len(uns) > 1 else 'it'}: the sentence{'s are' if len(uns) > 1 else ' is'} uncovered, "
                     f"`fns_entailed` and `fns_from_text` leave {'them' if len(uns) > 1 else 'it'} out, and the premise "
                     f"set of `gamma_from` holds Γ's item there.")
    if cuts:
        cl = ", ".join(f"{j} (sentence {i}, {'`notAsCondition`' if k['kind'] == 'notCond' else '`andUnderAppCut`'}"
                       f"{'' if k['place'] == ('own',) else ', under a competitor' + chr(39) + 's negation'})"
                       for j, i, k in cuts)
        th = "Γc" if confined else "Γ"
        parts.append(f"Γ's item{'s' if len(cuts) > 1 else ''} {cl} {'are equations' if len(cuts) > 1 else 'is the equation'} "
                     f"whose premise Γ writes through a cut of the clause's `requires` (`KcoreSpec/TieCutEq.lean`): "
                     f"`andUnderAppCut` reads `K[\\and{{S}}(x, u)]` as `K[x]` with the membership `x ∈ u`, and "
                     f"`notAsCondition` reads `\\not{{SortBool{{}}}}(b)` as `b = false`. The sentence is the item "
                     f"with the premise as the text writes it (`cut<j>_same`: `TieCutEq.textItem`, up to the names of "
                     f"its variables, free and bound), and it is not the item (`cut<j>_differs`). Of the two "
                     f"premises, Γ's is inside the text's in every model; the text's is inside Γ's where definedness "
                     f"is read and, for `notAsCondition`, every element of Bool is `true` or `false`; under a "
                     f"competitor's negation the inclusions swap sides. So for `andUnderAppCut` one direction reads "
                     f"definedness only and the other the constructors' facts (`HoldsShape.NodeFacts`, which a model "
                     f"of {th} has: `cut_nodeFacts`), and for `notAsCondition` both read the constructors' facts and "
                     f"the closure of Bool (`boolClosed`), a premise named in `cut<j>_iff` and `cut<j>_entailed`, "
                     f"not Γ's.")
    parts.append("Every other item is the translation of its function sentence (`shape`). -/")
    intro = "\n\n".join(textwrap.fill(x, width=100, break_on_hyphens=False, break_long_words=False) for x in parts)
    out = [f"/-! ## Function equations ({nfe} sentences) and priority equations ({npe} sentences)", "", intro, "",
           "/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority",
           "(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/",
           "noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all", "",
           "/-- **`fnText` is the account's function-equation and priority-equation classes**: the same",
           "indices, each once. -/",
           "theorem fns_account :",
           '    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by',
           "  decide +kernel", ""]
    if acs or rds or cuts:
        out += ["/-- A model of Γ satisfies each of Γ's equations. -/",
                "theorem fnItem_sat {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))",
                "    {j : Nat} {g : P} (hg : (TiePair.gammaPats c)[j]? = some g) : I ⊧ᴵ g := by",
                "  obtain ⟨it, hit, rfl⟩ : ∃ it ∈ fnItems c, it.pat = g := by",
                "    unfold TiePair.gammaPats at hg",
                "    rw [List.getElem?_map] at hg",
                "    cases h : (fnItems c)[j]? with",
                "    | none => rw [h] at hg; cases hg",
                "    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩",
                "  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))", ""]
    for j, i, p in ws:
        out += [f"/-- Γ's axiom of item {j} (sentence {i}, priority {p}). -/",
                f"noncomputable def prioAx{j} : Kore.Axiom := ((TiePair.fnAxioms c)[{j}]?).getD ⟨[], .top KoreAML.R, []⟩",
                f"theorem prioAx{j}_at : (TiePair.fnAxioms c)[{j}]? = some prioAx{j} := by decide +kernel",
                f"noncomputable def prioItem{j} : P := (trAxiom [] [] ⟨0, \"kernel\", prioAx{j}⟩).pat",
                f"theorem prioItem{j}_at : (TiePair.gammaPats c)[{j}]? = some prioItem{j} := TiePair.gammaPats_at prioAx{j}_at",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                "/-- Its premise has the negated conjunct, the clauses of a smaller priority. -/",
                f"theorem prio{j}_narrowed : (TiePair.negParts prioAx{j}.pattern).isSome = true := by decide +kernel",
                f"/-- **Γ's item without the priority premise is the text's sentence {i}** (`TiePair.minusNeg`, up",
                "to the indices of its variables: `TiePair.sameB`; kernel), and it is not the sentence. -/",
                f"theorem prio{j}_text : TiePair.sameB (TiePair.minusNeg prioAx{j}) (trS U.ax{i}).pat = true := by decide +kernel",
                f"theorem prio{j}_differs : prioItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel",
                f"/-- **W1**: the text's sentence {i} entails Γ's item {j}, in every model of definedness. -/",
                f"theorem prio{j}_w1 : TiePair.Texts [(trS U.ax{i}).pat] ⊧ prioItem{j} :=",
                f"  fun {{M}} _ {{I}} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) prio{j}_text",
                "    (hI _ (Or.inl (List.mem_singleton_self _)))", ""]
    for j, i in acs:
        out += [f"/-- Γ's item {j} (sentence {i}). -/",
                f"noncomputable def acItem{j} : P := (TiePair.gammaPats c).getD {j} ⊥",
                f"theorem acItem{j}_at : (TiePair.gammaPats c)[{j}]? = some acItem{j} := by decide +kernel",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                f"/-- **Γ's item {j} and sentence {i} agree** up to the order of the operands of their sorted",
                "disjunctions and the names of their variables (`TieAlpha.acEqB`; kernel), and the item is not the",
                "sentence as written. -/",
                f"theorem ac{j}_same : TieAlpha.acEqB acItem{j} (trS U.ax{i}).pat = true := by decide +kernel",
                f"theorem ac{j}_differs : acItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel",
                f"/-- **Sentence {i} and Γ's item {j} are satisfied by the same interpretations.** -/",
                f"theorem ac{j}_iff {{M : Type}} {{I : Interpretation KoreAML.Sym M}} : (I ⊧ᴵ (trS U.ax{i}).pat) ↔ (I ⊧ᴵ acItem{j}) :=",
                f"  (TieAlpha.acEqB_sat ac{j}_same).symm", "",
                f"/-- **E for sentence {i}**: Γ entails it, for every H (`ac{j}_iff`). -/",
                f"theorem ac{j}_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by",
                "  intro M _ I hI",
                f"  exact ac{j}_iff.mpr (fnItem_sat hI acItem{j}_at)", ""]
    for j, i in rds:
        out += [f"/-- Γ's axiom of item {j} (sentence {i}). -/",
                f"noncomputable def rdAx{j} : Kore.Axiom := ((TiePair.fnAxioms c)[{j}]?).getD ⟨[], .top KoreAML.R, []⟩",
                f"theorem rdAx{j}_at : (TiePair.fnAxioms c)[{j}]? = some rdAx{j} := by decide +kernel",
                f"noncomputable def rdItem{j} : P := (trAxiom [] [] ⟨0, \"kernel\", rdAx{j}⟩).pat",
                f"theorem rdItem{j}_at : (TiePair.gammaPats c)[{j}]? = some rdItem{j} := TiePair.gammaPats_at rdAx{j}_at",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                f"/-- The alternative of sentence {i}'s right side that holds nothing (`TieRhs.emptyAltOf`): whether it",
                "is the first, and it. -/",
                f"noncomputable def rdAlt{j} : Bool × Kore.Pattern :=",
                f"  (TieRhs.emptyAltOf U.ax{i}.ax.pattern).getD (false, .bottom KoreAML.R)",
                f"kernel_rfl rdAlt{j}_eq : TieRhs.emptyAltOf U.ax{i}.ax.pattern = some rdAlt{j}",
                f"/-- The alternative holds nothing, item {j} is an equation whose right side is a conjunction of two,",
                "and the item with the alternative written beside its first conjunct has the item's variable",
                "table, guards and sort (kernel). -/",
                f"theorem rd{j}_ok : TieRhs.orEmptyOK rdAlt{j}.1 rdAlt{j}.2 rdAx{j} = true := by decide +kernel",
                f"/-- **The text's sentence {i} is Γ's item {j} with the alternative written beside its right side's",
                "first conjunct** (`TieRhs.orEmptyIn`, up to the indices of its variables; kernel), and the item is",
                "not the sentence. -/",
                f"theorem rd{j}_text : TiePair.sameB",
                f"    (trAxiom [] [] ⟨0, \"kernel\", TieRhs.rhsMap (TieRhs.orEmptyIn rdAlt{j}.1 rdAlt{j}.2) rdAx{j}⟩).pat",
                f"    (trS U.ax{i}).pat = true := by decide +kernel",
                f"theorem rd{j}_differs : rdItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel",
                f"/-- **Sentence {i} and Γ's item {j} hold in the same models of definedness.** -/",
                f"theorem rd{j}_iff {{M : Type}} {{I : Interpretation KoreAML.Sym M}} (hD : DefOK I) :",
                f"    (I ⊧ᴵ (trS U.ax{i}).pat) ↔ (I ⊧ᴵ rdItem{j}) :=",
                f"  (TiePair.sameB_iff rd{j}_text).trans (TieRhs.orEmptyOK_iff hD rd{j}_ok)", "",
                f"/-- **E for sentence {i}**: Γ entails it, for every H (`rd{j}_iff`). -/",
                f"theorem rd{j}_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by",
                "  intro M _ I hI",
                f"  exact (rd{j}_iff (defOK hI)).mpr (fnItem_sat hI rdItem{j}_at)", ""]
    if cuts:
        th = "Γc" if confined else "Γ"
        out += ["theorem cut_sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by",
                "  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel"]
        if any(k["kind"] == "notCond" for _, _, k in cuts):
            out += ["theorem cut_sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by",
                    "  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel"]
        out += ["", f"/-- A model of {th} has the constructors' facts. -/",
                "theorem cut_nodeFacts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}",
                f"    (hI : I ⊧ᴵP {th} (cH H)) : HoldsShape.NodeFacts (cH H) I :="]
        out += (["  HoldsShape.nodeFacts_of_core (coreOKH H) hI", ""] if confined else
                ["  HoldsShape.nodeFacts_of_core (coreOKH H)",
                 "    (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI)", ""])
    # a model of the theory as a model of Γ, for `fnItem_sat`
    gm = "(fun φ hφ => hI φ (Or.inl hφ))" if confined else "hI"
    for j, i, k in cuts:
        kl, pl = cut_lits(k)
        f = cut_form(k)
        what = ("the `requires` `\\not{SortBool{}}(b)`" if f == "not" else
                "the conjunction at the argument path " + str(k["path"]) + " of the `requires`")
        where = ("" if k["place"] == ("own",) else
                 f", the cut premise the competitor {k['place'][1]}'s under its {k['place'][2]} binders")
        out += [f"/-- Γ's axiom of item {j} (sentence {i}). -/",
                f"noncomputable def cutAx{j} : Kore.Axiom := ((TiePair.fnAxioms c)[{j}]?).getD ⟨[], .top KoreAML.R, []⟩",
                f"theorem cutAx{j}_at : (TiePair.fnAxioms c)[{j}]? = some cutAx{j} := by decide +kernel",
                f"noncomputable def cutItem{j} : P := (trAxiom [] [] ⟨0, \"kernel\", cutAx{j}⟩).pat",
                f"theorem cutItem{j}_at : (TiePair.gammaPats c)[{j}]? = some cutItem{j} := TiePair.gammaPats_at cutAx{j}_at",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                f"/-- The text's form of item {j}: {what}{where}. -/",
                f"noncomputable def cutText{j} : P := (TieCutEq.textItem {kl} {pl} cutAx{j}).getD .bottom",
                f"kernel_rfl cut{j}_text_eq : TieCutEq.textItem {kl} {pl} cutAx{j} = some cutText{j}",
                "/-- The two forms have the same free variables, and the cut premise is of the form the converse",
                "inclusions read (kernel). -/",
                f"theorem cut{j}_shape : TieCutEq.shapeOK {kl} {pl} cutAx{j} = true := by decide +kernel",
                f"theorem cut{j}_facts : TieCutEq.factsOK c {kl} {pl} cutAx{j} = true := by decide +kernel",
                f"/-- **Sentence {i} is the text's form of item {j}** up to the names of the variables (kernel), and",
                "is not the item. -/",
                f"theorem cut{j}_same : TieAlpha.acEqB cutText{j} (trS U.ax{i}).pat = true := by decide +kernel",
                f"theorem cut{j}_differs : cutItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel", ""]
        facts = f"((TieCutEq.factsOK_withHooks c H _ _ _).trans cut{j}_facts)"
        if f == "own":
            out += [f"/-- **Sentence {i} gives Γ's item {j}** in every model of definedness. -/",
                    f"theorem cut{j}_from_text {{M : Type}} {{I : Interpretation KoreAML.Sym M}} (hD : DefOK I)",
                    f"    (h : I ⊧ᴵ (trS U.ax{i}).pat) : I ⊧ᴵ cutItem{j} :=",
                    f"  TieCutEq.cutEq_from_text_pure hD cut{j}_text_eq cut{j}_shape ((TieAlpha.acEqB_sat cut{j}_same).mpr h)", "",
                    f"/-- **E for sentence {i}**: {th} entails it, for every H (`cut_nodeFacts`). -/",
                    f"theorem cut{j}_entailed (H : HookParams) : {th} (cH H) ⊧ (trS U.ax{i}).pat := by",
                    "  intro M _ I hI",
                    f"  exact (TieAlpha.acEqB_sat cut{j}_same).mp (TieCutEq.cutEq_entailed (k := {kl}) (cut_nodeFacts H hI)",
                    f"    (cut_sortOf_true H) (fun h => nomatch h) cut{j}_text_eq cut{j}_shape {facts}",
                    f"    (fnItem_sat {gm} cutItem{j}_at))", ""]
        elif f == "under":
            out += [f"/-- **E for sentence {i}**: Γ entails it, for every H; of the model only definedness is read. -/",
                    f"theorem cut{j}_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by",
                    "  intro M _ I hI",
                    f"  exact (TieAlpha.acEqB_sat cut{j}_same).mp",
                    f"    (TieCutEq.cutEq_entailed_pure (defOK hI) cut{j}_text_eq cut{j}_shape (fnItem_sat hI cutItem{j}_at))", "",
                    f"/-- **Sentence {i} gives Γ's item {j}** in a model with the constructors' facts, for every H. -/",
                    f"theorem cut{j}_from_text (H : HookParams) {{M : Type}} [Inhabited M] {{I : Interpretation KoreAML.Sym M}}",
                    f"    (N : HoldsShape.NodeFacts (cH H) I) (h : I ⊧ᴵ (trS U.ax{i}).pat) : I ⊧ᴵ cutItem{j} :=",
                    f"  TieCutEq.cutEq_from_text (k := {kl}) N (cut_sortOf_true H) (fun h => nomatch h) cut{j}_text_eq cut{j}_shape",
                    f"    {facts} ((TieAlpha.acEqB_sat cut{j}_same).mpr h)", ""]
        else:
            out += [f"/-- **Sentence {i} and Γ's item {j} hold in the same models** among those with the constructors'",
                    "facts in which every element of Bool is `true` or `false`, for every H. -/",
                    f"theorem cut{j}_iff (H : HookParams) {{M : Type}} [Inhabited M] {{I : Interpretation KoreAML.Sym M}}",
                    "    (N : HoldsShape.NodeFacts (cH H) I) (hcl : I ⊧ᴵ boolClosed (cH H)) :",
                    f"    (I ⊧ᴵ (trS U.ax{i}).pat) ↔ (I ⊧ᴵ cutItem{j}) :=",
                    f"  (TieAlpha.acEqB_sat cut{j}_same).symm.trans (TieCutEq.cutEq_iff N (cut_sortOf_true H)",
                    f"    (fun _ => ⟨cut_sortOf_false H, hcl⟩) cut{j}_text_eq cut{j}_shape {facts})", "",
                    f"/-- Sentence {i} holds in a model of {th} in which Bool is closed, for every H. -/",
                    f"theorem cut{j}_entailed (H : HookParams) {{M : Type}} [Inhabited M] {{I : Interpretation KoreAML.Sym M}}",
                    f"    (hI : I ⊧ᴵP {th} (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) : I ⊧ᴵ (trS U.ax{i}).pat :=",
                    f"  (cut{j}_iff H (cut_nodeFacts H hI) hcl).mpr (fnItem_sat {gm} cutItem{j}_at)", ""]
    for j, i in uns:
        out += [f"/-- Γ's item {j} (sentence {i}): no reading here ties it. -/",
                f"noncomputable def unItem{j} : P := (TiePair.gammaPats c).getD {j} ⊥",
                f"theorem unItem{j}_at : (TiePair.gammaPats c)[{j}]? = some unItem{j} := by decide +kernel",
                f"kernel_rfl fnText_at{j} : fnText[{j}]? = some U.ax{i}",
                f"/-- **Γ's item {j} is not the text's sentence {i}** (kernel): the sentence is uncovered. -/",
                f"theorem un{j}_differs : unItem{j} ≠ (trS U.ax{i}).pat := by decide +kernel", ""]
    item = ({j: f"prioItem{j}" for j, _, _ in ws} | {j: f"acItem{j}" for j, _ in acs} |
            {j: f"rdItem{j}" for j, _ in rds} | {j: f"unItem{j}" for j, _ in uns} | {j: f"cutItem{j}" for j, _, _ in cuts})
    tp = "(fnText.map (trS · |>.pat))"
    for j in at:
        tp = f"({tp}.set {j} {item[j]})"
    sl = ", ".join(map(str, at))
    hs = ", ".join(f"h{j}" for j in at)
    ne = ", ".join(f"List.getElem?_set_ne (Ne.symm h{j})" for j in reversed(at))
    split_hn = (f"  obtain ⟨{hs}⟩ := hn" if len(at) > 1 else f"  have h{at[0]} := hn")
    out += ["/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's",
            f"item at {'positions' if len(at) > 1 else 'position'} {sl}. -/",
            f"noncomputable def textPats : List P := {tp[1:-1]}", "",
            "/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's",
            "items (kernel). -/",
            "theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel", "",
            "theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by",
            "  rw [TiePair.gammaPats_withHooks]; exact shape", "",
            "/-- The positions set to Γ's items. -/",
            f"def pairSetAt : List Nat := [{sl}]", "",
            "theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :",
            "    textPats[j]? = some (trS ad).pat := by",
            "  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn",
            split_hn,
            "  unfold textPats",
            f"  rw [{ne}, List.getElem?_map, hj]",
            "  rfl", ""]
    # the cut items whose sentence Γ entails (`fns_entailed` holds them), the others; those whose sentence
    # gives the item in every model of definedness (`fns_from_text` holds them), the others
    ce = [(j, i) for j, i, k in cuts if cut_in_entailed(k, confined)]
    cx = [j for j, _, k in cuts if not cut_in_entailed(k, confined)]
    cf = [j for j, _, k in cuts if cut_form(k) == "own"]
    cy = [j for j, _, k in cuts if cut_form(k) != "own"]
    ex_f = sorted(ujs + cy)
    out_l = ", ".join(map(str, sorted(wjs + ujs + cx)))
    via = [f"item {j} through `ac{j}_iff`" for j, _ in acs] + [f"item {j} through `rd{j}_iff`" for j, _ in rds]
    via_e = via + [f"item {j} by `cut{j}_entailed`" for j, _ in ce]
    via_f = via + [f"item {j} by `cut{j}_from_text`" for j in cf]
    but = ([f"the narrowed ones (items {', '.join(map(str, wjs))})"] if ws else []) + \
        ([f"the untied ones (items {', '.join(map(str, ujs))})"] if uns else []) + \
        ([f"the cut ones whose entailment reads more than Γ (items {', '.join(map(str, cx))})"] if cx else [])
    but_f = ([f"the untied ones (items {', '.join(map(str, ujs))})"] if uns else []) + \
        ([f"the cut ones given with the constructors' facts (items {', '.join(map(str, cy))})"] if cy else [])
    out += [f"/-- **E for the function equations**: Γ entails each sentence of `fnText`"
            + (f" but {' and '.join(but)}" if but else "") + ", for every H"
            + ("; " + ", ".join(via_e) if via_e else "") + ". -/",
            "theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →",
            f"    j ∉ ([{out_l}] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by",
            "  intro j ad hj hn"]
    for j, i in acs + rds + ce:
        ent = f"ac{j}_entailed" if (j, i) in acs else f"rd{j}_entailed" if (j, i) in rds else f"cut{j}_entailed"
        out += [f"  by_cases h{j} : j = {j}",
                f"  · subst h{j}",
                f"    rw [fnText_at{j}] at hj",
                f"    rw [← Option.some.inj hj]",
                f"    exact {ent} H"]
    # with no case before it (every item set to Γ's narrowed or untied), the entailment as the goal of
    # `exact` leaves `Inhabited ?M` stuck: the model is taken apart first there
    out += ["  have hn' : j ∉ pairSetAt := by",
            "    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢",
            "    omega"]
    out += (["  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))", ""] if acs or rds or ce else
            ["  intro M _ I hI",
             "  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI", ""])
    out += ["/-- **The converse for `fnItems`**: each item"
            + (f" but {' and '.join(but_f)}" if but_f else "")
            + " is a consequence of a text sentence, the j-th of `fnText`"
            + ("; the narrowed ones by W1" if ws else "") + ("; " + ", ".join(via_f) if via_f else "")
            + "; the others by their translation. -/",
            "theorem fns_from_text (H : HookParams) :",
            "    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →"
            + (f" j ∉ ([{', '.join(map(str, ex_f))}] : List Nat) →" if ex_f else ""),
            "      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by",
            "  intro j it hj" + (" hu" if ex_f else "")]
    # `hg` and `pick` only where an item set to Γ's is given by its sentence (unused, `pick`'s statement
    # does not elaborate)
    if len(at) > len(ex_f):
        out += ["  have hg : (TiePair.gammaPats c)[j]? = some it.pat := by",
                "    rw [← TiePair.gammaPats_withHooks c H]",
                "    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl",
                "  have pick : ∀ {i : Nat} {g : P} {ad : AxiomDecl}, (TiePair.gammaPats c)[i]? = some g → fnText[i]? = some ad →",
                "      (TiePair.Texts [(trS ad).pat] ⊧ g) → j = i →",
                "      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by",
                "    intro i g ad hgi hti hent hji",
                "    subst hji",
                "    rw [hgi] at hg",
                "    exact ⟨ad, hti, (Option.some.inj hg) ▸ hent⟩"]
    for j in at:
        out.append(f"  by_cases h{j} : j = {j}")
        if j in wjs:
            out.append(f"  · exact pick prioItem{j}_at fnText_at{j} prio{j}_w1 h{j}")
        elif j in ex_f:
            out.append(f"  · subst h{j}; simp at hu")
        elif j in cf:
            out.append(f"  · exact pick cutItem{j}_at fnText_at{j}")
            out.append(f"      (fun {{M}} _ {{I}} hI => cut{j}_from_text (TiePair.defOK_texts hI)")
            out.append(f"        (hI _ (Or.inl (List.mem_singleton_self _)))) h{j}")
        elif j in [x for x, _ in acs]:
            out.append(f"  · exact pick acItem{j}_at fnText_at{j}")
            out.append(f"      (fun {{M}} _ {{I}} hI => ac{j}_iff.mp (hI _ (Or.inl (List.mem_singleton_self _)))) h{j}")
        else:
            out.append(f"  · exact pick rdItem{j}_at fnText_at{j}")
            out.append(f"      (fun {{M}} _ {{I}} hI => (rd{j}_iff (TiePair.defOK_texts hI)).mp")
            out.append(f"        (hI _ (Or.inl (List.mem_singleton_self _)))) h{j}")
    out += ["  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj",
            "  unfold textPats at ht",
            f"  rw [{ne}, List.getElem?_map] at ht",
            "  cases hf : fnText[j]? with",
            "  | none => rw [hf] at ht; cases ht",
            "  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩", "",
            "/-- The priority each function sentence's attributes state is the priority of the clause whose",
            "item it gives, item by item in `fnItems`'s order. -/",
            "theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =",
            "    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel", "",
            "/-! ## The converse over Γ's content -/", "",
            "/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to",
            "Γ's through their sentences" + (", the untied ones as Γ's own" if uns else "")
            + "), Γ's rule items and the five parts Γ defines by predicates",
            "(`TiePair.Pre`), for every H. -/",
            "theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → TiePair.Pre (cH H) textPats ⊧ φ :=",
            "  TiePair.gamma_from (shapeH H)", ""]
    return "\n".join(out) + "\n"


def alpha_block():
    """test/NonExecOwiseTie.lean's patterns equal up to a renaming of element variables (`alphaB`,
    `satisfies_of_alphaB`) and its alignment of items with sentences (`alignB`), as written there."""
    t = open(NEX_TIE).read()
    try:
        a = t.index("\n/-! ## Patterns equal up to the names of their element variables -/") + 1
        b = t.index("\nkernel_rfl fnItems_withHooks", a) + 1
    except ValueError:
        raise Refused("test/NonExecOwiseTie.lean has changed: no alphaB section to copy")
    s = t[a:b]
    if "/-! ## Shared -/\n\n" not in s or "def alignB" not in s or "theorem satisfies_of_alphaB" not in s:
        raise Refused("test/NonExecOwiseTie.lean has changed: its alphaB section lacks alignB or satisfies_of_alphaB")
    return s.replace("/-! ## Shared -/\n\n", "").rstrip("\n") + "\n"


def erase_chain(base, js, piped):
    """`base` without the members at the sorted indices `js`, each erased in turn (an index moves
    down by the members erased before it)."""
    es = [j - k for k, j in enumerate(js)]
    if piped:
        return f"({base}.eraseIdx {es[0]}" + "".join(f" |>.eraseIdx {e}" for e in es[1:]) + ")"
    s = f"{base}.eraseIdx {es[0]}"
    for e in es[1:]:
        s = f"({s}).eraseIdx {e}"
    return f"({s})"


def fn_align_section(fn_text, nonlit):
    a, n = nonlit[0], len(nonlit)
    if nonlit != list(range(a, a + n)):
        raise Refused("the [owise] equations whose items are not their sentences as written are not consecutive in fnItems")
    ow = f"the {numword(n)} `[owise]` equations" if n > 1 else "the `[owise]` equation"
    return f"""/-! ## Function equations ({len(fn_text)} sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's {len(fn_text)} equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  {ax_list(fn_text)}

/-- **The items of the other equations are their sentences' translations, pattern for pattern**
(one kernel decision). -/
theorem fn_shape_but_owise : {erase_chain("(fnItems c)", nonlit, True)}.map (·.pat) =
    {erase_chain("fnText", nonlit, False)}.map (trS · |>.pat) := by
  rw [fnItems_eq]; decide +kernel

/-- The items of {ow} are not their sentences' translations as written: the text
writes the exclusion's bound variable under its own name. -/
theorem owise_not_literal : ((fnItems c).drop {a} |>.take {n}).map (·.pat) ≠
    ((fnText.drop {a}).take {n}).map (trS · |>.pat) := by
  rw [fnItems_eq]; decide +kernel

/-- **Each of Γ's equations is the translation of its text sentence up to a renaming of element
variables, free and bound**, both ways (one kernel decision). -/
theorem fn_align : alignB trS (fnItems c) fnText = true := by
  rw [fnItems_eq]; decide +kernel

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, _, hα⟩ := align_text fn_align had
  exact satisfies_of_alphaB hα (hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, rfl⟩)))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have hl : (fnItems c).length = fnText.length := by
    have := fn_align; simp only [alignB, Bool.and_eq_true, beq_iff_eq] at this; exact this.1
  obtain ⟨hjl, hjit⟩ := List.getElem?_eq_some_iff.mp hj
  have hjt : j < fnText.length := hl ▸ hjl
  refine ⟨fnText[j], List.getElem?_eq_getElem hjt, fun {{M}} _ {{I}} hI => ?_⟩
  have hα := (align_pair fn_align j hjl hjt).2
  rw [hjit] at hα
  exact satisfies_of_alphaB hα (hI _ (Or.inl ⟨trS fnText[j], List.mem_singleton_self _, rfl⟩))

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel
"""


NJ_ALIAS = """/-- The text's alias names, written out. -/
def aliasLit : List String := [@ALIASES@]

theorem aliasLit_eq : kore.aliasNames = aliasLit := by decide +kernel
"""

NJ_TR = """/-- The pattern is a `\\or` at the sort `S`. -/
def njIsOr (S : Kore.KSort) : Kore.Pattern → Bool
  | .or S' _ => decide (S' = S)
  | _ => false

/-- The disjuncts of a `\\or`. -/
def njOrArgs : Kore.Pattern → List Kore.Pattern
  | .or _ ds => ds
  | _ => []

theorem njOr_eq {S : Kore.KSort} {p : Kore.Pattern} (h : njIsOr S p = true) : p = .or S (njOrArgs p) := by
  cases p <;> simp_all [njIsOr, njOrArgs]

/-- Two disjunctions whose operands translate to the same patterns translate to the same pattern. -/
theorem njTrOrList_eq {c1 c2 : Ctx} {s : P} : ∀ {ds1 ds2 : List Kore.Pattern},
    ds1.map (tr c1) = ds2.map (tr c2) → trOrList c1 s ds1 = trOrList c2 s ds2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], [_], h => by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h; simp [trOrList, h]
  | [_], _ :: _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h
  | p1 :: q1 :: qs1, p2 :: q2 :: qs2, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have ih := njTrOrList_eq (c1 := c1) (c2 := c2) (s := s) (ds1 := q1 :: qs1) (ds2 := q2 :: qs2) h2
    simp only [trOrList] at ih ⊢
    rw [h1, ih]

/-- **Two `\\or` sentences at a sort `N` translate to the same pattern** where neither has a sort
variable or a free variable and their disjuncts translate to the same patterns, each under its own
sentence's table: the guards are none, the sort is `N`'s, and the disjunction is the operands'. The
disjuncts need not be equal: the table makes the variables' names positions. -/
theorem njTrOr_pat {d1 d2 : List SymbolDecl} {al1 al2 : List String} {a1 a2 : AxiomDecl} {N : String}
    {ds1 ds2 : List Kore.Pattern}
    (hsv1 : a1.ax.sortVars = []) (hsv2 : a2.ax.sortVars = [])
    (hp1 : a1.ax.pattern = .or (KoreAML.srt N) ds1) (hp2 : a2.ax.pattern = .or (KoreAML.srt N) ds2)
    (hf1 : freeOfList [] ds1 = []) (hf2 : freeOfList [] ds2 = [])
    (hds : ds1.map (tr ⟨tableOf [] (.or (KoreAML.srt N) ds1), al1⟩) =
      ds2.map (tr ⟨tableOf [] (.or (KoreAML.srt N) ds2), al2⟩)) :
    (trAxiom d1 al1 a1).pat = (trAxiom d2 al2 a2).pat := by
  simp only [trAxiom, hsv1, hsv2, hp1, hp2, List.map_nil, List.nil_append, freeOf, hf1, hf2, sortOf, tr]
  rw [njTrOrList_eq hds]
  simp [trSort, trSortApp, KoreAML.srt]
"""


def key_lit(k):
    """A `VarKey` the probe printed (`S`, `E` or `V`, the name, the sort's name), as a Lean literal."""
    kind, n, srt = k
    if kind == "S":
        return f".sortVar {lean_str(n)}"
    return f".{'evar' if kind == 'E' else 'svar'} {lean_str(n)} (.ctor ⟨⟨{lean_str(srt)}⟩⟩ [])"


def gen_lit(g):
    """A `KoreAML.Gen` the probe printed, as a Lean literal."""
    if g[0] == "inj":
        return f".inj {lean_str(g[1])}"
    return f".ctor ⟨{lean_str(g[1])}, [{', '.join(lean_str(x) for x in g[3])}], {lean_str(g[2])}⟩"


def nj_blocks(nm, i, srt_name, gs, ndisj, n, tabs=None):
    """The no-junk sentence `i`'s translation is the item over `gs` at the sort named `srt_name`
    (`njTrOr_pat`), the translations of its `ndisj` disjuncts compared with the item's by ranges of
    `n` (`tieEq_range`): the definitions and range theorems, and the tactic lines that prove the
    equation from them. `tabs`: the sentence's and the item's tables as the probe printed them,
    written out with an equation each (`{nm}_tabT_eq`, `{nm}_tabI_eq`) so that no range recomputes
    them; `srt_name` and `gs` are then literals."""
    ds_t, ds_i = f"(njOrArgs U.ax{i}.ax.pattern)", f"(KoreAML.noJunkDisjuncts {srt_name} [] {gs})"
    tab_t = f"tableOf [] (.or (KoreAML.srt {srt_name}) {ds_t})"
    tab_i = f"tableOf [] (.or (KoreAML.srt {srt_name}) {ds_i})"
    lt, li = f"{nm}_trT", f"{nm}_trI"
    out = [f"theorem {nm}_sv : U.ax{i}.ax.sortVars = [] := by decide +kernel",
           f"theorem {nm}_or : njIsOr (KoreAML.srt {srt_name}) U.ax{i}.ax.pattern = true := by decide +kernel",
           f"theorem {nm}_free : freeOfList [] {ds_t} = [] := by decide +kernel",
           f"theorem {nm}_ifree : freeOfList [] {ds_i} = [] := by decide +kernel",
           ""]
    if tabs:
        out += ["/-- The tables of the sentence and of the item, written out. -/",
                f"def {nm}_tabT : VarTable :=",
                "  [" + wrap_nums([key_lit(k) for k in tabs[0]], 3) + "]",
                f"theorem {nm}_tabT_eq : {tab_t} = {nm}_tabT := by",
                "  decide +kernel",
                f"def {nm}_tabI : VarTable :=",
                "  [" + wrap_nums([key_lit(k) for k in tabs[1]], 3) + "]",
                f"theorem {nm}_tabI_eq :",
                f"    {tab_i} = {nm}_tabI := by",
                "  decide +kernel",
                ""]
        tab_t, tab_i = f"{nm}_tabT", f"{nm}_tabI"
    out += ["/-- The translations of the sentence's disjuncts, under its table, and of the item's. -/",
            f"noncomputable def {lt} : List P :=",
            f"  {ds_t}.map (tr ⟨{tab_t}, aliasLit⟩)",
            f"noncomputable def {li} : List P :=",
            f"  {ds_i}.map",
            f"    (tr ⟨{tab_i}, []⟩)",
            ""]
    rs = ranges(ndisj, 0, n)
    for a, ln in rs:
        if ln is None:
            out.append(f"theorem {nm}_d{a} : {lt}.drop {a} = {li}.drop {a} := by decide +kernel")
        else:
            out.append(f"theorem {nm}_d{a} : ({lt}.drop {a}).take {ln} = ({li}.drop {a}).take {ln} := by decide +kernel")
    out += [f"/-- The translations of the disjuncts are the item's, by ranges of {n}. -/",
            f"theorem {nm}_ds : {lt} = {li} :="]
    chain = "".join(f"    tieEq_range (l := {lt}) (m := {li}) (a := {a}) (n := {ln}) {nm}_d{a} <|\n"
                    for a, ln in rs[:-1])
    out[-1] += "\n" + (chain + f"    {nm}_d{rs[-1][0]}")[2:]
    out.append("")
    rw = f"rw [{nm}_tabT_eq, {nm}_tabI_eq, aliasLit_eq]" if tabs else "rw [aliasLit_eq]"
    proof = (f"  exact njTrOr_pat (d2 := []) (al2 := []) (a2 := ⟨0, \"kernel\", KoreAML.Cons.noJunkAx {srt_name} {gs}⟩)\n"
             f"    {nm}_sv rfl (njOr_eq {nm}_or) rfl {nm}_free {nm}_ifree (by {rw}; exact {nm}_ds)")
    return "\n".join(out), proof


def nojunk_sort_section(i, e, sn, rawd, new, blocks=0):
    """The no-junk sentence `i` of a sort with generators other than KItem (`e`: the probe's
    match): the item over the sort's generators in the text's order, entailed by Γ for every H.
    `blocks`: the order by ranges of that many disjuncts (`nj_blocks`; 0: one decision)."""
    s, S = sn[e["srt"]], e["sort"]
    gr = [(k, r) for k, r, _ in rawd if k["res"] == e["srt"]]
    srt = lambda x: sn.get(x, str(x))
    out = []
    if new:
        out += [f"/-- {S}, a sort with generators. -/", f"def {s} : Srt := {e['srt']}", "",
                f'theorem {s}_name : c.sortName {s} = "{S}" := by decide +kernel', ""]
    if e["form"] == "perm":
        pm = e["perm"]
        gs = ", ".join(f"g{j}" for j in range(len(pm)))
        # a list pattern of many elements is no pattern Lean takes: past 5 generators (the probe's
        # enumeration) the order is the generators' positions
        body = [f"  match (c.gens {s}).map (Gen.toK c) with",
                f"  | [{gs}] => [{', '.join(f'g{j}' for j in pm)}]",
                "  | gs => gs"] if len(pm) <= 5 else \
            [f"  ([{wrap_nums([str(j) for j in pm], 4)}] : List Nat).filterMap",
             f"    (((c.gens {s}).map (Gen.toK c))[·]?)"]
        out += [f"/-- {S}'s generators in the order the text's no-junk sentence ({i}) lists them, a permutation",
                "of those `Semantics.gens` lists. -/",
                f"noncomputable def {s}TextGens : List KoreAML.Gen :="] + body + ["",
                ] + ([nj_blocks(f"nojunk_{s}", i, f"(c.sortName {s})", f"{s}TextGens", e["ngens"] + 1, blocks)[0]]
                     if blocks else []) + [
                f"/-- {S}'s no-junk sentence ({i}) is the item over {S}'s generators in the text's order. -/",
                f"theorem nojunk_{s}_order : (trS U.ax{i}).pat = (KoreAML.Cons.noJunkItem (c.sortName {s}) {s}TextGens).pat := by",
                nj_blocks(f"nojunk_{s}", i, f"(c.sortName {s})", f"{s}TextGens", e["ngens"] + 1, blocks)[1]
                if blocks else "  decide +kernel",
                f"theorem nojunk_{s}_members : {s}TextGens.isPerm ((c.gens {s}).map (Gen.toK c)) = true := by",
                "  decide +kernel"]
    else:
        go = f"((gensInOrder c defn.pres {s}).map (Gen.toK c))"
        nb = nj_blocks(f"nojunk_{s}", i, f"(c.sortName {s})", go, e["ngens"] + 1, blocks) if blocks else None
        out += ([nb[0]] if blocks else []) + [
                f"/-- {S}'s no-junk sentence ({i}) is the item over {S}'s generators in the text's order, the same",
                "generators as `Semantics.gens` lists. -/",
                f"theorem nojunk_{s}_order : (trS U.ax{i}).pat =",
                f"    (KoreAML.Cons.noJunkItem (c.sortName {s}) {go}).pat := by",
                nb[1] if blocks else "  decide +kernel",
                f"theorem nojunk_{s}_members :",
                f"    ((gensInOrder c defn.pres {s}).map (Gen.toK c)).isPerm ((c.gens {s}).map (Gen.toK c)) = true := by",
                "  decide +kernel"]
    names = [f"nojunk_{s}_order", f"nojunk_{s}_members"]
    if gr:
        og = " ∧ ".join(f"c.isOpenGen (.ctor ⟨{r}, [{', '.join(srt(a) for a in k['args'])}], {s}⟩) = true" for k, r in gr)
        nm = f"nojunk_{s}_{gr[0][1]}" if len(gr) == 1 else f"nojunk_{s}_open"
        out += [f"theorem {nm} : ((c.gens {s}).map (Gen.toK c)).length = {e['ngens']} ∧ {og} := by",
                "  decide +kernel"]
        names.append(nm)
    members = ("(List.isPerm_iff.mp nojunk_" + s + "_members).mem_iff.mpr hg")
    out += ["",
            f"/-- **E for {S}'s no junk ({i})**, for every H (`noJunkItem_of_subset`). -/",
            f"theorem nojunk_{s}_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by",
            "  intro M _ I hI",
            f"  rw [nojunk_{s}_order]",
            f"  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens {s}).map (Gen.toK c))",
            f"    (fun g hg => {members}) ?_",
            f"  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := {s})",
            f"    (show {s} ∈ consSorts c by decide +kernel) (show (c.gens {s}).isEmpty = false by decide +kernel), rfl⟩)",
            ""]
    names.append(f"nojunk_{s}_entailed")
    return "\n".join(out), names


IDEM_RAW = [
    ("theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel",
     "theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by\n  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel"),
    ("  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel", "  simp only [Semantics.sortsOf, s1_sort H]"),
]


def ovl_eq_section(ovl_eq):
    """The overload axioms: each `tieOvlEqB` (kernel), Γ entails it for every H."""
    return "\n".join([
        "/-! ## The overload axioms -/",
        "",
        "/-- The sentences of the class overload equation, in text order. -/",
        "noncomputable def ovlEqText : List AxiomDecl :=",
        "  " + ax_list(ovl_eq),
        "",
        "theorem ovleq_account : (classOf \"overload equation\").isPerm (ovlEqText.map (·.index)) = true := by",
        "  decide +kernel",
        "",
        "/-- Each is an overload axiom of the semantics: of an overloading symbol over a symbol it overloads,",
        "in the form `tieOvlEq_entailed` reads (`tieOvlEqB`; kernel). -/",
        "theorem ovleq_checked : ovlEqText.all (fun ad => tieOvlEqB c ad.ax) = true := by decide +kernel",
        "",
        "theorem ovleq_trS : ovlEqText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by",
        "  decide +kernel",
        "",
        "/-- **E for the overload axioms**: Γ entails each, for every H. Γ's overload equation states, at",
        "every element of the overloaded symbol's argument sorts, that the overloading symbol applied to",
        "their lifts is the lift of the overloaded symbol applied to them (`tieOvlEq_entailed`). -/",
        "theorem ovleq_entailed (H : HookParams) : ∀ ad ∈ ovlEqText, Γ (cH H) ⊧ (trS ad).pat := by",
        "  intro ad had M _ I hI",
        "  rw [of_decide_eq_true (List.all_eq_true.mp ovleq_trS ad had)]",
        "  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)",
        "  exact tieOvlEq_entailed (c := cH H) (a := ad.ax)",
        "    ((tieOvlEqB_withHooks c H ad.ax).trans (List.all_eq_true.mp ovleq_checked ad had)) ad.index ad.module hI",
        ""])


def ovl_nc_section(ovl_nc):
    """The no-confusion sentences of two symbols that meet at values: each `tieOvlNcB` (kernel), refuted
    by every model of Γ for every H."""
    return "\n".join([
        "/-! ## The no-confusion sentences of two symbols that meet: refuted -/",
        "",
        "/-- The sentences of `ovlRefuted`, in text order. -/",
        "noncomputable def ovlNcText : List AxiomDecl :=",
        "  " + ax_list(ovl_nc),
        "",
        "theorem ovlnc_index : ovlNcText.map (·.index) = ovlRefuted := by decide +kernel",
        "",
        "/-- Each is the no-confusion sentence of two symbols, at values of whose argument sorts the two",
        "have one normal form: values of the overloaded symbol's argument sorts and their lifts to the",
        "overloading symbol's (`tieOvlNcB`; kernel). -/",
        "theorem ovlnc_checked : ovlNcText.all (fun ad => tieOvlNcB c ad.ax) = true := by decide +kernel",
        "",
        "kernel_rfl ovlnc_wh : ∀ H : HookParams,",
        "  ovlNcText.all (fun ad => tieOvlNcB (cH H) ad.ax) = ovlNcText.all (fun ad => tieOvlNcB c ad.ax)",
        "",
        "theorem ovlnc_trS : ovlNcText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by",
        "  decide +kernel",
        "",
        "/-- **Γ refutes each**, for every H: in every model of Γ the two symbols build the element of the",
        "values' normal form from the values' elements (`Faithful.norm_gs`, by the overload equation), so the",
        "sentence's conjunction holds of it at the valuation sending its variables to those elements",
        "(`tieOvlNc_refuted`): Γ with the sentence has no model. -/",
        "theorem ovlnc_refuted (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}",
        "    (hI : I ⊧ᴵP Γ (cH H)) : ∀ ad ∈ ovlNcText, ¬ (I ⊧ᴵ (trS ad).pat) := by",
        "  intro ad had",
        "  rw [of_decide_eq_true (List.all_eq_true.mp ovlnc_trS ad had)]",
        "  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)",
        "  exact tieOvlNc_refuted hI (List.all_eq_true.mp ((ovlnc_wh H).trans ovlnc_checked) ad had) ad.index ad.module",
        ""])


def tok_omit_doc(i, sorts):
    """The header's paragraph on KItem's no-junk sentence `i`, which leaves out the injections from the
    sorts `sorts` (the probe's), listed apart."""
    names = ", ".join(e["sort"] for e in sorts)
    valued = [e["sort"] for e in sorts if e["valued"]]
    para = (f"- KItem's no-junk sentence ({i}), weaker under tokKItem, listed apart: it lists KItem's generators "
            f"but `inj{{X, KItem}}` for X in `tokKItemSorts` ({names}), {'sorts' if len(sorts) > 1 else 'a sort'} "
            "the definition holds below KItem (`Parse.ReadingNote.tokKItem`, `tokkitem_sub`; `tokkitem_text`). "
            "It entails Γ's no-junk item of KItem in every interpretation with definedness "
            "(`tokkitem_entails_item`), an item of Γ for every H (`tokkitem_item_in_gamma`). In a model of Γ it "
            "holds exactly where no sort of `tokKItemSorts` has an element (`tokkitem_holds_iff_empty`): Γ's "
            "Cons-Fun item of `inj{X, KItem}` gives an element of X an image in KItem, and Γ's Cons-Dist items, "
            "which it holds through the reading's subsort, put that image apart from the image of each injection "
            "the sentence lists; the text states neither that the image is apart from those nor that it meets them. ")
    if valued:
        para += (f"{', '.join(valued)} {'have values' if len(valued) > 1 else 'has a value'} the reader exhibits "
                 "(`tokkitem_exhibit`), so Γ with the sentence has no model, for every H (`tokkitem_refuted`).")
    else:
        para += ("No model of Γ satisfies it together with the text's G-nonempty item of a sort of "
                 "`tokKItemSorts` (`tokkitem_nonempty_in_text`, `tokkitem_refuted_with_nonempty`), for every H.")
    return textwrap.fill(para, width=100, initial_indent="  ", subsequent_indent="    ", break_on_hyphens=False,
                         break_long_words=False)


def tok_omit_section(i, sorts):
    """KItem's no-junk sentence `i`, which leaves out the injections from the sorts `sorts` (the probe's
    `omit`, with `kitemOmitB`): the theorems of KcoreSpec/TieTokKItem.lean at the text's literals."""
    ids = ", ".join(str(e["srt"]) for e in sorts)
    names = ", ".join(lean_str(e["sort"]) for e in sorts)
    valued = [e for e in sorts if e["valued"]]
    L = [f"/-! ## KItem's no-junk sentence ({i}) without the injections from sorts below KItem: weaker under",
         "tokKItem, listed apart -/",
         "",
         f"/-- The sorts of the definition whose injections into KItem sentence {i} does not list. -/",
         f"def tokKItemSorts : List Srt := [{ids}]",
         "",
         f"theorem tokkitem_index : tokKItemApart = [{i}] := by decide +kernel",
         f"theorem tokkitem_sorts_named : tokKItemSorts.map c.sortName = [{names}] := by decide +kernel",
         "",
         "/-- Each is a sort of the definition below KItem (`Parse.ReadingNote.tokKItem`). -/",
         "theorem tokkitem_sub : tokKItemSorts.all (fun x => c.subsorts.contains (x, Srt.kitem)) = true := by",
         "  decide +kernel",
         "",
         f"/-- The generators of KItem sentence {i} lists: KItem's generators in kompile's order but the",
         "injections from `tokKItemSorts`. -/",
         "noncomputable def tokKItemGens : List Gen := kitemOmitGens c defn.pres tokKItemSorts",
         "",
         f"/-- Sentence {i} is the no-junk sentence of KItem over `tokKItemGens`. -/",
         f"theorem tokkitem_text : (trS U.ax{i}).pat =",
         "    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (tokKItemGens.map (Gen.toK c))).pat := by decide +kernel",
         "",
         "/-- The left-out sorts and the listed generators are as the lemmas of `kitemOmitB` ask: each",
         "listed generator an injection that is not open, from a sort incomparable with each left-out sort",
         "and with no lower bound in common with it; each generator of KItem listed or from a left-out sort. -/",
         "theorem tokkitem_ok : kitemOmitB c tokKItemSorts tokKItemGens = true := by decide +kernel",
         "theorem tokkitem_kitem_cons : Srt.kitem ∈ consSorts c := by decide +kernel",
         "theorem tokkitem_noFnOvl : c.fnOvlSyms = [] := by decide +kernel",
         "",
         "/-- **The sentence entails Γ's no-junk item of KItem, in every interpretation with definedness**",
         "(`kitemOmit_entails_item`). -/",
         "theorem tokkitem_entails_item {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)",
         f"    (h : I ⊧ᴵ (trS U.ax{i}).pat) :",
         "    I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c))).pat := by",
         "  rw [tokkitem_text] at h",
         "  exact kitemOmit_entails_item tokkitem_ok hD h",
         "",
         "/-- That item is Γ's, for every H. -/",
         "theorem tokkitem_item_in_gamma (H : HookParams) :",
         "    KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c)) ∈ consItemsK (cH H) :=",
         "  kitemOmit_item_in_gamma tokkitem_ok tokkitem_kitem_cons H",
         "",
         f"/-- **In a model of Γ, sentence {i} holds exactly where no sort of `tokKItemSorts` has an element**,",
         "for every H (`kitemOmit_holds_iff_empty`). -/",
         "theorem tokkitem_holds_iff_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}",
         f"    (hI : I ⊧ᴵP Γ (cH H)) : (I ⊧ᴵ (trS U.ax{i}).pat) ↔ ∀ x ∈ tokKItemSorts, ¬ ∃ y, InS I (c.sortName x) y := by",
         "  rw [tokkitem_text]",
         "  exact kitemOmit_holds_iff_empty tokkitem_ok tokkitem_kitem_cons tokkitem_noFnOvl H hI",
         ""]
    if valued:
        x = valued[0]
        L += [f"/-- The reader exhibits a value of {x['sort']} (`Parse.exhibit?`). -/",
              f"theorem tokkitem_exhibit : (Parse.exhibit? c {x['srt']}).isSome = true := by decide +kernel",
              "",
              f"/-- **Γ with sentence {i} has no model**, for every H: the exhibited value's element is an element of",
              f"{x['sort']} in every model of Γ (`kitemOmit_refuted_exhibit`). -/",
              "theorem tokkitem_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax{i}).pat) := by",
              "  intro M _ I hI",
              "  rw [tokkitem_text]",
              "  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp tokkitem_exhibit",
              f"  exact kitemOmit_refuted_exhibit tokkitem_ok tokkitem_kitem_cons tokkitem_noFnOvl H (x := {x['srt']})",
              "    (by decide) hv hI",
              ""]
    else:
        L += ["/-- The text's G-nonempty item of each sort of `tokKItemSorts` is one of its translation's",
              "signature items. -/",
              "theorem tokkitem_nonempty_in_text : tokKItemSorts.all (fun x => (Theory.ofDefinition kore).signature.any",
              "    (·.pat == (nonemptyItem ⟨\"Sort\" ++ c.sortName x, [], false⟩).pat)) = true := by",
              "  decide +kernel",
              "",
              f"/-- **For every H, no model of Γ satisfies sentence {i} together with the text's G-nonempty item",
              "of a sort of `tokKItemSorts`** (`kitemOmit_refuted_nonempty`). -/",
              "theorem tokkitem_refuted_with_nonempty (H : HookParams) {M : Type} [Inhabited M]",
              f"    {{I : Interpretation KoreAML.Sym M}} (hI : I ⊧ᴵP Γ (cH H)) (h : I ⊧ᴵ (trS U.ax{i}).pat) :",
              "    ∀ x ∈ tokKItemSorts, ¬ (I ⊧ᴵ (nonemptyItem ⟨\"Sort\" ++ c.sortName x, [], false⟩).pat) := by",
              "  intro x hx hne",
              "  rw [tokkitem_text] at h",
              "  exact kitemOmit_refuted_nonempty tokkitem_ok tokkitem_kitem_cons tokkitem_noFnOvl H hx hI hne h",
              ""]
    return "\n".join(L)


# the forms of the covered part of a sentence of `ovlFnApart` the hand section (`--hand ovlfn`) states,
# each by the names it defines: at values for every H; refuted for every H (the sentence also in
# `ovlFnRefuted`); or owed under a hypothesis on H, with an H at which it holds and one at which it fails
OVL_FN_FORMS = {"at_values": ("ovlfn_at_values_{}",),
                "refuted": ("ovlfn_refuted_{}",),
                "hypothesis": ("OvlFnHyp{}", "ovlfn_hyp_at_values_{}", "ovlfn_hyp_holds_{}", "ovlfn_hyp_fails_{}")}
OVL_FN_KIND = {"fun": "the `functional` sentence", "inj": "the same-constructor sentence",
               "dist": "a different-constructors sentence"}


def ovl_fn_rows_of(name, ovl_fn, head, sents):
    """Per sentence of `ovlFnApart`, from the probe's `OF` rows: its kind, sort, generators, and the
    `functional` sentence of `ovlFnApart` it is joint with (`jf`, the sentence itself for a `functional`
    one) with the position of that sentence's generator among the sentence's (`gf`); and the distinct
    generators, in order of first appearance. Refused where a sentence has no row or several, where
    its sort is not one of the semantics', or where no `functional` sentence of the text that
    `tieOvlFnFunAtB` accepts at the generator, with Γ's arity item of it (`tieOvlFnArityB`), is there
    to be joint with."""
    rows, gens = {}, []
    of = head.get("ovlFn", {})
    for i in ovl_fn:
        rs = of.get(i, [])
        if len(rs) != 1 or rs[0]["kind"] != sents[i]["ovlFn"]:
            raise Refused(f"{name}: sentence {i} is of a function-overloaded symbol, but the probe gives "
                          f"{len(rs)} sorts and generators it is that sentence at (one is stated)")
        r = rs[0]
        if not r["numbered"]:
            raise Refused(f"{name}: sentence {i}: its sort {r['sort']} is not one of the semantics' numbered sorts")
        for g in r["gens"]:
            if g["lit"] not in gens:
                gens.append(g["lit"])
        funs = [j for j in ovl_fn if j in of and of[j][0]["kind"] == "fun" and of[j][0]["srt"] == r["srt"]]
        cands = [(p, j) for p, g in enumerate(r["gens"]) if g["fnOvl"]
                 for j in funs if of[j][0]["gens"][0]["lit"] == g["lit"]]
        if r["kind"] == "fun":
            cands = [(0, i)]
        if not cands:
            raise Refused(f"{name}: sentence {i} ({r['kind']}) is joint with the `functional` sentence of its "
                          f"function-overloaded generator, which the text does not state")
        p, j = cands[0]
        if not r["gens"][p]["arity"]:
            raise Refused(f"{name}: sentence {i}: Γ holds no arity item of the generator {r['gens'][p]['sym']} in "
                          f"the form `tieOvlFnArityB` reads")
        rows[i] = dict(kind=r["kind"], srt=r["srt"], sort=r["sort"], gens=[g["lit"] for g in r["gens"]],
                       syms=[g["sym"] for g in r["gens"]], jf=j, gf=p)
    return rows, gens


def ovl_fn_hand_of(name, ovl_fn, text):
    """The form of the covered part the hand section states for each sentence of `ovlFnApart`, read
    from the names it defines (`OVL_FN_FORMS`), and those names. Refused where it states none or
    several for a sentence, or where `ovlFnRefuted` lists a sentence it does not refute."""
    if text is None:
        raise Refused(f"{name}: sentences {', '.join(map(str, ovl_fn))} are of a function-overloaded symbol "
                      f"(`ovlFnApart`): what each says at covered arguments is stated by hand (--hand ovlfn=FILE)")
    has = lambda n: re.search(r"^(?:noncomputable )?(?:theorem|def|abbrev) " + re.escape(n) + r"(?![\w'])", text, re.M)
    m = re.search(r"^(?:noncomputable )?def ovlFnRefuted : List Nat := \[([^\]]*)\]", text, re.M)
    listed = [int(x) for x in re.findall(r"\d+", m.group(1))] if m else []
    out = {"at_values": [], "refuted": [], "hypothesis": [], "names": [] + (["ovlFnRefuted"] if m else [])}
    for i in ovl_fn:
        forms = [f for f, ns in OVL_FN_FORMS.items() if all(has(n.format(i)) for n in ns)
                 and (f != "refuted" or i in listed)]
        if len(forms) != 1:
            raise Refused(f"{name}: --hand ovlfn " + ("leaves" if not forms else f"states {' and '.join(forms)} for")
                          + f" sentence {i}" + (" without its covered part: one of " + "; ".join(
                              ", ".join(n.format(i) for n in ns) + (f" (with {i} in `ovlFnRefuted`)" if f == "refuted" else "")
                              for f, ns in OVL_FN_FORMS.items()) if not forms else ": one is stated"))
        out[forms[0]].append(i)
        out["names"] += [n.format(i) for n in OVL_FN_FORMS[forms[0]]]
    stray = [i for i in listed if i not in out["refuted"]]
    if stray:
        raise Refused(f"{name}: --hand ovlfn: `ovlFnRefuted` lists {', '.join(map(str, stray))}, no sentence of "
                      f"`ovlFnApart` the section refutes (`ovlfn_refuted_<i>`)")
    if out["refuted"] and listed != out["refuted"]:
        raise Refused(f"{name}: --hand ovlfn: `ovlFnRefuted` is not in text order")
    return out


def ovl_fn_doc(ovl_fn, rows, hand):
    """The header's paragraph on the sentences of a function-overloaded symbol, listed apart."""
    what = "; ".join(f"{i}, {OVL_FN_KIND[rows[i]['kind']]} of `{rows[i]['syms'][0]}`"
                     + (f" and `{rows[i]['syms'][1]}`" if rows[i]["kind"] == "dist" else "") for i in ovl_fn)
    para = (f"- Sentences of a function-overloaded symbol ({what}), weaker under overloadFunction, listed apart "
            "(`ovlFnApart`): Γ holds each at the arguments no overload covers only. Part 1, for every H: in a "
            "model of Γ the sentence, with the `functional` sentence it is joint with, entails Γ's item at "
            "uncovered arguments (`ovlfn_text_<i>`, `ovlfn_entails_item_<i>`), which is Γ's "
            "(`ovlfn_item_in_gamma_<i>`). Part 2, what it says at covered arguments, by hand: ")
    parts = []
    if hand["at_values"]:
        parts.append(f"at values for every H ({', '.join(map(str, hand['at_values']))}; `ovlfn_at_values_<i>`)")
    if hand["refuted"]:
        parts.append(f"refuted for every H ({', '.join(map(str, hand['refuted']))}; `ovlFnRefuted`, "
                     "`ovlfn_refuted_<i>`)")
    if hand["hypothesis"]:
        parts.append(f"owed under a hypothesis on H ({', '.join(map(str, hand['hypothesis']))}; `OvlFnHyp<i>`, "
                     "`ovlfn_hyp_at_values_<i>`, with an H at which it holds, `ovlfn_hyp_holds_<i>`, and one at "
                     "which it fails, `ovlfn_hyp_fails_<i>`)")
    para += "; ".join(parts) + "."
    return textwrap.fill(para, width=100, initial_indent="  ", subsequent_indent="    ", break_on_hyphens=False,
                         break_long_words=False)


def ovl_fn_item(kind, srt, ga, gb=None, h="(cH H)"):
    """Γ's item at uncovered arguments of a sentence of the kind, over the generators' definitions."""
    if kind == "fun" or kind == "inj":
        it = "funUncItem" if kind == "fun" else "injUncItem"
        return (f"(KoreAML.Cons.{it} ({h}.sortName {srt}) (Gen.toK {h} {ga}) ((ovlArgsOf {h} {ga}).getD [])).pat")
    return (f"(KoreAML.Cons.distUncItem ({h}.sortName {srt}) (Gen.toK {h} {ga}) (Gen.toK {h} {gb}) "
            f"(ovlArgsOf {h} {ga}) (ovlArgsOf {h} {gb})).pat")


def ovl_fn_entails(i, r, gname):
    """The binders and the conclusion of `ovlfn_entails_item_<i>`, after `H`, `M` and `I`, and before
    the model hypothesis (`hI`)."""
    ga = gname[r["gens"][0]]
    gb = gname[r["gens"][1]] if r["kind"] == "dist" else None
    hyps = ([f"(hf : I ⊧ᴵ (trS U.ax{r['jf']}).pat) "] if r["jf"] != i else []) + [f"(h : I ⊧ᴵ (trS U.ax{i}).pat)"]
    if r["kind"] == "dist":
        concl = (f"(I ⊧ᴵ {ovl_fn_item('dist', r['srt'], ga, gb)}) ∧\n"
                 f"    (I ⊧ᴵ {ovl_fn_item('dist', r['srt'], gb, ga)})")
    else:
        concl = f"I ⊧ᴵ {ovl_fn_item(r['kind'], r['srt'], ga)}"
    return "".join(hyps), concl


def ovl_fn_section(ovl_fn, rows, gens):
    """Part 1 of the sentences of `ovlFnApart`, for every H: each is the sentence of its kind of a
    function-overloaded generator (`tieOvlFnFunAtB`, `tieOvlFnInjAtB`, `tieOvlFnDistAtB`; kernel), Γ holds
    its item at uncovered arguments (`tieOvlFn*_item_withHooks`), and in a model of Γ it entails that
    item with the `functional` sentence it is joint with (`tieOvlFn*_weaker_Γ`)."""
    gname = {g: f"ovlFnGen{k}" for k, g in enumerate(gens)}
    srts = sorted({r["srt"] for r in rows.values()})
    L = [f"/-! ## Sentences of a function-overloaded symbol ({', '.join(map(str, ovl_fn))}): weaker under",
         "overloadFunction, listed apart",
         "",
         "Γ holds each sentence at the arguments no overload of its generator covers only (Γ's items",
         "`funUncItem`, `injUncItem`, `distUncItem`). This section states what holds for every H on every",
         "text: the sentence entails that item in a model of Γ, the same-constructor and",
         "different-constructors sentences with the `functional` sentence of their function-overloaded",
         "generator. What a sentence says at covered arguments is the next section's, by hand. -/",
         "",
         "/-- The sentences of `ovlFnApart`, in text order. -/",
         "noncomputable def ovlFnText : List AxiomDecl :=",
         "  " + ax_list(ovl_fn),
         "",
         "theorem ovlfn_index : ovlFnText.map (·.index) = ovlFnApart := by decide +kernel",
         ""]
    for g in gens:
        sym = next(r["syms"][k] for r in rows.values() for k, x in enumerate(r["gens"]) if x == g)
        L += [f"/-- The generator `{sym}`. -/", f"def {gname[g]} : Gen := {g}", ""]
    names = " ∧ ".join(f"c.sortName {x} = {lean_str(next(r['sort'] for r in rows.values() if r['srt'] == x))}" for x in srts)
    L += ["/-- The sorts of these generators are the semantics' sorts, named: -/",
          f"theorem ovlfn_sorts : {' ∧ '.join(f'{x} < nRegSorts + c.sortNames.length' for x in srts)} := by decide +kernel",
          f"theorem ovlfn_sort_names : {names} := by decide +kernel",
          "",
          "/-- Γ holds the G-arity item of each generator whose `functional` sentence the others are joint",
          "with (`tieOvlFnArityB`). -/"]
    fgens = []
    for i in ovl_fn:
        r = rows[i]
        key = (r["srt"], r["gens"][r["gf"]])
        if key not in fgens:
            fgens.append(key)
    arity = {k: f"ovlfn_arity_{n}" for n, k in enumerate(fgens)}
    for (x, g), n in arity.items():
        L.append(f"theorem {n} : tieOvlFnArityB c {x} {gname[g]} = true := by decide +kernel")
    L.append("")
    srt_ix = {x: k for k, x in enumerate(srts)}
    numbered = lambda x: "ovlfn_sorts" + ".2" * srt_ix[x] + (".1" if srt_ix[x] < len(srts) - 1 else "")
    pred = {"fun": "Fun", "inj": "Inj", "dist": "Dist"}
    for i in ovl_fn:
        r = rows[i]
        P = pred[r["kind"]]
        x = r["srt"]
        ga = gname[r["gens"][0]]
        gb = gname[r["gens"][1]] if r["kind"] == "dist" else None
        gargs = f"{ga} {gb}" if gb else ga
        j, gf = r["jf"], gname[r["gens"][r["gf"]]]
        hyps, concl = ovl_fn_entails(i, r, gname)
        L += [f"/-- Sentence {i} is {OVL_FN_KIND[r['kind']]} of `{r['syms'][0]}`"
              + (f" and `{r['syms'][1]}`" if gb else "") + f" of {r['sort']}"
              + ("" if j == i else f", joint with the `functional` sentence {j}") + ". -/",
              f"theorem ovlfn_text_{i} : tieOvlFn{P}AtB c {x} {gargs} U.ax{i}.ax = true := by decide +kernel",
              f"theorem ovlfn_trS_{i} : (trS U.ax{i}).pat = (trAxiom [] [] U.ax{i}).pat := by decide +kernel",
              "",
              f"/-- Γ holds its item at uncovered arguments, for every H{'' if gb else ''}"
              + (" (in one of the two orders)" if gb else "") + ". -/",
              f"theorem ovlfn_item_in_gamma_{i} (H : HookParams) :"]
        if gb:
            L += [f"    (∃ it ∈ consItemsK (cH H), it.pat = {ovl_fn_item('dist', x, ga, gb)}) ∨",
                  f"    (∃ it ∈ consItemsK (cH H), it.pat = {ovl_fn_item('dist', x, gb, ga)}) :="]
        else:
            L += [f"    ∃ it ∈ consItemsK (cH H), it.pat = {ovl_fn_item(r['kind'], x, ga)} :="]
        L += [f"  tieOvlFn{P}_item_withHooks ovlfn_text_{i} H",
              "",
              f"/-- **In a model of Γ, sentence {i}"
              + ("" if j == i else f" with sentence {j}") + " entails that item**"
              + (", in both orders" if gb else "") + ", for every H. -/",
              f"theorem ovlfn_entails_item_{i} (H : HookParams) {{M : Type}} [Inhabited M] {{I : Interpretation KoreAML.Sym M}}",
              f"    (hI : I ⊧ᴵP Γ (cH H)) {hyps} :",
              f"    {concl} := by"]
        if j != i:
            L.append(f"  rw [ovlfn_trS_{j}] at hf")
        L.append(f"  rw [ovlfn_trS_{i}] at h")
        hA = f"((tieOvlFnArityB_withHooks c H _ _).trans {arity[(x, r['gens'][r['gf']])]})"
        if r["kind"] == "fun":
            L += [f"  exact tieOvlFnFun_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_{i}) {numbered(x)}",
                  f"    {hA} h _"]
        elif r["kind"] == "inj":
            L += [f"  exact tieOvlFnInj_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_{j})",
                  f"    ((tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_{i}) {numbered(x)} {hA} hf h _"]
        else:
            L += [f"  have hfa := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_{j}",
                  "  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at hfa",
                  f"  exact tieOvlFnDist_weaker_Γ hI (gf := {gf}) ({'.inl' if r['gf'] == 0 else '.inr'} rfl) hfa.1.2",
                  f"    ((tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_{i}) {numbered(x)} {hA} hf h _ _"]
        L.append("")
    return "\n".join(L)


def ovl_fn_refuted_section():
    """`ovlFnRefuted`, which the hand section defines, is a sublist of `ovlFnApart`."""
    return "\n".join([
        "/-! ## The refuted sentences of a function-overloaded symbol -/",
        "",
        "/-- The sentences the hand section refutes for every H are sentences of `ovlFnApart`, in its order. -/",
        "theorem ovlfn_refuted_sub : ovlFnRefuted.isSublist ovlFnApart = true := by decide +kernel",
        ""])

def law_section(law_idx):
    il = ", ".join(map(str, law_idx))
    lt = ", ".join(f"U.ax{i}" for i in law_idx)
    return f"""/-! ## The law sentences ({il}): owed as `FnLaws` -/

/-- The text's law sentences of functions, in the order of the reader's laws (`Definition.laws`). -/
noncomputable def lawText : List AxiomDecl := [{lt}]

theorem law_indices : lawText.map (·.index) = lawIdx := by decide +kernel

/-- **Each law sentence is, as written, the sentence of the reader's law** (`lawPattern`), in
`Definition.laws`' order: what `consistent_with_laws` states in a model of Γ with the step's
closure, where the interpretation satisfies the laws at values (`FnLaws`). -/
theorem law_text : lawText.map (trS · |>.pat) = defn.laws.map (lawPattern c) := by decide +kernel

/-- **No law sentence is a function equation's item or a constructor item of Γ** (`fnItems`,
`consItemsK`). -/
theorem law_not_item : lawText.all (fun ad => !(fnItems c).any (·.pat == (trS ad).pat) &&
    !(consItemsK c).any (·.pat == (trS ad).pat)) = true := by decide +kernel

/-- The law sentences are the account's class `{LAW_FN_CLASS}`, of the direction `hypothesis` (Γ does
not hold the sentence; it is owed as `FnLaws`). -/
theorem law_account : lawText.map (·.index) = classOf "{LAW_FN_CLASS}" := by
  decide +kernel
"""


def param_functional_section(param_fun, total_names, n, chunk):
    il = ", ".join(map(str, param_fun))
    lt = ", ".join(f"U.ax{i}" for i in param_fun)
    tn = ", ".join(f'"{x}"' for x in total_names)
    pred = f'(fun ad => !functionalOfNamed [{tn}] ad.ax || (classOf "{PARAM_FUNCTIONAL_CLASS}").contains ad.index)'
    if chunk:
        thms, body = by_ranges("paramFunE", "U.all", "paramFunP", ranges(n, 0, chunk), "tieAll", True)
        heads = (f"""/-- The sentence is no parameter's functional sentence, or it is of the class
`{PARAM_FUNCTIONAL_CLASS}`. -/
noncomputable def paramFunP (ad : AxiomDecl) : Bool :=
  !functionalOfNamed [{tn}] ad.ax || (classOf "{PARAM_FUNCTIONAL_CLASS}").contains ad.index

{thms}

""", "  rw [userAxioms_eq]; exact\n    " + body.replace("\n    ", "\n      "))
    else:
        heads = ("", "  rw [userAxioms_eq]; decide +kernel")
    return f"""/-! ## The parameter functional sentences ({il}): owed as `ParamsTotal` -/

/-- The parameter symbols no registry hook interprets that the text declares total
(`Definition.totalParams`): the statements take `ParamsTotal c defn.totalParams H`, that `H` gives
each a value of its result sort at every argument list of its argument sorts. -/
theorem total_params : defn.totalParams.map c.symName = [{tn}] := by decide +kernel

/-- The text's `functional` sentences of those parameters (`isParamFunctional`). -/
noncomputable def paramFunctionalText : List AxiomDecl := [{lt}]

/-- The parameter functional sentences are the account's class `{PARAM_FUNCTIONAL_CLASS}`, of the
direction `hypothesis`: Γ states a parameter's graph at values from the interpretation (`ΓDomains`),
so it holds the sentence at values exactly where `H` gives the parameter a value at the values of its
argument sorts, which is `ParamsTotal` at that parameter. -/
theorem paramfunctional_account : paramFunctionalText.map (·.index) = classOf "{PARAM_FUNCTIONAL_CLASS}" ∧
    paramFunctionalText.all (fun ad => functionalOfNamed [{tn}] ad.ax) = true := by
  decide +kernel

{heads[0]}/-- Every `functional` sentence of the user module of a parameter the text declares total
(`total_params`) is of the class `{PARAM_FUNCTIONAL_CLASS}`. -/
theorem paramfunctional_heads : userAxioms.all {pred} = true := by
{heads[1]}
"""


def param_lemma_section(param_lem, reads_h=()):
    il = ", ".join(map(str, param_lem))
    lt = ", ".join(f"U.ax{i}" for i in param_lem)
    rl = ", ".join(map(str, reads_h))
    if reads_h:
        doc = ("""The text's lemmas whose truth at values reads a value the interpretation gives: those that apply
a parameter symbol no registry hook interprets (`isParamLemma`, or a `simplification` sentence of
K's builtin library applying one), and those `--reads-h` names (""" + rl + """), which apply a symbol
through which evaluation may read the interpretation (`paramlemma_reads_h`).""")
        rh = f"""
/-- The lemmas `--reads-h` names ({rl}) apply, at a head Γ has, a symbol through which evaluation may
read the interpretation (`appliesHRead`): the necessary condition of their class. -/
theorem paramlemma_reads_h : [{", ".join(f"U.ax{i}" for i in reads_h)}].all (fun ad => appliesHRead c ad.ax.pattern) = true := by
  decide +kernel
"""
    else:
        doc = """The text's lemmas that apply a parameter symbol no registry hook interprets (`isParamLemma`, or a
`simplification` sentence of K's builtin library applying one)."""
        rh = ""
    return f"""/-! ## The parameter lemmas ({il}): owed as a hypothesis on H -/

/-- {doc} -/
noncomputable def paramLemmaText : List AxiomDecl := [{lt}]

/-- The parameter lemmas are the account's class `{PARAM_LEMMA_CLASS}`, of the direction `hypothesis`
(Γ does not hold the sentence; at the member `cH H` it is owed at values). -/
theorem paramlemma_account : paramLemmaText.map (·.index) = classOf "{PARAM_LEMMA_CLASS}" := by
  decide +kernel

/-- **What the tie owes of the parameter lemmas**: one interpretation `H` at which `FnHyp` holds
and every parameter lemma holds in every model of Γ at the valuations sending its
free element variables to values (`EntailsAtValues`), so that the text with its hypotheses has a
model. Γ states a parameter's graph at values only (`ΓDomains`), so the lemma is owed there. Stated,
not proved here: the proof is owed. -/
def ParamLemmaWitnessAtValues : Prop :=
  ∃ H : HookParams, FnHyp (cH H) ∧
    ∀ ad ∈ paramLemmaText, EntailsAtValues (cH H) ad (trS ad).pat

/-- Every sentence of the user module that carries `simplification`, is an equation
(`AttrsAgree.eqnHead`) and has at the head of its left side a parameter symbol no registry hook
interprets (`impl = none`) is of the class `{PARAM_LEMMA_CLASS}`: the sentences `attrsAgree` does not
count as equations of such a parameter are held by the account as hypotheses on `H`. -/
theorem paramlemma_heads : userAxioms.all (fun ad =>
    !(AttrsAgree.has ad.ax.attributes "simplification" &&
      (AttrsAgree.eqnHead ad.ax.pattern).any (fun n =>
        c.params.any fun k => k.impl.isNone && c.symName k.sig.name == n)) ||
    (classOf "{PARAM_LEMMA_CLASS}").contains ad.index) = true := by
  rw [userAxioms_eq]; decide +kernel
{rh}"""


def user_lemma_section(user_lem, user_lem_v):
    il = ", ".join(map(str, user_lem + user_lem_v))
    lt = ", ".join(f"U.ax{i}" for i in user_lem)
    lv = ", ".join(f"U.ax{i}" for i in user_lem_v)
    return f"""/-! ## The user lemmas ({il}): owed, by hand -/

/-- The lemmas of a user's file that the reader leaves out of Γ and that apply no parameter symbol
without `impl`, of the class `{USER_LEMMA_CLASS}`. -/
noncomputable def userLemmaText : List AxiomDecl := [{lt}]

/-- Those of the class `{USER_LEMMA_VALUES_CLASS}`. -/
noncomputable def userLemmaValuesText : List AxiomDecl := [{lv}]

/-- The two lists are the account's classes `{USER_LEMMA_CLASS}`, of the direction `entailed`, and
`{USER_LEMMA_VALUES_CLASS}`, of the direction `atValues`. -/
theorem userlemma_account : userLemmaText.map (·.index) = classOf "{USER_LEMMA_CLASS}" ∧
    userLemmaValuesText.map (·.index) = classOf "{USER_LEMMA_VALUES_CLASS}" := by
  decide +kernel

/-- **What the tie owes of the user lemmas of the class `{USER_LEMMA_CLASS}`**: Γ entails each, for
every interpretation `H`. Stated, not proved here: the proof is owed. -/
def UserLemmaEntailed : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaText, Γ (cH H) ⊧ (trS ad).pat

/-- **What the tie owes of the user lemmas of the class `{USER_LEMMA_VALUES_CLASS}`**: each holds in
every model of Γ at the valuations sending its free element variables to values, for every
interpretation `H`. Stated, not proved here: the proof is owed. -/
def UserLemmaAtValues : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaValuesText, EntailsAtValues (cH H) ad (trS ad).pat
"""


def openlaw_section(open_law, rnames, need_rfl):
    i = open_law[0]
    rfl = ("kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c\n\n"
           if need_rfl else "")
    return f"""/-! ## The law sentence of {rnames} ({i}): an item of Γ -/

{rfl}/-- **Γ's one law item is the translation of sentence {i}, as written** (`lawItemsK`, a part of
the constructors' items). -/
theorem openlaw_item : (lawItemsK c).map (·.pat) = [(trS U.ax{i}).pat] := by decide +kernel
theorem openlaw_cons : (consItemsK c).any (·.pat == (trS U.ax{i}).pat) = true := by decide +kernel

/-- **E for the law sentence**: Γ entails it, for every H. -/
theorem openlaw_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by
  intro M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp openlaw_cons
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- The law sentence is the account's class `{LAW_OPEN_CLASS}` (direction `equal`: Γ's law item is
its translation, `openlaw_item`, and Γ entails it, `openlaw_entailed`). -/
theorem openlaw_account : classOf "{LAW_OPEN_CLASS}" = [{i}] := by decide +kernel
"""


def open_functional_section(open_fun, rnames):
    if len(open_fun) == 1:
        i = open_fun[0]
        return f"""/-! ## The functional sentence of {rnames} ({i}): owed as `OpenTotal` -/

/-- **Γ holds no item for {rnames}'s functional sentence**: the constructors' items state the
functionality of the generators that are no open generator only. The sentence is owed, at values,
as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : !(consItemsK c).any (·.pat == (trS U.ax{i}).pat) &&
    !(fnItems c).any (·.pat == (trS U.ax{i}).pat) &&
    (classOf "{OPEN_FUNCTIONAL_CLASS}" == [{i}]) = true := by
  decide +kernel
"""
    return f"""/-! ## The functional sentences of {rnames} ({', '.join(map(str, open_fun))}): owed as `OpenTotal` -/

/-- **Γ holds no item for the open generators' functional sentences**: the constructors' items
state the functionality of the generators that are no open generator only. The sentences are owed,
at values, as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : {ax_list(open_fun, 4)}.all (fun ad => !(consItemsK c).any (·.pat == (trS ad).pat) &&
    !(fnItems c).any (·.pat == (trS ad).pat)) &&
    (classOf "{OPEN_FUNCTIONAL_CLASS}" == [{', '.join(map(str, open_fun))}]) = true := by
  decide +kernel
"""


def gamma_c_section(gamma, fn_align, nrules, fn_any, nj_triv, nj_items, nj_kitem, cons_text, idem, own_idem=(),
                    ovl_eq=(), ovl_nc=(), tok_omit=(), tok_sorts=(), ovl_fn=(), ovl_fn_rows=None):
    """The statements over `Γc = Γ ∪ Γcl`, the theory of a definition that reads a confined sort: each
    entailment over Γ holds over `Γc`; `Γcl` holds `boolClosed` alone; the origin of `Γc`'s premises."""
    L = ["/-! ## Over `Γc`, the theory the statements are about -/", "",
         "/-- `Γc` holds every premise of Γ. -/",
         "theorem Γ_sub_Γc (c : Semantics) {φ : P} (h : Γ c φ) : Γc c φ := Or.inl h", "",
         "/-- What Γ entails, `Γc` entails. -/",
         "theorem entails_c {c : Semantics} {ψ : P} (h : Γ c ⊧ ψ) : Γc c ⊧ ψ :=",
         "  fun hI => h fun φ hφ => hI φ (Γ_sub_Γc c hφ)", "",
         "/-- Bool holds only its literals here, and the definition reads a confined sort: `Γcl` holds its",
         "one item, `boolClosed`. -/",
         "theorem gammaCl_eq (H : HookParams) (φ : P) : Γcl (cH H) φ ↔ φ = boolClosed (cH H) :=",
         "  ⟨fun h => h.2.2, fun h => ⟨readsConfined_c, (by decide +kernel : c.litSort Srt.bool = true), h⟩⟩", ""]
    names = ["gammaCl_eq"]
    if gamma:
        if fn_align:
            fnd = "(∃ ad ∈ fnText, ∃ env, alphaB env (trS ad).pat φ = true)"
        else:
            fnd = "(∃ ad ∈ fnText, (trS ad).pat = φ)"
        if nrules:
            body = (f"    ({fnd} ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ φ) ∨\n"
                    "      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x)) ∨ φ = boolClosed (cH H) := by")
        else:
            body = (f"    ({fnd} ∨ Families H φ ∨\n"
                    "      (∃ x : EVar, φ = @definedness KoreAML.Sym _ x)) ∨ φ = boolClosed (cH H) := by")
        L += ["/-- **The origin of each premise of `Γc`**: one of Γ's (`gamma_origin`), or `boolClosed`, the item",
              "of `Γcl`: every element of Bool is `true` or `false`, a family of the reading of a definition that",
              "reads a confined sort, which no sentence of the text states. -/",
              "theorem gamma_origin_c (H : HookParams) : ∀ φ, Γc (cH H) φ →", body,
              "  intro φ h", "  rcases h with h | h", "  · exact Or.inl (gamma_origin H φ h)",
              "  · exact Or.inr ((gammaCl_eq H φ).mp h)", "",
              "/-- Every premise of `Γc` is a consequence of `Pre` with `Γcl`. -/",
              "theorem gamma_from_c (H : HookParams) : ∀ φ, Γc (cH H) φ → (Pre H ∪ Γcl (cH H)) ⊧ φ := by",
              "  intro φ h M _ I hI", "  rcases h with h | h",
              "  · exact gamma_from H φ h (fun ψ hψ => hI ψ (Or.inl hψ))", "  · exact hI _ (Or.inr h)", ""]
        names += ["gamma_origin_c", "gamma_from_c"]
    L += ["theorem decls_entailed_c (H : HookParams) : ∀ it ∈ declItems, Γc (cH H) ⊧ it.pat :=",
          "  fun it hit => entails_c (decls_entailed H it hit)"]
    names.append("decls_entailed_c")
    if fn_any:
        L += ["theorem fns_entailed_c (H : HookParams) : ∀ ad ∈ fnText, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (fns_entailed H ad had)"]
        names.append("fns_entailed_c")
    if nj_triv:
        L += ["theorem nojunk_trivial_entailed_c (H : HookParams) :",
              f"    ∀ ad ∈ {ax_list([i for i, _ in nj_triv], 6)}, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (nojunk_trivial_entailed H ad had)"]
        names.append("nojunk_trivial_entailed_c")
    if nj_items:
        L += [f"theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ {ax_list(nj_items, 6)},",
              "    Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (nojunk_items_entailed H ad had)"]
        names.append("nojunk_items_entailed_c")
    for i in nj_kitem:
        L += [f"theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax{i}).pat :=",
              "  entails_c (nojunk_kitem_entailed H)"]
        names.append("nojunk_kitem_entailed_c")
    if cons_text:
        L += ["theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (cons_entailed H ad had)"]
        names.append("cons_entailed_c")
    if idem is not None:
        L += [f"/-- **Sentence {idem} is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/",
              "theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax{idem}).pat) :=",
              "  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)"]
        names.append("idem_refuted_c")
    for i, _, _ in own_idem:
        L += [f"/-- **Sentence {i} is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/",
              f"theorem own_idem_refuted_{i}_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax{i}).pat) :=",
              f"  fun M hM I hI => own_idem_refuted_{i} H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)"]
        names.append(f"own_idem_refuted_{i}_c")
    if ovl_eq:
        L += ["theorem ovleq_entailed_c (H : HookParams) : ∀ ad ∈ ovlEqText, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (ovleq_entailed H ad had)"]
        names.append("ovleq_entailed_c")
    if ovl_nc:
        L += ["/-- **The sentences of `ovlRefuted` are refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/",
              "theorem ovlnc_refuted_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}",
              "    (hI : I ⊧ᴵP Γc (cH H)) : ∀ ad ∈ ovlNcText, ¬ (I ⊧ᴵ (trS ad).pat) :=",
              "  @ovlnc_refuted H M _ I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)"]
        names.append("ovlnc_refuted_c")
    if tok_omit:
        i = tok_omit[0]
        L += [f"/-- **Over `Γc`, sentence {i} holds exactly where no sort of `tokKItemSorts` has an element**, for",
              "every H: a model of `Γc` is one of Γ. -/",
              "theorem tokkitem_holds_iff_empty_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}",
              f"    (hI : I ⊧ᴵP Γc (cH H)) : (I ⊧ᴵ (trS U.ax{i}).pat) ↔ ∀ x ∈ tokKItemSorts, ¬ ∃ y, InS I (c.sortName x) y :=",
              "  tokkitem_holds_iff_empty H fun φ hφ => hI φ (Γ_sub_Γc _ hφ)"]
        names.append("tokkitem_holds_iff_empty_c")
    if ovl_fn:
        gname = {}
        for r in ovl_fn_rows.values():
            for g in r["gens"]:
                gname.setdefault(g, f"ovlFnGen{len(gname)}")
        for i in ovl_fn:
            r = ovl_fn_rows[i]
            hyps, concl = ovl_fn_entails(i, r, gname)
            args = " hf h" if r["jf"] != i else " h"
            L += [f"/-- **Over `Γc`, sentence {i}" + ("" if r["jf"] == i else f" with sentence {r['jf']}") +
                  " entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/",
                  f"theorem ovlfn_entails_item_{i}_c (H : HookParams) {{M : Type}} [Inhabited M] {{I : Interpretation KoreAML.Sym M}}",
                  f"    (hI : I ⊧ᴵP Γc (cH H)) {hyps} :",
                  f"    {concl} :=",
                  f"  ovlfn_entails_item_{i} H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)){args}"]
            names.append(f"ovlfn_entails_item_{i}_c")
    return "\n".join(L) + "\n", names


OWN_IDEM_RE = re.compile(r"axiom ?\{R\} ?\\equals\{Sort([\w']+)\{\}, ?R\} ?\(([^\s{}(),]+)\{\}\("
                         r"(\w+):Sort\1\{\}, ?\3:Sort\1\{\}\), ?\3:Sort\1\{\}\) ?\[idem\{\}\(\)\]")


def own_idem_shape(raw):
    """`(concatenation symbol, variable)` of an idempotence sentence `\\equals{S, R}(f(K, K), K)`
    with nothing but `idem` among its attributes, or None."""
    m = OWN_IDEM_RE.match(raw.strip())
    return (m.group(2), m.group(3)) if m else None


def own_idem_section(own_idem):
    """The refutation of each idempotence sentence of a set collection other than the library's
    `Set` (`Faithful.setColl_idem_refuted_text`)."""
    L = ["/-! ## Set idempotence of the definition's own set collections: refuted",
         "",
         "Each sentence is the idempotence sentence of a set collection of the definition, whose key sort",
         "has a value the search exhibits (`setIdemTextOK`, a kernel decision). At the element `x` of a",
         "one-member set `{w}` the sentence says `concat(x, x)` holds `x`; `ΓColls` (`setElemAtomAx`) then",
         "makes `x` the unit's, which `setElemNotUnitAx` denies (`Faithful.setColl_idem_refuted_text`). -/",
         ""]
    for i, f, v in own_idem:
        L += [f"theorem own_idem_ok_{i} : setIdemTextOK c \"{f}\" \"{v}\" U.ax{i} = true := by decide +kernel",
              f"theorem own_idem_trS_{i} : (trS U.ax{i}).pat = (trAxiom [] [] U.ax{i}).pat := by decide +kernel",
              "",
              f"/-- **Sentence {i} is refuted, for every H**: Γ with it has no model. -/",
              f"theorem own_idem_refuted_{i} (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax{i}).pat) := by",
              "  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)",
              "  intro M hM I hI hax",
              f"  rw [own_idem_trS_{i}] at hax",
              f"  exact setColl_idem_refuted_text c H own_idem_ok_{i} M hM I hI hax",
              ""]
    return "\n".join(L)



RULE_COMP_SECTION = """/-- A rule axiom with a negated conjunct, `\\rewrites{C}(\\and{C}(l, t, ¬ n, x), r)`, read as its parts:
the axiom of a rule that has rules of a smaller priority, `n` their `applies`. -/
def ruleCompParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, .not _ n, x]) r => some (C, l, t, n, x, r)
  | _ => none

theorem ruleCompParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t n x r : Kore.Pattern}
    (h : ruleCompParts p = some (C, l, t, n, x, r)) : ∃ C' C'', p = .rewrites C (.and C' [l, t, .not C'' n, x]) r := by
  unfold ruleCompParts at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- **Γ's item of a rule with competitors without its premises `¬ n` and `x`**: the axiom
`\\rewrites(l ∧ t ∧ ¬ n ∧ x, r)` read as `\\rewrites(l ∧ t, r)`, under the variable table and the
guards of the axiom itself (so the variables keep their indices, the variables only `n` binds
included). An axiom of another form is its own item. -/
noncomputable def minusComp (p : Kore.Pattern) : P :=
  match ruleCompParts p with
  | some (C, l, t, _, _, r) =>
    let tb := tableOf [] p
    conjList (((freeOf [] p).eraseDups).map (guardOf tb)) ⇒
      (tr ⟨tb, []⟩ (.rewrites C (.and C [l, t]) r) ≡ inhOf (trSort tb C))
  | none => (trAxiom [] [] (kAx p)).pat

/-- **Two conjuncts more on a rule's left side give a consequence**: in a model of definedness, the
item without the premises `¬ n` and `x` entails the rule's item. -/
theorem item_of_minusComp {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    {p : Kore.Pattern} (h : I ⊧ᴵ minusComp p) : I ⊧ᴵ (trAxiom [] [] (kAx p)).pat := by
  unfold minusComp at h
  cases hq : ruleCompParts p with
  | none => rw [hq] at h; exact h
  | some q =>
    obtain ⟨C, l, t, n, x, r⟩ := q
    rw [hq] at h
    dsimp only at h
    obtain ⟨C', C'', hp⟩ := ruleCompParts_eq hq
    intro e m
    have h1 := h e m
    simp only [trAxiom, kAx, List.map_nil, List.nil_append]
    rw [hp] at h1 ⊢
    rw [interpret_impl] at h1 ⊢
    intro hg
    have h2 := h1 hg
    rw [interp_equal hD] at h2 ⊢
    intro a
    have h3 := h2 a
    simp only [sortOf, tr, trAndList, sRewrites, interp_sImp, interp_sAnd] at h3 ⊢
    exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 ⟨hl.1, hl.2.1⟩⟩⟩
"""


def ens_section(start, end, drop=()):
    """The text of test/TieEns.lean from the line `start` up to the line `end`, each text of `drop`
    taken out, its sentences 61 and 166 made the placeholder @I@."""
    t = open(ENS_TIE).read()
    a = t.index("\n" + start) + 1
    b = t.index("\n" + end, a) + 1
    s = t[a:b]
    for d in drop:
        if d not in s:
            raise Refused(f"test/TieEns.lean has changed: no {d[:60]!r} in its section {start!r}")
        s = s.replace(d, "")
    return s.replace("U.ax61", "U.ax@I@").replace("U.ax166", "U.ax@I@").replace("Sentence 61", "Sentence @I@").replace(
        "sentence 166", "sentence @I@").replace("Sentence 166", "Sentence @I@")


IDEM_DROP = ("""set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- No rule or clause has an open variable or a condition with a binder. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

""",)


GAMMA = r'''/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; the text has no rule, so Γ has no rule item; everything else is one of the five parts
defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl ⟨ad, had, he⟩))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))
'''

GAMMA_RULES = r'''/-! ## The converse over Γ's content -/

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, Γ's rule items (each a consequence of its
text sentence, `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; a rule item is a consequence of a text sentence of `ruleText`; everything else is one of
the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ φ) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))
'''

GAMMA_ALIGN = r'''/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence up to a renaming of element variables; the text has no rule, so Γ has no rule item;
everything else is one of the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, ∃ env, alphaB env (trS ad).pat φ = true) ∨ Families H φ ∨
      (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      exact Or.inl (align_item fn_align hit)
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, _, hα⟩ | hf | hx
  · exact satisfies_of_alphaB hα (hI _ (Or.inl (Or.inl ⟨ad, had, rfl⟩)))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))
'''


def law_refuted(name, head, laws, raws, sents):
    """The refusal of a text with a law the probe refutes at values (the module's docstring,
    Function laws), or None. `laws`: the probe's `lawIx`, in `Definition.laws`' order."""
    for r in head["lawRef"]:
        if r["wit"]:
            i, w = laws[r["j"]][0], r["wit"]
            return (f"{name}: the law axiom {i} ({law_what([i], raws, sents)}) is false at values under every "
                    f"interpretation: at {w['sigma']} its left side's value is {w['lhs']} and its right side's "
                    f"{w['rhs']} (`Cert.evalTC`, which consults no interpretation); `FnLaws` fails at every H, so the "
                    "text is not tied and a fixture of it is a test of the check (DONE-0 C8; "
                    "test/constructs/rows-header.toml, owed-sentence rule items 3 and 4)")
    return None


# the law search's expected outcome on fixtures: the refusal's witness, or None where no law is refuted
SELF_TEST = {"e2-fn-assoc-bad": "at var 0 = 0, var 1 = 0, var 2 = 1 its left side's value is -1 and its right side's 1",
             "e2-fn-assoc": None, "e2-fn-assoc-rest": None}


def index_range(order):
    """`(a, n)` where `order` is `a, a+1, ..., a+n-1` with n > 0, else None (`--account-sorted`)."""
    return (order[0], len(order)) if order and order == list(range(order[0], order[0] + len(order))) else None


# `index_range` on lists that are a range and lists that are not
INDEX_RANGE_TEST = [([7, 8, 9], (7, 3)), ([0], (0, 1)), ([], None), ([7, 9, 10], None), ([8, 7, 9], None),
                    ([7, 7, 8], None)]
# `head_code_lit` against `KoreAML.Distinct.strCode` as the kernel computes it (decided on these heads)
HEAD_CODE_TEST = [(("kseq", []), "(6197441387, [])"),
                  (("inj", ["SortA", "SortB"]), '(23752297, [.ctor ⟨⟨"SortA"⟩⟩ [], .ctor ⟨⟨"SortB"⟩⟩ []])')]


def self_test():
    bad = []
    for order, want in INDEX_RANGE_TEST:
        if index_range(order) != want:
            print(f"tiegen self-test: index_range({order}) is {index_range(order)}, not {want}  FAILS")
            bad.append(f"index_range {order}")
    for h, want in HEAD_CODE_TEST:
        if head_code_lit(h) != want:
            print(f"tiegen self-test: head_code_lit({h}) is {head_code_lit(h)}, not {want}  FAILS")
            bad.append(f"head_code_lit {h}")
    for name, want in SELF_TEST.items():
        text = restored_text(name)
        with tempfile.TemporaryDirectory(prefix="tiegen-self-") as d:
            path = os.path.join(d, f"{name}.kompile.kore")
            open(path, "w").write(text)
            account_check(name, path)
            ob = obligations(name, path)
            um0, ua = user_axioms(text)
            head, sents = probe(name, path, um0, ob["order_list"])
        laws, lr = nested(head["lawIx"]), head["lawRef"]
        got = law_refuted(name, head, laws, {i: raw for i, _, _, raw in ua}, sents) if len(lr) == len(laws) else None
        ok = len(laws) == len(lr) == 1 and lr[0]["searched"] and (got is None if want is None else want in got)
        print(f"tiegen self-test: {name}: " + (f"refused: {got}" if got else
              f"{len(lr)} laws, searched {[x['searched'] for x in lr]}, {[x['tried'] for x in lr]} valuations, no witness")
              + ("" if ok else "  FAILS"))
        if not ok:
            bad.append(name)
    print(f"tiegen self-test: {len(SELF_TEST)} fixtures, {len(INDEX_RANGE_TEST)} index lists and "
          f"{len(HEAD_CODE_TEST)} head codes, {len(bad)} failing")
    return 1 if bad else 0


def main(argv):
    if argv[:1] == ["--self-test"]:
        return self_test()
    if not argv or argv[0].startswith("-"):
        raise SystemExit(__doc__)
    name = argv[0]
    opt = lambda f, d: int(argv[argv.index(f) + 1]) if f in argv else d
    chunks = (opt("--sig-chunk-first", 34), opt("--sig-chunk", 13), opt("--decl-chunk", 25))
    chunk = opt("--chunk", 0)
    at_values = ()
    if "--at-values" in argv:
        v = argv[argv.index("--at-values") + 1] if argv.index("--at-values") + 1 < len(argv) else ""
        if not re.fullmatch(r"\d+(,\d+)*", v):
            raise Refused(f"--at-values {v!r}: a comma-separated list of sentence indices is expected")
        at_values = tuple(sorted({int(x) for x in v.split(",")}))
    reads_h = ()
    if "--reads-h" in argv:
        v = argv[argv.index("--reads-h") + 1] if argv.index("--reads-h") + 1 < len(argv) else ""
        if not re.fullmatch(r"\d+(,\d+)*", v):
            raise Refused(f"--reads-h {v!r}: a comma-separated list of sentence indices is expected")
        reads_h = tuple(sorted({int(x) for x in v.split(",")}))
    hand = {}
    for j, a in enumerate(argv):
        if a == "--hand":
            sec, _, f = argv[j + 1].partition("=")
            if sec not in HAND_SECTIONS or not os.path.isfile(f):
                raise Refused(f"--hand {argv[j + 1]}: no section {sec!r} or no file {f!r} (sections: {', '.join(HAND_SECTIONS)})")
            hand[sec] = open(f).read()
    if not os.path.isdir(os.path.join(FX, name)):
        raise Refused(f"{name}: no such fixture")
    text = restored_text(name)
    text_rel = f"f2-examples/{name}.kompile.kore"
    final = os.path.join(KS, text_rel)
    tmpd = tempfile.TemporaryDirectory(prefix="tiegen-text-")
    path = os.path.join(tmpd.name, f"{name}.kompile.kore")
    open(path, "w").write(text)
    wf_ok, failing = account_check(name, path)
    ob = obligations(name, path, "consistency" in hand)
    um0, ua = user_axioms(text)
    cons_head = "--cons-head" in argv
    wf_parts = None
    if "--wf-parts" in argv:
        nsorts = len(re.findall(r"^\s*(?:hooked-)?sort ", text, re.M))
        nsyms = len(re.findall(r"^\s*(?:(?:hooked-)?symbol|alias) ", text, re.M))
        wf_parts = (nsorts.bit_length() + 1, nsyms.bit_length() + 1)
    sig_pos = "--sig-positions" in argv
    decl_pos = "--decl-positions" in argv
    fn_readings = "--fn-readings" in argv
    head, sents = probe(name, path, um0, ob["order_list"], cons_head, sig_pos, decl_pos, reads_h, readings=fn_readings)
    # the sentences whose item is narrowed by the priority premise and is the sentence without it
    for w_ in head["fnW"].values():
        if w_["idx"] in sents and not w_["same"] and w_["narrowed"] and w_["wtext"] and w_["differs"]:
            sents[w_["idx"]]["narrowW"] = True
    if "consistency" in hand and not (ob["agree"] or ob["match"] or ob["owed"] or ob["held"] or ob["total"]
                                      or ob.get("prehyp")):
        raise Refused(f"{name}: --hand consistency is for a text that owes an agreement, a match independence, a "
                      f"condition, a held-named function's fact or a totality")
    laws, open_laws = nested(head["lawIx"]), nested(head["openLawIx"])
    if any(len(l) != 1 for l in laws) or len({l[0] for l in laws}) != len(laws):
        raise Refused(f"{name}: a law of the reader (`Definition.laws`) is not, as written, exactly one sentence of the user module")
    if any(len(l) != 1 for l in open_laws) or len(open_laws) > 1:
        raise Refused(f"{name}: Γ's law items (`lawItemsK`) are not one sentence of the user module, as written")
    if len(head["lawRef"]) != len(laws):
        raise Refused(f"{name}: the probe's law search does not list the reader's laws")
    refuted = law_refuted(name, head, laws, {i: raw for i, _, _, raw in ua}, sents)
    if refuted:
        raise Refused(refuted)
    if head.get("wf") != ("true" if wf_ok else "false"):
        raise Refused(f"{name}: the probe's wf and the account's differ")
    next_only = head.get("sigBadNext") == "true" and head.get("textNext") == "false"
    if (head.get("sigAll") != "true" and not next_only) or head.get("declAll") != "true":
        raise Refused(f"{name}: an item of the signature has no origin (items {head.get('sigBad')}) or a declaration's item is not Γ's")
    law_set, open_set = {l[0] for l in laws}, {l[0] for l in open_laws}
    names_of = lambda k: set(re.findall(r"[^\s\[\],]+", head.get(k, "")))
    um, cls, mapped, unmapped = classify(name, text, sents, law_set, open_set, {k["name"] for k in head["raw"]},
                                         at_values, names_of("totalParams"), names_of("noImplParams"), reads_h)
    for i in law_set | open_set:
        if sents[i]["fnJ"] or (i in law_set and sents[i]["consItem"]):
            raise Refused(f"{name}: law sentence {i} is a function equation's item or a constructor item of Γ")
    account_sorted = None
    if "--account-sorted" in argv:
        account_sorted = index_range([a[0] for a in ua])
        if account_sorted is None:
            raise Refused(f"{name}: --account-sorted: the indices of the user module's sentences, in text order, "
                          f"are no range a, ..., a+n-1")
    heads_literal = "--heads-literal" in argv
    if heads_literal and not chunk:
        raise Refused(f"{name}: --heads-literal decides `account_absent` by ranges: it needs --chunk N")
    if heads_literal and (not head["gHeads"] or any("?" in ss for _, ss in head["gHeads"])):
        raise Refused(f"{name}: --heads-literal: the probe gives no heads of Γ, or a head with a sort argument "
                      f"that is no sort constructor without arguments")
    heads_codes = "--heads-codes" in argv
    if heads_codes and not heads_literal:
        raise Refused(f"{name}: --heads-codes codes the literal of Γ's heads: it needs --heads-literal")
    heads_plain = "--heads-plain" in argv
    if heads_plain:
        if not chunk:
            raise Refused(f"{name}: --heads-plain decides `account_absent` by ranges: it needs --chunk N")
        if heads_literal:
            raise Refused(f"{name}: --heads-plain replaces --heads-literal and --heads-codes: give one of them")
        gs, gh = head["gSyms"], head["gHeads"]
        if any("{" in n for n in gs):
            raise Refused(f"{name}: --heads-plain: a name of Γ's symbols holds `{{` (the decoder may read it as an "
                          f"instance, which Γ applies at sort arguments): use --heads-literal")
        if (not gs or gh[:len(gs)] != [(n, []) for n in gs] or
                any(n != "inj" or len(ss) != 2 for n, ss in gh[len(gs):])):
            raise Refused(f"{name}: --heads-plain: the probe's heads of Γ are not its symbols' names at no sort "
                          f"argument followed by `inj` at the subsort pairs")
    fn_blocks = opt("--fn-blocks", 0)
    attrs_blocks = opt("--attrs-blocks", 0)
    absent_file = "--absent-file" in argv
    if absent_file and "--split" not in argv:
        raise Refused(f"{name}: --absent-file puts the absent section in a file of `--split`: it needs --split")
    builtin_decls = ()
    if "--builtin-decls" in argv:
        has = set(re.findall(r"[^\s\[\],]+", head.get("plainSymNames", "")))
        builtin_decls = [n for n in builtin_symbol_decls(text) if n in has]
        if not builtin_decls:
            raise Refused(f"{name}: --builtin-decls: the text declares no symbol of Γ with a K builtin file's "
                          f"Source, without a hook and without sort parameters")
    if sig_pos and (len(head.get("sigPos", [])) != int(head["nSig"]) or any(k == "x" for k, _ in head["sigPos"])):
        raise Refused(f"{name}: --sig-positions: the probe gives no origin for each item of the signature")
    if decl_pos and (len(head.get("declPos", [])) != int(head["nDecl"]) or None in head["declPos"]):
        raise Refused(f"{name}: --decl-positions: the probe gives no position in Γ's signature for each declaration item")
    ns, lean, summary = generate(name, text_rel, um, cls, mapped, unmapped, sents, head, wf_ok, failing,
                                 ob, chunks, {i: raw for i, _, _, raw in ua}, hand, chunk,
                                 at_values, cons_head, wf_parts, "--split" in argv, account_sorted,
                                 heads_literal, heads_codes, "--attrs-parts" in argv or attrs_blocks > 0, "--decl-parts" in argv,
                                 fn_blocks, attrs_blocks, absent_file, builtin_decls=builtin_decls,
                                 decl_syms="--decl-syms-literal" in argv, nojunk_eq="--nojunk-eq" in argv,
                                 nojunk_blocks=opt("--nojunk-blocks", 0), lists_by_class="--lists-by-class" in argv,
                                 heads_plain=heads_plain, sig_pos=sig_pos, fnfun_chunk=opt("--fnfun-chunk", 0),
                                 decl_pos=decl_pos, reads_h=reads_h, fn_readings=fn_readings)
    outdir = argv[argv.index("--out") + 1] if "--out" in argv else None
    if outdir is None and (not os.path.exists(final) or open(final).read() != text):
        open(final, "w").write(text)
    out = os.path.join(outdir or os.path.join(KS, "test"), ns + ".lean")
    files = summary.pop("split_files", None)
    if files:
        for stem, t in files.items():
            open(os.path.join(os.path.dirname(out), stem + ".lean"), "w").write(t)
        summary["files"] = [os.path.relpath(os.path.join(os.path.dirname(out), stem + ".lean"), KS) for stem in files]
    else:
        open(out, "w").write(lean)
    summary["file"] = os.path.relpath(out, KS)
    print(json.dumps(summary, indent=1) if "--print" in argv else
          f"tiegen: {summary['file']}: {summary['sentences']} sentences ({summary['mapped']} as ens's, "
          f"{summary['unmapped']} unmapped), {len(summary['uncovered'])} uncovered"
          + (f"; {len(files)} files: {', '.join(summary['files'])}" if files else ""))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Refused as e:
        print(f"tiegen: refused: {e}", file=sys.stderr)
        sys.exit(1)
