#!/usr/bin/env bash
# The example definitions as generated packages: regenerate each with `kcore gen`, build it, then the
# user's modules over it. Peano is generated with `--tie` and built with its tie (by blocks): the one
# worked example of a definition read from its KORE text whose `emit` gives the text back, proved in the
# kernel. The others are generated with `--wf` (`wf defn` decided in the kernel, no tie), but ref-kk
# with `--core` (`coreOK` decided in the kernel, no `wf`). krust's runs in
# examples/runs (findings/work/m25/rpcrun.py) become certificate modules (NAME.Certs.*). Each module in its
# own process under a 12 GiB memory scope, one thread (gen/build.sh).
# With --build-only, nothing is generated: the committed packages are built as they stand (test/regen.sh
# checks that they are what `kcore gen` writes).
# Usage: examples/run.sh [--build-only] [NAME...]  (from anywhere; kcore-spec built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
only=0; [ "${1:-}" = --build-only ] && { only=1; shift; }
want=" ${*:-peano prio kink-imp kimp imp-sec imp-sec-leaky ph kimp-ni kryp vault vault-leaky colls-list lazy fprio colls ref-peano ref-fprio ref-kimp ref-kk} "
on() { case "$want" in *" $1 "*) return 0;; esac; return 1; }
# gen KORE NAME NS OPTION...: `kcore gen` into examples/NAME (skipped with --build-only)
gen() { [ $only = 1 ] && return 0; a=$1 b=$2; shift 2; gen/gen.sh "$a" "examples/$b" "$@" || exit 1; }
step() { echo "=== $*"; "$@" || exit 1; }
if on peano; then gen examples/peano/Peano/definition.kore peano Peano --tie --cert term=examples/runs/peano-term.cert.json
  step gen/build.sh --tie examples/peano User.Statements User.Facts User.Proofs User.Cert User.Reach User.Faithful User.Faithful3 User.Model User.Course; fi
if on prio; then gen f2-examples/prio.kore prio Prio --wf --cert goD=examples/runs/prio-goD.cert.json --cert goB=examples/runs/prio-goB.cert.json; step gen/build.sh examples/prio User.Cert User.Course; fi
if on kink-imp; then gen f2-examples/imp.kore kink-imp KinkImp --wf; step gen/build.sh examples/kink-imp User.Overlaps; fi
# kimp's store secret except at the observed identifiers (`--keyed env`, Kinds/NI.lean): one
# obligation, `CALC.var`, refuted by two runs (kimp-ni's NI.Keyed); User.Reach, one rule read as a claim
if on kimp; then gen f2-examples/kimp.kore kimp Kimp --wf --keyed env; step gen/build.sh examples/kimp User.Reach User.Faithful4 User.Course; fi
if on imp-sec; then gen f2-examples/imp-sec.kore imp-sec ImpSec --wf; step gen/build.sh examples/imp-sec User.Faithful; fi
# the weakened checker (findings/work/p3/leaky-kore.sh) that kimp-ni's Leak.lean refutes
if on imp-sec-leaky; then gen f2-examples/imp-sec-leaky.kore imp-sec-leaky ImpSecLeaky --wf; step gen/build.sh examples/imp-sec-leaky; fi
if on ph; then gen f2-examples/ph.kore ph Ph --wf; step gen/build.sh examples/ph User.Overlaps; fi
if on kimp-ni; then step gen/build.sh --only --with examples/kimp --with examples/imp-sec --with examples/imp-sec-leaky \
  examples/kimp-ni NI.Names NI.Spec NI.Incl NI.Examples NI.Kind NI.Leak NI.Keyed; fi
# DOMAINS, BYTES and KEVM's plugin KRYPTO: the builtin modules' hooks and KRYPTO's are parameters
if on kryp; then gen examples/kryp/Kryp/definition.kore kryp Kryp --wf; step gen/build.sh examples/kryp; fi
# noninterference for a secret cell (`--high sec`, Kinds/NI.lean): vault's decided by the condition,
# vault-leaky's one obligation refuted by two runs (User.Leak)
if on vault; then gen f2-examples/vault.kore vault Vault --wf --high sec; step gen/build.sh examples/vault; fi
if on vault-leaky; then gen f2-examples/vault-leaky.kore vault-leaky VaultLeaky --wf --high sec; step gen/build.sh examples/vault-leaky User.Leak; fi
# list patterns (`ListItem(X) L`, `L ListItem(_)`): a core outside `ok`, well formed from `okAll`
if on colls-list; then gen f2-examples/colls-list.kore colls-list CollsList --wf; step gen/build.sh examples/colls-list User.Faithful User.Course; fi
# strict evaluation: an `#if` guarding a partial division and an `andBool` guarding a partial
# predicate, the package's two lazy obligations; the kernel's runs (User.Strict)
if on lazy; then gen f2-examples/lazy.kore lazy Lazy --wf; step gen/build.sh examples/lazy User.Strict; fi
# function priorities: `priority(n)` clauses at 40, 50 and 100, an `[owise]` with a `requires`, one
# over a pattern beside a clause of priority 30, and two agreeing clauses of one priority (User.Values)
if on fprio; then gen f2-examples/fprio.kore fprio Fprio --wf; step gen/build.sh examples/fprio User.Values; fi
# a cell map (`<acct multiplicity="*" type="Map">` in `<accts>`) and list patterns; without the tie,
# which needs `emit` to write a cell collection's own sentences (its sort's and symbols' attributes,
# its laws, and the cell-into-collection subsort and no-junk axioms, which are not read); a
# `PatVal` of the map pattern and one step (User.Course)
if on colls; then gen f2-examples/colls.kore colls Colls --wf
  step gen/build.sh examples/colls User.Course; fi
# read from K 7.1.337 kompile's own KORE, not krust's (findings/RD-2-kompile-kore.md): without the tie,
# which needs emit to print kompile's text; `--wf` gives `wf defn` and soundness and completeness
if on ref-peano; then gen f2-examples/ref-peano.kore ref-peano RefPeano --wf
  step gen/build.sh examples/ref-peano; fi
# `ag`'s agreement, its one named obligation, discharged (User.Agree)
if on ref-fprio; then gen f2-examples/fprio.kompile.kore ref-fprio RefFprio --wf
  step gen/build.sh examples/ref-fprio User.Agree; fi
# K's claim `sum-spec` (imp-semantics, examples/specs/imp-sum-spec.k) proved on the package: the
# loop's run by induction, all-path through determinism, entailed by Γ through soundness (User.SumSpec);
# `sum-N` (imp-simple-spec.k), the whole program from the empty store (User.SumN); each step `fire i`
if on ref-kimp; then gen f2-examples/ref-kimp.kore ref-kimp RefKimp --wf
  step gen/build.sh examples/ref-kimp User.SumSpec User.SumN User.SumSpecStmt User.RunInstance; fi
# kore.k (krs/semantics/kore), read from K 7.1.337 kompile's KORE of it (test/kk-kompile.toml records
# the command), with `--core`: `coreOK_defn`, its conjuncts each decided on its own and those that
# read names on the names' codes, and from it `sound_hyp` and `complete_hyp`. With `--wf` one module
# decides every conjunct of `faithOK` on the names themselves, and for this text the kernel needs
# more than the 12 GiB scope there (namesNumbered about 10 GiB alone, itesApart beyond 12 GiB alone);
# its functions coherent at HookParams.none (User.Coherent: `KK.coherent`); one clause of its `eval`
# inverted (User.EvalInversion: `KK.eval_app_inv`); FnDet at HookParams.none (User.FnSolves:
# `KK.fnDet`); PrioDecided with `leq`'s Bool results (User.PrioDecided: `KK.prioDecided`,
# `KK.leq_result`)
if on ref-kk; then gen examples/ref-kk/RefKk/definition.kore ref-kk RefKk --core
  step gen/build.sh examples/ref-kk User.Coherent User.EvalInversion User.FnSolves User.PrioDecided; fi
echo "all built"
