---
name: tlaps
description: Write and check TLA+ proofs with TLAPS (tlapm) through this tooling — tlaps-check for a compact per-obligation report, decomposing failing obligations, choosing backends, the PTL findings, the tlapm soundness bugs and the discipline and audit against them (tlaps-audit), and reporting a result as tlaps-report prints it, with each theorem statement reviewed. Use whenever editing a .tla file with THEOREM or PROOF, diagnosing a tlapm failure, or claiming that something is proved.
---

# TLA+ proofs with TLAPS

The specifications are in the descriptor's `tla_rel` (read
`tla-tooling.conf` at the checkout root); `<tla_rel>/AGENTS.md` says what
they model. The scripts are under `"$TLA_TOOLING_ROOT/scripts/"`, written
by name below. They run the tlapm that the tooling pins (a 1.6.0-pre
build; its `--version` prints a commit), never one from `PATH`. If a
script says a tool or the pinned tooling is not in the store, follow the
`tla-setup` skill; `tla-tooling smoke` proves a module that exercises every
backend (Zenon, SMT/Z3, Isabelle, LS4) and the standard proof libraries.

## Checking a module

```bash
tlaps-check [--lines A B] [--stretch F] [--nofp] [--parse] [--full] tla/Foo.tla
```

- It prints one summary line (proved, failed, interrupted, not finished;
  the module's omitted and missing proofs), then each failed obligation
  with its location, backend, reason and goal text.
- Exit 0 only when tlapm exits 0, every obligation tlapm announced for the
  range ends proved, nothing reports an error, and the module has no
  `OMITTED` or missing proof. Anything else exits 1, with the reasons on
  the last line; 2 is a usage or setup error. A module without
  obligations says so, and passes on the same terms.
- The complete tlapm output is in the run directory under
  `<tla_rel>/.tla-runs/`, whose path is printed. Grep it rather than
  rerunning.
- `--lines A B` checks only obligations located in lines A..B. Use it to
  iterate on one step. Get the range right: a `QED` or a step's last line
  left outside the range is silently not checked, and a range that selects
  no obligation fails. Before claiming a theorem is proved, run the whole
  module once without `--lines`.
- Successful obligations are fingerprinted in `.tlacache/` next to the
  module and skipped next time. `--nofp` re-proves everything; `--cleanfp`
  resets the cache. Use `--nofp` for the final run of a session: a
  fingerprint can carry an unsound result to an alpha-variant of a step
  (`references/tlapm-soundness.md` §4).
- `--parse` only parses and lists obligations; use it after large edits.
  `tla-parse FILE` runs SANY, which is stricter: it rejects, for example, a
  theorem named like an operator of an extended module (`Trivial` is
  defined in `TLAPS`).
- `--stretch F` multiplies backend timeouts. Prefer decomposition; above 3
  is a sign the step is wrong, not slow.

## Writing proofs that check

- Structure every proof hierarchically (`<1>1.`, `<2>3.`, `QED`). Read
  `references/hierarchical-proofs.md` and
  `references/other-proof-constructs.md` once; they define `SUFFICES`,
  `PICK`, `TAKE`, `WITNESS`, `CASE`, `HAVE`, `USE`, `HIDE`, `DEFINE`.
- Decompose one level at a time. After writing sub-steps, check the `QED`
  first so the decomposition is known to be sound, then prove the sub-steps
  in order, one at a time. Do not split several steps at once.
- Step labels must be unique within a level. Theorem and operator names must
  not shadow anything in scope: naming a theorem `Cardinality` silently
  breaks `Cardinality(S)` from `FiniteSets`.
- Name every lemma and prove it fully. Never leave `OMITTED` or `PROOF
  OMITTED` in work you report as done; if a gap remains, say so explicitly
  and keep it as a named lemma with `OMITTED` so that it is counted.
- Choose the backend (`references/backends.md`): `SMT` for arithmetic,
  `Zenon` for set theory and library instantiation, `Isa` as a fallback,
  `PTL` for temporal reasoning over already-proved state-level facts. Avoid
  bare `OBVIOUS` on anything non-trivial; the default backend cascade is the
  slowest way to fail. Prefer `SMTT("rN")`, N ≤ 30, for deterministic runs.
- SMT needs typing facts: cite the step or invariant giving `x \in Nat`, and
  prove a type-correctness invariant first
  (`references/type-correctness-lemma.md`).
- Expand definitions deliberately with `BY ... DEF Op`; large definitions
  drown the backends, so `HIDE DEF` what a step does not need
  (`references/hints.txt`).
- Using a theorem from an instantiated module whose assumptions mention
  extended operators needs a bridge lemma: `references/instance-bridge.md`.
- Know what TLAPS cannot do before modelling
  (`references/unsupported-features.md`): no reals, no recursive operators
  (recursive functions are fine), no `ENABLED` without the preprocessing
  pragmas, no quantification over tuples, weak `CHOOSE`, `CASE`, records,
  strings. Keep time discrete in `Nat`, state enabledness as an explicit
  existential, and prefer functions to records.
- Standard proof libraries ship with tlapm: `FiniteSetTheorems`,
  `NaturalsInduction`, `WellFoundedInduction`, `SequenceTheorems`,
  `FunctionTheorems`, `TLAPS`. Cite their theorems by name; their
  statements are in the `lib/tlapm/stdlib/` directory next to the `bin/`
  of `"$TLA_TOOLING_ROOT/bin/tla-tooling" path tlapm`.

## Temporal proofs and PTL

- Prove every state-level implication as its own step, then close the
  temporal step with `BY <steps>, PTL`. PTL ignores the structure inside
  state predicates.
- PTL atoms depend on bound-variable names (tlapm#197):
  `\A u \in S : F(u)` does not match `\A v \in S : F(v)`, and a binder
  that tlapm renames (`v_1`, after a clash with a constant `v`) breaks
  matching. Name binders as in the operator being unfolded, or hide the
  quantified formula behind an operator.
- LS4 can fail on a step that both unfolds an instance lemma and chains a
  state-level fact; split it into one step per job.
- A state-level fact is usable under `[]` by PTL only if it is proved in a
  context with no temporal hypotheses (tlapm marks the others
  `(* non-[] *)`); constant `CASE` hypotheses are fine.
- `FS_Induction` and `NatInduction` accept a temporal-level predicate when
  it is hidden and the step is closed `BY Isa`; the induction step must be
  in the `ASSUME ..., P(T), ... PROVE P(T \cup {x})` shape (for
  `FS_Induction`) or a `\A n \in Nat : P(n) => P(n+1)` fact.
- Substituting a tuple `<<a, b>>` for an instance variable leaves
  `<<a, b>>[1]` in the obligations, which then fail to match; use one
  instance variable per state variable. Rigid tuple parameters also leave
  projections unreduced in PTL atoms; state the equivalences explicitly
  before temporal reasoning. An instance's `T!IsFiniteSet` needs the
  bridge `\A S : T!IsFiniteSet(S) <=> IsFiniteSet(S)`, `BY DEF
  T!IsFiniteSet, IsFiniteSet`.
- Inside the proof of an `ASSUME ..., G(T), ... PROVE` step whose
  hypothesis `G(T)` is temporal-level, the backends do not get `G(T)`
  unless the step cites itself (`BY <1>2, <1>3` in the proof of `<1>3`).
- A leads-to from an existential over an arbitrary set, `\A v \in S :
  [](Q(v) => <>P)` giving `[]((\E v \in S : Q(v)) => <>P)`, is valid in TLA
  because `v` is rigid, but no backend proves it soundly. Over a finite
  set it follows by `FS_Induction`.

## Soundness: what tlapm can prove wrongly

tlapm hands Zenon, SMT and Isabelle an abstraction of the temporal and
other untranslated terms, and the abstraction is unsound in known ways,
all open upstream (`references/tlapm-soundness.md`, with reproducers):

- **A temporal formula under a binder** (`\A`, `\E`, `CHOOSE`, a set or
  function constructor) becomes a constant that does not depend on the
  bound variable, so `(\E n \in S : []P(n)) => (\A n \in S : []P(n))`
  proves by Zenon, SMT or Isabelle (tlapm#309). PTL rejects it.
- **A cited fact with `NEW` parameters and a temporal conclusion** is such
  a binder: at the same constant names the citation matches whatever the
  rest instantiates to (tlapm#309).
- **Abstraction names** are 20 bits of a hash of the term's print, with no
  collision check, and the print does not distinguish a bound variable
  from a constant of the same name (tlapm#310), PTL included.

The discipline:

- Never let a temporal operator appear under a binder in an obligation not
  closed by PTL: wrap such formulas in a module-level operator of the bound
  variable and keep it folded. Proof-local `DEFINE`s are unfolded by
  default, so they do not count.
- Wrap the temporal conclusion of every theorem or step with `NEW`
  parameters that is cited outside PTL, even at its own parameter names.
- Do not name a constant like a bound variable of a definition it is used
  with.
- `tlaps-audit OUTPUT` checks saved output of `tlapm --toolbox 0 0
  --printallobs --nofp --verbose` for the binder and citation patterns and
  for capture, and lists the other non-PTL obligations with temporal
  operators for review by hand; `tlaps-report` runs it. It matches the
  printed text approximately, and it cannot see a hash collision: its
  collision figure is an estimate, not a bound.

## Triage of a failed obligation

1. Read the printed goal. If a hypothesis you expected is missing, the fact
   is not in scope: cite the step, add `USE`, or expand a definition.
2. If the goal is right but the backend fails, try the appropriate backend
   explicitly, then split the step into a type fact plus the logical step.
   Zenon in particular can fail to apply a cited lemma whose conclusion is
   an existential, even at the exact instance; `BY Lemma, SMT` or
   `BY Lemma, Isa` usually closes such a step.
3. If the same step keeps failing after two decompositions, the invariant
   or lemma is likely too weak; propose the smallest strengthening rather
   than cycling tactics or raising timeouts.
4. A tlapm crash or "Could not parse" is a syntax problem; `--parse`,
   `tla-parse` and the log show the location.

## Assurance: what a result establishes

For each result you claim:

1. **Report it with `tlaps-report`.** List in `proof_modules` of
   `tla-tooling.conf` every module under `tla_rel` that the result rests
   on, the specification modules included, and run `tlaps-report`. It
   re-proves every obligation (`--nofp`), counts omitted and missing
   proofs, lists the modules under `tla_rel` they extend or instantiate
   that are not in `proof_modules`, prints every module-level `ASSUME`,
   `AXIOM` and `OMITTED`, and runs the audit. It exits 0 only if
   everything is proved, nothing is omitted, nothing it rests on under
   `tla_rel` is unchecked, and the audit flags nothing.
2. **Read each theorem statement**, not the proof you meant to write. Say
   which hypotheses it keeps (assumptions, invariants, fairness, the
   properties taken as hypotheses) and why each is acceptable for the
   claim. A hypothesis that is false, or that assumes what is to be shown,
   makes the theorem vacuous; no tool here sees that. Read each `ASSUME`
   the report prints the same way.
3. **Review the audit's hand-review list**: for each obligation, say why
   the abstracted temporal terms cannot be confused (for example, closed
   and identical in hypothesis and goal).
4. **Say what is left unchecked**, as the report prints: that the
   statements mean what is meant, the proofs of modules outside
   `tla_rel` (tlapm's library included), the soundness of tlapm and its
   backends beyond the audited patterns, and any unreviewed obligation.

Report a result as: the theorems, `tlaps-report`'s counts and the tlapm
version, every `ASSUME`, `AXIOM` or `OMITTED` it rests on, the hypotheses
each statement keeps and why, and what is left unchecked. Never report an
obligation as proved from reasoning alone; only tlapm output counts. TLC
and Apalache results are separate evidence, reported separately (the
`tla-modeling` skill).

## Files

- `references/` — TLAPS tutorial pages (hierarchical proofs, other
  constructs, tactics, practical hints, advanced options, unsupported
  features), `backends.md`, `hints.txt`, `instance-bridge.md`,
  `type-correctness-lemma.md`, and `tlapm-soundness.md`. Sources and
  licences: `ATTRIBUTION.md`.
