---
name: tla-modeling
description: Parse and model-check TLA+ specifications through this tooling — tla-parse (SANY), tlc and apalache with their run directories and verdicts, model files and their .cfg (model values, CONSTANT substitution, SYMMETRY), Apalache type annotations and bounded checks, inductive invariants with Apalache, PlusCal translation, reading traces and counterexamples, and reporting a model-checking result with its bounds as evidence, not proof. Use whenever a task parses a .tla file, writes or runs a model, or reports what TLC or Apalache found.
---

# Parsing and model checking

The specifications are in the descriptor's `tla_rel` (read
`tla-tooling.conf` at the checkout root); `<tla_rel>/AGENTS.md` says what
they model. The scripts are under `"$TLA_TOOLING_ROOT/scripts/"`, written by
name below. Each runs the tool the tooling pins, from the user's store,
never one from `PATH`; if a script says a tool or the pinned tooling is
not in the store, follow the `tla-setup` skill.

Every script writes into a new run directory under `<tla_rel>/.tla-runs/`,
temporary files included, prints its path, and ends with a verdict. Exit 0
means the tool established the result; 1 means it did not (a failure, an
incomplete or inconclusive run); 2 is a usage or setup error. Read the
verdict, not the tool's exit status: Apalache exits 0 on an SMT timeout.

## The scripts

- **`tla-parse FILE`** runs SANY with `-error-codes`. It prints a `Parsing
  file` line for each module it reads, and finds `TLAPS` and the proof
  libraries in tlapm's library, after TLC's own standard modules. A module
  that extends `Apalache` or `Variants` is checked with `apalache
  typecheck` instead.
- **`tlc MODEL [TLC options]`** runs TLC with `-config MODEL.cfg` unless
  one is given, and with its state files and trace specifications in the
  run directory. `-workers`, `-deadlock` (which turns deadlock checking
  *off*), `-simulate`, `-depth`, `-lncheck` and the other options pass
  through; `-continue` is refused, since TLC then reports violations
  without failing. `TLC_JAVA_OPTS` (default `-Xmx4g`) sets the heap. It
  prints the command and the `.cfg`, TLC's output, and ends with `no
  error`, `simulation, N traces, no error, not exhaustive` (for `-simulate
  num=N`), or `failed or incomplete` with TLC's exit code (10–14 a
  violation of an assumption, deadlock, safety, liveness or assert; 75–77
  an evaluation error; 150–153 a parse or configuration error, a state
  space too large, a system error).
- **`apalache check|typecheck [ARGS]`** runs Apalache with `--out-dir` in
  the run directory and a time limit of `APALACHE_TIMEOUT` seconds (default
  600). `check` passes only on `The outcome is: NoError`, `typecheck` only
  on `Type checker [OK]`; anything else, a timeout included, is
  inconclusive or a failure. It prints any `.apalache.json` that sets
  options outside the command line.

## Model files

The conventions of the user's repositories:

- **`<Spec>MC.tla` and `<Spec>MC.cfg` for TLC.** The model module
  `EXTENDS` the specification and `TLC`, declares model values as
  `CONSTANTS p1, p2, p3`, and defines the instances (`P_MC == {p1, p2,
  p3}`); the `.cfg` names `SPECIFICATION` (or `INIT` and `NEXT`),
  `INVARIANT`s and `PROPERTY`s, assigns model values (`p1 = p1`) and
  substitutes constants with operators (`P <- P_MC`, also for operator
  constants such as `Leader <- Leader_MC`). Bound an infinite domain by
  substituting it (`Nat <- Nat_MC`) or with an `ACTION_CONSTRAINT`, and
  say so when reporting.
- **Symmetry.** `SYMMETRY` with an operator defined as
  `Permutations(S)` of a set of model values cuts the state space. Use it
  only for values the specification treats alike (a fixed leader schedule
  distinguishes processes), and never when checking liveness: TLC can
  then miss liveness violations.
- **`<Spec>Apalache.tla` and its `.cfg` for Apalache.** Apalache needs a
  type for every variable and constant: annotate them with
  `\* @type: ...;` in the model module, and `INSTANCE` the specification
  with the constants given as typed operators, which leaves the
  specification itself unannotated. Uninterpreted types come from the
  `_OF_` suffix (`"p1_OF_PROC"`). Run `apalache typecheck` first.
  Constants may also be fixed with `--cinit=ConstInit`.

## Apalache

- Checks are bounded: `--length=N` explores executions of up to N steps,
  and a result holds for those only. `--inv`, `--init`, `--next` and
  `--config` name what to check; `--no-deadlock` turns deadlock checking
  off.
- **Inductive invariants.** A project's own script runs three checks
  through `apalache check`:
  1. initiation: `--init=Init --inv=IndInv --length=0`;
  2. consecution: `--init=IndStates --inv=IndInv --length=1
     --tuning-options=search.invariant.mode=after`, where `IndStates` is a
     predicate on the starting states, often `IndInv` itself, written so
     that Apalache can enumerate it (typed, with bounded domains);
  3. implication: `--init=IndStates --inv=Safety --length=0`.

  This proves the invariant inductive for the model's constants only if
  `IndStates` covers every state that satisfies `IndInv`: say what it
  restricts (bounded sequences, a finite epoch range) and why that loses
  nothing. Each check passes only on `NoError`.
- A failing consecution check prints a counterexample to induction: a
  state satisfying `IndStates` whose successor violates `IndInv`. It is
  often unreachable; strengthen the invariant rather than the model.

## PlusCal

Translation rewrites the source file, so it is a deliberate step, never
part of a checking script. Translate a copy, review the diff, then copy it
back:

```bash
java -cp "$("$TLA_TOOLING_ROOT/bin/tla-tooling" path tla2tools)" pcal.trans -nocfg Foo.tla
```

`-nocfg` keeps the translator from writing `Foo.cfg`. Never edit the
generated TLA+ between the `BEGIN TRANSLATION` and `END TRANSLATION`
markers.

## Reading results

- **TLC.** A violation prints the error trace in the output; the trace
  specification `*_TTrace_*.tla` in the run directory replays it. Add
  `-dumpTrace json FILE` or `-dumpTrace tla FILE` to save it in a form a
  script can read. A liveness violation is a lasso: the states after
  `Back to state` repeat forever.
- **Apalache.** A violation writes `violation.tla` and
  `violation.itf.json` (and numbered copies) under
  `<run directory>/<Spec>.tla/<timestamp>/`; for an invariant, the last
  state of the trace is the one that violates it.
- Explain a counterexample in terms of the specification: which actions
  fire, and which conjunct of the property fails. A trace through a state
  the real system cannot reach means the model is too permissive, or, for
  induction, the invariant too weak.

## Assurance: what a model-checking result establishes

- A result holds for the model's constants and bounds only (the instance
  sizes, `--length`, constraints, substituted domains), and must be
  reported with them: "TLC, no error, for 3 processes, 2 payloads, epochs
  up to 7, 1 234 567 distinct states".
- Model checking is evidence, not proof. Simulation finds bugs but proves
  nothing: report it as such, with the number of traces and their depth.
- A run that ran out of memory or time, or was interrupted, is
  "incomplete", and an Apalache timeout "inconclusive"; never report
  either as "no error".
- An inductive-invariant result from Apalache is a proof only for the
  constants and the `IndStates` of the check; say what they are.
- TLAPS results are separate, reported as the `tlaps` skill says.
