# TLAPS backend pragmas (from `library/TLAPS.tla`)

Cite a pragma in a `BY` clause to choose the backend; without one, tlapm
tries its default sequence (SMT, then Zenon, then Isabelle `auto`), which is
slow on failure. `XT(n)` forms take a wall-clock timeout in seconds.

| Pragma | Backend | Good for |
|---|---|---|
| `SMT`, `SMTT(n)` | Z3 via the SMT-LIB encoding | arithmetic over Nat/Int, `..`, `<=`, simple set/function facts, records with known fields |
| `SMTT("rN")` | Z3 with a deterministic rlimit budget (tlapm ≥ 1.6 only) | reproducible SMT runs; keep N ≤ 30 |
| `Z3`, `Z3T(n)` | Z3 native encoding | alternative when `SMT` times out |
| `Zenon`, `ZenonT(n)` | Zenon tableau prover | first-order set theory, quantifier instantiation, citing library lemmas with `ASSUME ... PROVE` shape |
| `Isa`, `IsaT(n)`, `IsaM("tactic")` | Isabelle/TLA+ | fallback; `IsaM("blast")`, `IsaM("force")`, `Auto`, `Blast`, `Force` are shorthands |
| `PTL`, `LS4` | LS4 propositional temporal logic | `[]`, `<>`, `~>` reasoning once the state-level facts are proved separately |
| `Zipper` | Zipperposition (tlapm ≥ 1.6 only) | higher-order goals |
| `OBVIOUS` | the default sequence on the goal alone | trivial goals; never as a retry strategy |
| `AllProvers`, `AllSMT`, `AllIsa` | run every backend of a family | diagnosis only; slow |
| `ExpandENABLED`, `ExpandCdot`, `AutoUSE`, `Lambdify`, `ENABLEDaxioms`, `LevelComparison` | preprocessing passes (tlapm ≥ 1.5) | `ENABLED` and `\cdot` goals; see advanced-options.md |

Rules of thumb:

- Arithmetic goes only to SMT. Zenon and Isabelle do not know `..`, `<=` on
  Nat, or `+`; give SMT the typing facts (`n \in Nat`) it needs as hypotheses.
- Instantiating a library theorem stated as `ASSUME NEW S, ... PROVE ...` works
  best with `BY Thm, Zenon` or by stating the instance as a step first.
- Temporal steps: prove every state predicate implication as its own step, then
  close with `BY <steps>, PTL`. PTL ignores the structure inside state predicates.
- Division, modulus, exponentiation, reals, CHOOSE, CASE, strings, tuples and
  records get little automation; see unsupported-features.md.
