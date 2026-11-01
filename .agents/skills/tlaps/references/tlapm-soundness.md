# tlapm soundness and completeness issues

Found in a TLAPS liveness development with tlapm 1.6.0-pre 5f5037f
(observed 2026-10-27), and re-observed with 4744c0f, the build this
tooling pins, on 2026-10-31: the reproducers of issues 1, 2 and 5 below
are the test fixtures of `tlaps-audit`, and behave the same. Each
reproducer is self-contained; run it with `tlaps-check --nofp`, which
shows which backend closed each obligation.

All of it is reported upstream and open as of 2026-10-31:

- issues 1 and 2: [tlapm#309](https://github.com/tlaplus/tlapm/issues/309),
  which also names the citation pattern of issue 2;
- issue 3: [tlapm#197](https://github.com/tlaplus/tlapm/issues/197), the
  incompleteness side of #309 and #310;
- the fingerprint observation of §4:
  [tlapm#120](https://github.com/tlaplus/tlapm/issues/120);
- §5: [tlapm#310](https://github.com/tlaplus/tlapm/issues/310).

[tlaplus/Examples#250](https://github.com/tlaplus/Examples/pull/250)
concerns a different bug, tlapm#69 (instantiation pushed into `WF` and
`SF`), which matters only to proofs with `WF`, `SF` or `ENABLED`.

## 1. Unsound: temporal formulas under a binder are abstracted without the bound variable

Zenon, SMT and Isabelle do not reason about temporal operators; tlapm
replaces each temporal subformula by an opaque constant before sending the
obligation. When the subformula is under a binder (`\A`, `\E`), the
constant does not depend on the bound variable, so `[]P(n, x)` for every
`n` becomes one constant `c`, and `\E n \in S : c` implies
`\A n \in S : c`. The Isabelle output shows it: the obligation below is
sent as
`(\<exists> n \<in> {1, 2} : (hdd80b :: c)) \<Rightarrow> (\<forall> n \<in> {1, 2} : (hdd80b :: c))`.

```tla
---- MODULE TlapmTemporalBinder ----
(* Every theorem below is INVALID except the controls Z5 (rejected, as    *)
(* it should be).                                                          *)
EXTENDS Naturals, TLAPS
VARIABLE x
CONSTANT P(_, _)

(* Issue 1: a temporal formula under a quantifier. *)
THEOREM Z1 == (\E n \in {1, 2} : [](P(n, x))) => (\A n \in {1, 2} : [](P(n, x)))
  BY Zenon
THEOREM S1 == (\E n \in {1, 2} : [](P(n, x))) => (\A n \in {1, 2} : [](P(n, x)))
  BY SMT
THEOREM I1 == (\E n \in {1, 2} : [](P(n, x))) => (\A n \in {1, 2} : [](P(n, x)))
  BY Isa
THEOREM D1 == (\E n \in {1, 2} : [](P(n, x))) => (\A n \in {1, 2} : [](P(n, x)))
  OBVIOUS
THEOREM P1 == (\E n \in {1, 2} : [](P(n, x))) => (\A n \in {1, 2} : [](P(n, x)))
  BY PTL

(* Issue 2: a cited fact with a NEW parameter and a temporal conclusion. *)
THEOREM Fact == ASSUME NEW a \in Nat PROVE a = 0 => [](P(a, x) => []P(a, x))
PROOF OMITTED
THEOREM Z4 == ASSUME NEW a \in Nat PROVE [](P(a, x) => []P(a, x))
  BY Fact, Zenon
THEOREM S4 == ASSUME NEW a \in Nat PROVE [](P(a, x) => []P(a, x))
  BY Fact, SMT

(* Control: issue 1 with the temporal formula behind a folded operator. *)
Bx(n) == [](P(n, x))
THEOREM Z5 == (\E n \in {1, 2} : Bx(n)) => (\A n \in {1, 2} : Bx(n))
  BY Zenon
====
```

| Theorem | Backend | Result |
|---|---|---|
| `Z1` | Zenon | proved (invalid) |
| `S1` | SMT | proved (invalid) |
| `I1` | Isabelle | proved (invalid) |
| `D1` | default (closed by SMT) | proved (invalid) |
| `P1` | PTL | failed (correct) |
| `Z4` | Zenon | proved (invalid) |
| `S4` | SMT | proved (invalid) |
| `Z5` | Zenon | failed (correct) |

Also observed with 5f5037f: the same with `<>` and `~>` instead of `[]`,
with an arbitrary set `S` instead of `{1, 2}`, through `LET` (and so
through proof-local `DEFINE`, which is unfolded by default), and with the
binder inside the temporal formula (`[](\A n \in {m} : P(n, x))` under
`\E m`). Not reproduced: the analogous `CHOOSE n \in {1, 2} : []P(n, x)`
and `{n \in {1, 2} : []P(n, x)}` statements, which no backend proved.
Folding the temporal formula into a module-level operator of the bound
variable (`Bx(n)` above, or an operator of an `INSTANCE`) avoids the
problem in every form tried, and PTL rejected every invalid formula tried.

## 2. Unsound: citing a fact whose temporal conclusion is under its own `NEW` parameters

Same root cause as issue 1. A cited `ASSUME NEW a ... PROVE ... []F(a)`
fact is a hypothesis with a binder over a temporal formula. The temporal
part becomes a constant keyed by its printed text, so when the citing
step's goal prints the same (same constant names), it matches whatever the
instantiation of the non-temporal part is: `Z4` above instantiates `a = 0`
at an arbitrary `a`. In the development where it was found, it let SMT
prove, from a lemma concluding `Hyp /\ R(n) => [](...)`, the statement
`Hyp /\ R(0) => [](...)` for every `n`: a one-line "proof" of a whole
induction from its trivial base case. Two such steps went unnoticed until
an independent review, which is why `tlaps-audit` exists.

The converse is an incompleteness: a citation at differently named
constants never proves, since the constants differ. So no correct non-PTL
proof can use such a fact at all, and every proof that does is suspect.

By inspection (not rerun), the EWD840 liveness proof in the TLA+ Examples
repository (`specifications/ewd840/EWD840_proof.tla`, lemmas
`Round1`/`Round2`, step `<1>2 <2>1`) moves `\A n \in Nat` inside `[]` by
citing `\A n \in Nat : TSpec => [](P(n) => <>Q)` with the definitions
unfolded. The statement is valid in TLA, but no sound backend proves it,
so it goes through issue 1.

## 3. Incomplete: PTL compares formulas with their bound-variable names

LS4 treats a quantified formula as a propositional atom, and two formulas
that differ only in the name of a bound variable get different atoms.

```tla
---- MODULE TlapmPtlAlpha ----
EXTENDS TLAPS
VARIABLE x
CONSTANT P(_, _), S

THEOREM A0 == [](\A v \in S : P(v, x)) => [](\A v \in S : P(v, x))
  BY PTL                                          \* proved
THEOREM A1 == [](\A u \in S : P(u, x)) => [](\A v \in S : P(v, x))
  BY PTL                                          \* fails (valid)
====
```

In practice this bites when an instantiated module's operator has bound
variable `v` and the citing proof has a constant `v` in scope: tlapm
renames the binder to `v_1` and the atoms no longer match.

## 4. Observations not yet reduced to a reproducer

- **LS4 on combined steps.** A PTL step that both unfolded an instance
  lemma and chained a state-level implication failed (`ls4 false`, not a
  timeout), while the same step split in two proved, though the failing
  obligation was propositionally valid. A possible cause is that an atom
  written by hand differs internally from the one produced by unfolding the
  instance's LAMBDA, though both print alike.
- **Fingerprints.** Two citations were reported proved in a run that
  reused fingerprints, and failed when rechecked with `--nofp`. Their
  obligation text had changed since the run that proved them (a bound
  variable was renamed). Likely explanation, from tlapm#120: fingerprints
  are computed up to the names of bound variables, but abstraction names
  are not (§5). The earlier run proved the step through issue 2 (matching
  names). So a fingerprint does not carry a result to a different
  obligation, only to an alpha-variant, but it can carry an unsound
  result. Check final results with `--nofp`, as `tlaps-report` does.

## 5. Unsound: abstraction names are a short hash of a print that ignores bound-variable renaming (tlapm#310)

tlapm names each abstracted term, and each LS4 atom, `h` + the first five
hex digits of the MD5 of the term's print (`Coalesce.crypthash`).

- **Collisions.** Twenty bits, and no check. Two different terms of one
  obligation that get the same name are one symbol to the backend, PTL
  included: `R63 => R699 BY PTL` proves for `R63 == y = 3`,
  `R699 == y = 4`.
- **Capture.** The print shows a bound variable `k` as `k` even where
  tlapm's display renames it `k_1` to avoid a clash with a free `k`.
  With `P(z) == \E k \in D : w = <<k, z>>` and
  `Q == \E k \in D : w = <<k, k>>`,
  `ASSUME NEW k \in D PROVE []Q => [](P(k))` proves.

The reproducer is the module `NameUnsound` of tlapm#310. Besides temporal
formulas, the abstracted terms include PTL atoms and primed operator
applications in action-level obligations sent to SMT. `tlapm --verbose`
prints the obligation the front-end returns, with the names
(`PROVE ?h0823c => ?h0823c`), but not the term each name stands for.

## The discipline against issues 1, 2 and 5

- A temporal formula under a binder is always a module-level operator of
  the bound variable, kept folded in every obligation not closed by PTL.
  Proof-local `DEFINE`s are unfolded by default, so they do not count.
- A theorem or step with `NEW` parameters and a temporal conclusion has
  that conclusion wrapped in an operator if it is ever cited outside PTL,
  even at the theorem's own parameter names: that is exactly the unsound
  case.
- `tlaps-audit` reads the output of
  `tlapm --toolbox 0 0 --printallobs --nofp --verbose`, which
  `tlaps-report` makes. It checks the obligations as the front-end
  receives them, with definitions expanded (the `--printallobs` text
  leaves them folded), for:
  - issues 1 and 2, in obligations not closed by PTL;
  - capture (issue 5), in every obligation with an abstracted term: a
    binder renamed `b_N` whose scope also contains a free `b`.
  It lists any other non-PTL obligation that contains a temporal operator
  for review by hand. It also prints Σ n(n−1)/2²¹ over the proved
  obligations, n being the number of distinct abstraction names in one
  obligation: an estimate, not a bound, of the chance that some
  obligation had a collision, on the assumption that the names are random
  and that each distinct term has its own name.
- A collision cannot be ruled out from tlapm's output: when two terms
  collide, the obligation shows one name, so the audit sees nothing
  (`NameUnsound`'s `HashSMT` is only on the hand-review list, with an
  estimate of 0, and `HashPTL` appears nowhere). Ruling it out would mean
  rerunning with a tlapm built to use the full digest.
