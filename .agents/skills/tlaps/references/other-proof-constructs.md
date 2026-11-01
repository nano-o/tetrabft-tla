<!-- From the TLAPS documentation, https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Other_proof_constructs.html (tlaplus/tlapm, BSD-2-Clause). Converted to Markdown 2026-10-27 with the page's own example listings inlined; written for TLAPS 1.4.x, so flag names may differ in 1.6. -->

## TLA+ proof constructs

### `SUFFICES`

An ordinary expression or `ASSUME … PROVE …` in a step stands for an assertion of that step. Its subproof proves it, and the rest of the proof in the same level is allowed to use the assertion as an assumption. `SUFFICES` reverses these two roles. Succinctly, the following two proof fragments are equivalent.

    <4>1. t1
      <5>1. s1
      <5>2. s2
      …
      <5>m. QED
    <4>2. t2
    <4>3. t3
    …
    <4>n. QED

    <4>1. SUFFICES t1
      <5>1. t2
      <5>2. t3
      …
      <5>n-1. QED
    <4>2. s1
    <4>3. s2
    …
    <4>m+1. QED

In the proof on the left-hand side above, `t`<sub>`1`</sub> is known in proof-steps `<4>2`, `<4>3`, ..., `<4>`*`n`*, while in the proof on the right-hand side, `t`<sub>`1`</sub> is known in proof-steps `<5>1`, `<5>2`, ..., `<5>`*`n-1`*.   `SUFFICES` is mainly used to rephrase the sequent to be proved in a more perspicuous form. For example, suppose we have:

    VARIABLE x
    A == /\ x = 1
         /\ x' = 2
    B == /\ x = 2
         /\ x' = 1
    Next == A \/ B
    Inv == x \in {1, 2}

    THEOREM Inv /\ Next => Inv'
    <1>1. ASSUME Inv, Next PROVE Inv'
      <2>1. ASSUME A PROVE Inv'
      <2>2. ASSUME B PROVE Inv'
      <2>3. QED BY <1>1, <2>1, <2>2 DEF Next
    <1>2. QED BY <1>1

This proof is unnatural because of the nested occurrences of `ASSUME … PROVE …`. The point where `Next` needs to be expanded, in `<2>3`, is potentially far removed from its relevant assertion, `<1>1`. It would be better instead to rephrase the theorem as a conjunction and then derive the conjuncts with a `SUFFICES` as follows:

    THEOREM Inv /\ Next => Inv'
    <1>1. SUFFICES /\ Inv /\ A => Inv'
                   /\ Inv /\ B => Inv'
      BY DEF Next
    <1>2. ASSUME Inv, A PROVE Inv'
    <1>3. ASSUME Inv, B PROVE Inv'
    <1>4. QED BY <1>2, <1>3

In this form, the definition of `Next` is cited right next to the assertion where it is relevant. In the rest of the proof after step `<1>1`, the definition of `Next` is irrelevant. The proof is also shallower because we change an instance of a `QED` step into a `BY` leaf proof. This kind of restatement of the current goal can make proofs much easier to read and maintain.

(Strictly speaking, the `SUFFICES` step was not necessary in this simple proof because the `DEF Next` could have been folded into the proof of `<1>4`. However, in more complex proofs it is better to use `SUFFICES` as needed to rephrase the goal *up front*. These steps also serve as hints to the reader about the direction of the proof.)

### `HAVE`, `TAKE` and `WITNESS`

TLAPS provides some shortcuts for proving implications and quantifications. They can be described with their equivalent `SUFFICES` construct:

> | goal                | step                    | equivalent `SUFFICES` step                                                               |
> |---------------------|-------------------------|------------------------------------------------------------------------------------------|
> | `e => f`            | `<n>l. HAVE g`          | `<n>l. SUFFICES ASSUME g PROVE f OBVIOUS`                                                |
> | `\A x : P(x)`       | `<n>l. TAKE y`          | `<n>l. SUFFICES ASSUME NEW y PROVE P(y) OBVIOUS`                                         |
> | `\A x \in S : P(x)` | `<n>l. TAKE y \in T`    | `<n>l. SUFFICES ASSUME NEW y \in T PROVE P(y) OBVIOUS`                                   |
> | `\E x : P(x)`       | `<n>l. WITNESS e`       | `<n>l. SUFFICES P(e) OBVIOUS`                                                            |
> | `\E x \in S : P(x)` | `<n>l. WITNESS e \in T` | `<n>l. SUFFICES ASSUME e \in T PROVE P(e) <n+1>1. e \in T OBVIOUS <n+1>2. QED BY <n+1>1` |

One important deficiency of `HAVE`, `TAKE` and `WITNESS` steps is that the precise form of the rephrased goal is not textually present in the proof. The (human) reader might get confused by long chains of these steps, especially if interleaved with other kinds of steps. These constructs should therefore be used sparingly, preferably only in the lowest levels of proof where there is some actual benefit in linearizing the proof.

### `PICK`

An assumption of the form `\E x : P(x)` can be used by picking a fresh `x` for which `P(x)` is assumed. This is done using the step `PICK x : P(x)`. Note that `\E x : P(x)` need not be present exactly in the assumptions; this step accepts a subproof that supplies the justification for `\E x : P(x)`. Here is a somewhat contrived example:

    THEOREM ~ \E x \in Nat : x + 1 = 0
    <1>1. SUFFICES ASSUME \E x \in Nat : x + 1 = 0
                   PROVE  FALSE
      OBVIOUS
      (* new facts: \E x \in Nat : x + 1 = 0 *)
      (* goal: FALSE *)
    <1>2. PICK u \in Nat : u = -1
      (* goal: \E u \in Nat : u = -1 *)
      <2>1. \A n \in Nat : n + 1 = 0 => n = -1
        OBVIOUS
      <2>2. QED BY <2>1, <1>1
      (* new facts: u \in Nat, u = -1 *)
      (* goal: FALSE *)
    <1> QED BY -1 \notin Nat, <1>2
