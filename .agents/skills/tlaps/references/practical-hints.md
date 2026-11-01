<!-- From the TLAPS documentation, https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Practical_hints.html (tlaplus/tlapm, BSD-2-Clause). Converted to Markdown 2026-10-27 with the page's own example listings inlined; written for TLAPS 1.4.x, so flag names may differ in 1.6. -->

## Hints on using TLAPS effectively

The TLA+ proof system is designed to check the validity of claims as independently as possible of specific proof back-ends. We believe that users should concentrate on writing proofs in terms of their particular applications, not in terms of the capabilities of a particular proof system. In particular, TLAPS invokes its back-ends with some default setup for automatic proof, and we try to make it hard for users to change this default setup. Expert users of back-end provers may be frustrated because they may have to develop proofs somewhat further than what would be necessary with a fine-tuned tactic script. The main payoff of limited access to the nitty-gritty details of provers is greater clarity of the resulting proofs. They are also easier to maintain across minor changes of the specification or new releases of the TLA prover.

On some occasions users will encounter situations where the prover cannot prove an "obvious" proof obligation. Here are a few hints on what to try to make the proof go through. Your additions to this list are welcome.

### Control the size of formulas and expressions

Our provers are currently not good at making abstractions that humans understand immediately. They are easily confused by moderately big proof obligations and are just as likely to work on a top-level conjunction as on a set construction buried deeply inside the formula. This can cause back-ends to become very slow or even unable to complete seemingly trivial steps. While we intend to improve the back-ends in this respect, you can help them by using local definitions in proofs and hiding these definitions in order to keep expressions small. (Keep in mind that definitions introduced in a proof are usable by default and must be hidden explicitly, unlike definitions in specifications, which must be explicitly `USE`d.)

Here is a contrived example:

    LEMMA   /\ x \in SomeVeryBigExpression
            /\ y \in AnotherBigExpression
        <=>
            /\ y \in AnotherBigExpression
            /\ x \in SomeVeryBigExpression
    <1> DEFINE S == SomeVeryBigExpression
        \** here and in the following, you may use positional names
        \** to avoid repeating the big expressions
    <1> DEFINE T == AnotherBigExpression
    <1>1. x \in S <=> x \in SomeVeryBigExpression
      OBVIOUS
    <1>2. y \in T <=> y \in AnotherBigExpression
      OBVIOUS
    <1> HIDE DEF S, T
    <1>3.   /\ x \in S
            /\ y \in T
        <=>
            /\ y \in T
            /\ x \in S
      OBVIOUS
    <1>4. QED
      BY <1>1, <1>2, <1>3

This kind of problem typically arises when reasoning about `LET` expressions, which are silently expanded by the proof manager. In a proof, introduce local definitions corresponding to the `LET` (using copy and paste from the specification), show that the overall expression equals the body of the `LET`, establish the necessary facts about these locally defined operators, and `HIDE` the definitions afterwards.

### Avoid "circular" (sets of) equations

Rewriting is one effective way to reason about equations, and it underlies the automatic proof methods used by the Isabelle back-end. The basic idea is to orient equalities such that the expressions on the left-hand side are systematically replaced by the right-hand sides. However, if the set of equations contains cycles as in

    s = f(t)
    t = g(s)

then rewriting may never terminate. Isabelle employs some (incomplete) heuristics to detect such cycles and will refuse to rewrite equations that it determines to be circular. This usually leads to its inability to infer anything about these equations. If circularity is not detected, it may cause Isabelle to enter an infinite loop. The suggested remedy is again to introduce local definitions that are hidden to break the loops.

As a concrete example consider the following proof snippet:

      <4>17. foo.name = "xyz"
        <5>1. foo = [name |-> "xyz", value |-> foo.value]
          BY <2>2
        <5>2. QED
          BY <5>1  \** may not work because <5>1 is a circular equation

One possible workaround is as follows:

      <4>17. foo.name = "xyz"
        <5>   fooval == foo.value
        <5>1. foo = [name |-> "xyz", value |-> fooval]
          BY <2>2
        <5>   HIDE DEF fooval
        <5>2. QED
          BY <5>1

### Using set extensionality

The theorem of set extensionality asserts that two sets are equal if they contain the same elements:

    THEOREM SetExtensionality == \A S,T : (\A x : x \in S <=> x \in T) => S = T

This theorem is defined in the standard module `TLAPS` and can be proved automatically in TLAPS. Nevertheless, it is sometimes necessary to appeal to that theorem for proving that two set expressions are equal. Making set extensionality a part of the background theory would be counter-productive, since it could be applied to many occurrences of the equality symbol. When necessary, it can be added explicitly in a `BY` clause for the SMT backend. For Isabelle proofs, `TLAPS` defines a specific pragma `IsaWithSetExtensionality` that instructs Isabelle to try applying the set extensionality rule for proving equality of sets.

### Reasoning about CHOOSE expressions

Consider a definition such as

    foo == CHOOSE x \in S : P(x)

In order to prove a property `Q(foo)`, you will typically prove the two following assertions:

\(a\) `\E x \in S : P(x)`  
(b) `\A x \in S : P(x) => Q(x)`

In some cases, assertion (b) can be trivial and need not be shown explicitly. Reasoning about an unbounded `CHOOSE` expression is analogous.

Remember that `CHOOSE` always denotes some value, even if `P(x)` holds for no `x \in S` (in particular, if `S = {}`), in which case the `CHOOSE` expression is fixed, but arbitrary. In practice, `CHOOSE` expressions usually arise when condition (a) is satisfied. Should you have designed your property to work even if the domain of the `CHOOSE` is empty, property `Q` must be trivial in that case, and you can structure your proof as follows:

    <3>5. Q(foo)
        <4>1. CASE \E x \in S : P(x)
          <5>1. \A x \in S : P(x) => Q(x)
          <5>2. QED
            BY <4>1, <5>1 DEF foo
        <4>2. CASE ~ \E x \in S : P(x)
          <5>1. \A x : Q(x)
          <5>2. QED
            BY <5>1
        <4>3. QED
          BY <4>1, <4>2

A frequent TLA+ idiom is to define a "null" value by writing

    NoValue == CHOOSE x : x \notin Value

The laws of set theory ensure that no set is universal, hence there exists an x that is not an element of set `Value`, ensuring condition (a) above. The theorem `NoSetContainsEverything` in the standard module TLAPS can be used to prove this condition.

The SMT backend may fail to prove obligations involving several `CHOOSE` expressions. In particular, the axioms for determinacy of `CHOOSE` stating

    (\A x : P(x) <=> Q(x))  =>  (CHOOSE x : P(x)) = (CHOOSE x : Q(x))

may not be available to the SMT solver.

### Help Zenon and Isabelle When Reasoning About Records

In one proof, we had

    mb == [type  |-> "1b", bal |-> b, acc |-> self,
           mCBal |-> maxCBal[self], mCVal |-> maxCVal[self]]

and were trying to prove

    m1 # mb /\ m2 # mb

from facts that included

    m1.type = "2av" /\ m2.type = "2av"

Zenon failed on the proof and Isabelle proved it only after a long time. (In fact, we originally stopped the proof because it was taking so long.) However, Zenon proved it instantly when we added `mb.type = "1b"` to the `BY` statement's list of facts. The provers are reluctant to try finding relations of the form `record.field = value`. They often need help.

The SMT backend should not require similar help for reasoning about records.

### Using theorems from instantiated modules

When you create an instance `I == INSTANCE M` of a module `M`, all assumptions of `M` become additional hypotheses of every theorem instance (see Section 17.5.5 of *Specifying Systems*). For example, consider the following modules, where the theorem `Thm` of module `A` is proved using the assumption `NA`:

    MODULE Lib ----
    EXTENDS Integers
    Pos(n) == n > 0
    ====
    ---- MODULE A ----
    EXTENDS Lib
    CONSTANT N
    ASSUME NA == Pos(N)

    THEOREM Thm == N > 0
    BY NA DEF Pos
    ====

If a module `B` imports `A` via `I == INSTANCE A`, then the theorem instance `I!Thm` does *not* stand for the bare fact `N > 0`. Instead, it carries the (instantiated) assumptions of `A` as hypotheses, so it represents the sequent

`ASSUME I!Pos(N) PROVE N > 0`

In order to use `I!Thm` you therefore have to discharge its hypothesis `I!Pos(N)` explicitly. The importing module declares the matching assumption `NA == Pos(N)`, so one might expect `BY I!Thm, NA` to close the goal.

However, a subtlety arises because the assumption mentions an operator imported through `EXTENDS` (here `Pos`, defined in the common module `Lib`). The instance re-exports that operator under the `I!` prefix (`I!Pos`), while the importing module keeps the unprefixed name (`Pos`). These denote the same operator but are two distinct internal symbols, and the back-ends do not automatically relate them. The hypothesis carried by `I!Thm` is thus `I!Pos(N)`, whereas the local assumption `NA` only establishes `Pos(N)`, so even `BY I!Thm, NA` is not enough. The remedy is a *bridge* theorem that equates the prefixed operator with its local counterpart and is then cited alongside the instantiated theorem:

    MODULE B ----
    EXTENDS Lib
    CONSTANT N
    ASSUME NA == Pos(N)

    I == INSTANCE A

    THEOREM Bridge == \A n : I!Pos(n) = Pos(n)
    BY DEF I!Pos, Pos

    THEOREM Test == N > 0
    \* BY I!Thm, NA          \* FAILS: I!Pos and Pos are distinct symbols
    BY I!Thm, NA, Bridge     \* WORKS
    ====

### Divide and Conquer

When the provers can't prove something that you think is obvious, it's usually because it isn't true. You can easily spend hours looking at a proof obligation without noticing a tiny mistake. The best way to find a mistake is by breaking the proof into simpler steps. Continuing to do this on the step or steps whose proof fails will eventually lead you to discover the problem – usually a missing hypothesis or a mistake in a formula. When you correct the mistake in the original proof step, the prover will usually be able to prove it.

### Don't Reinvent Mathematics

We expect that most people who use TLAPS will do so because they want to verify properties of an algorithm or system. We have therefore not devoted our limited resources to building libraries of mathematical results. If you want to create such libraries, we would welcome your help. However, if you are concerned with an algorithm or system, you should not be spending your time proving basic mathematical facts. Instead, you should assert the mathematical theorems you need as assumptions or theorems.

Asserting facts is dangerous, because it's easy to make a mistake and assert something false, making your entire proof unsound. Fortunately, you can use the TLC model checker to avoid such mistakes. For example, our example correctness proof of Euclid's algorithm uses this assumption

    ASSUME GCDProperty3 ==
           \A p, q \in Nat \ {0}: (p < q) => GCD(p, q) = GCD(p, q-p)

TLC cannot check this assumption because it can't evaluate a quantification over an infinite set. However, you can tell TLC to replace the definition of Nat with

    Nat == 0..50

(In the Toolbox, use the Definition Override section of the model's Advanced Options page.) TLC quickly verifies this assumption. (TLC checks each `ASSUME`; to add an assumption that you don't want TLC to check, make it an `AXIOM`.)

This kind of checking is almost certain to catch an error in expressing a fundamentally correct mathematical result – except when the only counterexamples are infinite. Fortunately, this is rarely the case when the result is needed for reasoning about an algorithm or system.

### It's Easier to Prove Something if it's True

Before trying to prove a property of an algorithm or system, try to check it with TLC. Even if TLC cannot check a large enough model to catch all errors, running it on a small model can still catch many simple errors. You will save a lot of time if you let TLC find these errors instead of discovering them while writing the proof.
