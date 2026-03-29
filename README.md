# Mechanically-checked safety and liveness of the TetraBFT consensus protocol

This repository contains the TLA+ specification of TetraBFT, as well as evidence for its correctness in the form of inductive invariants, showing both safety and liveness, verified by model-checking for small system sizes.
For more information about TetraBFT, see our [PODC paper](https://dl.acm.org/doi/abs/10.1145/3662158.3662783) and its [extended version](https://arxiv.org/abs/2405.02615).

To check the safety and liveness of TetraBFT, run `make tetrabft-safety` and `make tetrabft-liveness`, respectively.
This uses the [Apalache](https://github.com/informalsystems/apalache) model-checker to exhaustively check, for a fixed finite domain, that the safety and liveness properties of TetraBFT hold.

For this check, the size of the system and maximum number of rounds are fixed to the values appearing in [ApaTetraBFT.tla](./ApaTetraBFT.tla).
Depending on your hardware configuration, model-checking might take a lot of time.
To speed things up, you can for example reduce the number of rounds explored by setting `MaxRound == 1` (so only rounds 0 and 1 will be considered) in [ApaTetraBFT.tla](./ApaTetraBFT.tla).

# Liveness proof

Let a "good" round be a round with a well-behaved leader, where Byzantine nodes do not take steps, and that is long enough.
We check that every good round produces a decision.
Note that this is weaker than the traditional liveness property of BFT consensus, where a good round must produce a decision even if Byzantine nodes interfere.
TetraBFT does satisfy this stronger liveness property, but it is harder to encode for checking with Apalache and we do not do so.

For checking with Apalache, we encode our liveness property as a safety property in three steps.
First, we augment the specification with a variable `goodRound` which is set non-deterministically at initialization and we modify the specification to enforce that no higher round than `goodRound` is ever started.
We also introduce a `Propose` actions which models the leader of `goodRound`, which is assumed well-behaved, making a proposal.

Second, we check that all the actions of well-behaved nodes (voting, changing round, proposing) are self-disabling.
This is formalized in file [ApaTetraBFTSelfDisablingActions.tla](./ApaPaxosSelfDisablingActions.tla).
Note that, because Apalache does not support `ENABLED`, we manually specify the enabledness conditions of the actions; to make sure we did not make a typo, we check the correctness of the enabledness predicates with TLC (see predicate `ENABLED_OK` in [TetraBFT.tla](./TetraBFT.tla)).
Because, in our finite domain, there are finitely many such actions, the fact that the actions are self-disabling implies that, under fair scheduling and in a long-enough round, all actions of well-behaved nodes are eventually disabled (the soundness of this relies on our assumption that Byzantine nodes do not take steps and therefore cannot cause an action of a well-behaved node to become enabled just before the round timer would fire).

Finally, we check that, once all fairly-scheduled actions are disabled, we have a consensus decision.

Note that the two properties we checks are safety properties, and check them by providing and checking suitable inductive invariants.

# Didactic Paxos proof

For didactic purposes, we apply the same verification techniques to the specification of Paxos found in [Paxos.tla](./Paxos.tla).
To check it, run `make paxos-safety` and `make paxos-liveness`.

If you want to modify things and play around with inductive invariants, use [show_cti.sh](./show_cti.sh) to print the latest counterexample to induction found by Apalache.
