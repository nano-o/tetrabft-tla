# Mechanically-checked safety and liveness of the TetraBFT consensus protocol

This repository contains the TLA+ specification of TetraBFT, as well as evidence for its correctness in the form of inductive invariants, showing both safety and liveness, verified by model-checking for small system sizes.
For more information about TetraBFT, see our [PODC paper](https://dl.acm.org/doi/abs/10.1145/3662158.3662783) and its [extended version](https://arxiv.org/abs/2405.02615).

To check the safety and liveness of TetraBFT, run `make tetrabft-safety` and `make tetrabft-liveness`, respectively.
This uses the [Apalache](https://github.com/informalsystems/apalache) model-checker to exhaustively check, for a fixed finite domain, that the safety and liveness properties of TetraBFT hold.

For this check, the size of the system and maximum number of rounds are fixed to the values appearing in [ApaTetraBFT.tla](./ApaTetraBFT.tla).
Depending on your hardware configuration, model-checking might take a lot of time.
To speed things up, you can for example reduce the number of rounds explored by setting `MaxRound == 1` (so only rounds 0 and 1 will be considered) in [ApaTetraBFT.tla](./ApaTetraBFT.tla).

# Liveness proof

For liveness, we proceed in three steps.
First, we augment the specification with a variable `goodRound` which is set non-deterministically at initialization and we modify the specification to enforce that no higher round than `goodRound` is ever started.
We also introduce a `Propose` actions which models the leader of `goodRound`, which is assumed well-behaved, making a proposal.
This formalizes the assumption that there is eventually a round that lasts long enough and that has a well-behaved leader.

Second, we check that all the actions that are fairly scheduled (voting, changing round, proposing) are self-disabling.
This is formalized in file [ApaTetraBFTSelfDisablingActions.tla](./ApaPaxosSelfDisablingActions.tla).
Note that, because Apalache does not support `ENABLED`, we manually specify the enabledness conditions of the actions; to make sure we did not make a typo, we check the correctness of the enabledness predicates with TLC (see predicate `ENABLED_OK` in [TetraBFT.tla](./TetraBFT.tla)).

Because, in our finite domain, there are finitely many such actions, the fact that the actions are self-disabling implies that, under fair scheduling, all actions are eventually disabled.

Finally, we check that, once all fairly-scheduled actions are disabled, a quorum of well-behaved processes has voted unanimously.

Note that the two properties we checks are safety properties, and check them by providing and checking suitable inductive invariants.

# Didactic Paxos proof

For didactic purposes, we apply the same verification techniques to the specification of Paxos found in [Paxos.tla](./Paxos.tla).
To check it, run `make paxos-safety` and `make paxos-liveness`.

If you want to modify things and play around with inductive invariants, use [show_cti.sh](./show_cti.sh) to print the latest counterexample to induction found by Apalache.
