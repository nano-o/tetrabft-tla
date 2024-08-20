This repository contains the TLA+ specification of TetraBFT, as well as evidence for its correctness in the form of inductive invariants, showing both safety and liveness, verified by model-checking for small system sizes.
For more information about TetraBFT, see our [PODC paper](https://dl.acm.org/doi/abs/10.1145/3662158.3662783) and its [extended version](https://arxiv.org/abs/2405.02615).

To check the safety of TetraBFT, run `make safety`. This uses the [Apalache](https://github.com/informalsystems/apalache) model-checker to exhaustively check that an invariant implying safety is inductive.
For this check, the size of the system and maximum number of rounds are fixed to the values appearing in [ApaTetraBFT.tla](./ApaTetraBFT.tla).
Depending on your hardware configuration, model-checking might take a lot of time.
To speed things up, you can for example reduce the number of rounds explored by setting `MaxRound == 1` (so only rounds 0 and 1 will be considered) in [ApaTetraBFT.tla](./ApaTetraBFT.tla).

TODO: explain liveness.

Finally, for didactic purposes, we apply the same verification techniques to the specification of Paxos found in [Paxos.tla](./Paxos.tla).
To check it, run `make paxos`.

If you want to modify things and play around, use [show_cti.sh](./show_cti.sh) to print the latest counterexample to induction found by Apalache.
