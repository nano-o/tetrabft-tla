This repository contains the TLA+ specification of TetraBFT. For more information about TetraBFT, see our [PODC paper](https://dl.acm.org/doi/abs/10.1145/3662158.3662783).

On Linux, to check that the provided invariant is inductive, run `make check`. Depending on your hardware configuration, this might take a lot of time. Note that `ApaVoting.tla` fixes values for e.g. the set of processes or the maximum number of rounds to explore during model-checking. For example, setting `MaxRound == 1` should speed things up because it means that the model-checker will only explore rounds 0 and 1.
