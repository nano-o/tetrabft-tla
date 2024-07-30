------------------ MODULE TLCTetraBFT ------------------

EXTENDS TetraBFT, TLC

Symm == Permutations(P) \cup Permutations(V)

========================================================