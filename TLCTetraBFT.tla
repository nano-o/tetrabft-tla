------------------ MODULE TLCTetraBFT ------------------

EXTENDS TetraBFT, TLC

Symm == Permutations(P) \cup Permutations(V)

Canary1 == \neg (
    /\  decided # {}
    /\  \E p \in P : \E vt \in votes[p] : vt.round = 0 /\ vt.phase = 3
    /\  \A p \in P : \A vt \in votes[p] : vt.round = 0 => vt.phase < 4
)

========================================================