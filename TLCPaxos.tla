--------------------------- MODULE TLCPaxos -------------------------------

EXTENDS Paxos, TLC

Symm == Permutations(Acceptor) \cup Permutations(Value)

\* debugging canary:
Canary1 == \neg (
    \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ \neg IncreaseCurrBal_ENABLED(a, b)
        /\ \neg VoteFor_ENABLED(a, b, v)
        /\ \neg Propose_ENABLED(b, v)
)

===================================================================================