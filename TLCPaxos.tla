--------------------------- MODULE TLCPaxos -------------------------------

EXTENDS Paxos, FiniteSets, TLC

Symm == Permutations(Acceptor) \cup Permutations(Value)

\* debugging canary:
Canary1 == \neg (
    \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ \neg IncreaseCurrBal_ENABLED(a, b)
        /\ \neg VoteFor_ENABLED(a, b, v)
        /\ \neg Propose_ENABLED(b, v)
)

leaderFun(b) ==
    LET PID == 
            CHOOSE f \in [Acceptor -> 0..Cardinality(Acceptor)] :
                \A a1,a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
    IN  CHOOSE a \in Acceptor : PID[a] = b % Cardinality(Acceptor)

===================================================================================