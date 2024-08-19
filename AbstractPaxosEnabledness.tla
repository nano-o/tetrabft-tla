------------------------------- MODULE AbstractPaxosEnabledness -------------------------------


\* To make sure that no action remains enabled forever, we check that starting every action disables itself

EXTENDS Integers

CONSTANTS
    Value,
    Acceptor,
    Quorum,
    Ballot

VARIABLES
    votes,
    maxBal,
    crashed,
    goodBallot,
    voteFor,
    increaseMaxBal


vars == <<votes, maxBal, crashed, goodBallot, voteFor, increaseMaxBal>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times Value)]
    /\ maxBal \in [Acceptor -> Ballot\cup {-1}]
    /\ crashed \in SUBSET Acceptor
    /\ goodBallot \in Ballot
    /\ voteFor \in [Acceptor \times Ballot \times Value -> BOOLEAN]
    /\ increaseMaxBal \in [Acceptor \times Ballot -> BOOLEAN]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  \* NOTE: `^Apalache^' does not support non-constant integer ranges (e.g. we cannot write (c+1)..(b-1))
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b => \A a \in Q : DidNotVoteAt(a, d)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ crashed = {}
    /\ goodBallot \in Ballot
    /\ voteFor = [a \in Acceptor \times Ballot \times Value |-> FALSE]
    /\ increaseMaxBal = [a \in Acceptor \times Ballot |-> FALSE]

Crash(a) ==
    /\  crashed' = crashed \cup {a}
    /\  \E Q \in Quorum : \A a2 \in Q : a2 \notin crashed'
    /\  UNCHANGED <<votes, maxBal, goodBallot, voteFor, increaseMaxBal>>

IncreaseMaxBal(a, b) ==
  /\ a \notin crashed
  \* once a good ballot started, we cannot increase maxBal beyond it:
  /\ goodBallot > -1 => b <= goodBallot
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
\*   /\ increaseMaxBal' = [increaseMaxBal EXCEPT ![a] = [c \in Ballot |-> IF c = b THEN TRUE ELSE increaseMaxBal[a][c]]]
  /\ increaseMaxBal' = [increaseMaxBal EXCEPT ![<<a,b>>] = TRUE]
  /\ UNCHANGED <<votes, crashed, goodBallot, voteFor>>

IncreaseMaxBal_ENABLED(a, b) ==
  /\ a \notin crashed
  /\ goodBallot > -1 => b <= goodBallot
  /\ b > maxBal[a]

VoteFor(a, b, v) ==
    /\ a \notin crashed
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ voteFor' = [voteFor EXCEPT ![<<a,b,v>>] = TRUE]
    /\ UNCHANGED <<crashed, goodBallot, increaseMaxBal>>

VoteFor_ENABLED(a, b, v) ==
    /\ a \notin crashed
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)

Next  ==  \E a \in Acceptor, b \in Ballot, v \in Value :
    \/ IncreaseMaxBal(a, b)
    \/ VoteFor(a, b, v)
    \/ Crash(a)

Spec == Init /\ [][Next]_vars

NoActionTaken == 
    /\  TypeOK
    /\  \A a \in Acceptor, b \in Ballot, v \in Value :
        /\  \neg voteFor[<<a, b, v>>]
        /\  \neg increaseMaxBal[<<a, b>>]

SelfDisabling == \A a \in Acceptor, b \in Ballot, v \in Value :
    /\  voteFor[<<a,b,v>>] => \neg VoteFor_ENABLED(a, b, v)
    /\  increaseMaxBal[<<a,b>>] => \neg IncreaseMaxBal_ENABLED(a, b)



=====================================================================================