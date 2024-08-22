------------------------------- MODULE PaxosEnabledness -------------------------------

\* Here we show that Propose, IncreaseCurrBal, and VoteFor are irrevocably self-disabling.

EXTENDS Integers

CONSTANTS
    Value,
    Acceptor,
    Leader(_),
    Quorum,
    Ballot

VARIABLES
    votes,
    currBal,
    proposals,
    crashed,
    goodBallot,
    proposeTaken,
    voteForTaken,
    increaseCurrBalTaken

vars == <<votes, currBal, crashed, goodBallot, voteForTaken, increaseCurrBalTaken>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times Value)]
    /\ currBal \in [Acceptor -> Ballot\cup {-1}]
    /\ crashed \in SUBSET Acceptor
    /\ goodBallot \in Ballot
    /\ proposals \in SUBSET (Ballot\times Value)
    /\ proposeTaken \in [Ballot\times Value -> BOOLEAN]
    /\ voteForTaken \in [Acceptor \times Ballot \times Value -> BOOLEAN]
    /\ increaseCurrBalTaken \in [Acceptor \times Ballot -> BOOLEAN]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : currBal[a] \geq b
  \* NOTE: `^Apalache^' does not support non-constant integer ranges (e.g. we cannot write (c+1)..(b-1))
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b => \A a \in Q : DidNotVoteAt(a, d)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ currBal = [a \in Acceptor |-> -1]
    /\ crashed = {}
    /\ proposals = {}
    /\ goodBallot \in Ballot
    /\ proposeTaken = [x \in Ballot\times Value |-> FALSE]
    /\ voteForTaken = [x \in Acceptor \times Ballot \times Value |-> FALSE]
    /\ increaseCurrBalTaken = [x \in Acceptor \times Ballot |-> FALSE]

Crash(a) ==
    /\  goodBallot > -1 => a # Leader(goodBallot)
    /\  crashed' = crashed \cup {a}
    /\  \E Q \in Quorum : \A a2 \in Q : a2 \notin crashed'
    /\  UNCHANGED <<votes, currBal, goodBallot, proposals, proposeTaken, voteForTaken, increaseCurrBalTaken>>

Propose(b, v) ==
    /\  Leader(b) \notin crashed
    /\  \A prop \in proposals : prop[1] # b
    /\  \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\  proposals' = proposals \cup {<<b,v>>}
    /\  proposeTaken' = [proposeTaken EXCEPT ![<<b,v>>] = TRUE]
    /\  UNCHANGED <<votes, currBal, crashed, goodBallot, voteForTaken, increaseCurrBalTaken>>

Propose_ENABLED(b, v) ==
    /\  Leader(b) \notin crashed
    /\  \A prop \in proposals : prop[1] # b
    /\  \E Q \in Quorum : ShowsSafeAt(Q, b, v)

IncreaseCurrBal(a, b) ==
  /\ a \notin crashed
  \* once a good ballot started, we cannot increase currBal beyond it:
  /\ goodBallot > -1 => b <= goodBallot
  /\ b > currBal[a]
  /\ currBal' = [currBal EXCEPT ![a] = b]
  /\ increaseCurrBalTaken' = [increaseCurrBalTaken EXCEPT ![<<a,b>>] = TRUE]
  /\ UNCHANGED <<votes, crashed, goodBallot, proposals, proposeTaken, voteForTaken>>

IncreaseCurrBal_ENABLED(a, b) ==
  /\ a \notin crashed
  /\ goodBallot > -1 => b <= goodBallot
  /\ b > currBal[a]

VoteFor(a, b, v) ==
    /\ a \notin crashed
    /\ currBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ currBal' = [currBal EXCEPT ![a] = b]
    /\ voteForTaken' = [voteForTaken EXCEPT ![<<a,b,v>>] = TRUE]
    /\ UNCHANGED <<crashed, goodBallot, proposals, proposeTaken, increaseCurrBalTaken>>

VoteFor_ENABLED(a, b, v) ==
    /\ a \notin crashed
    /\ currBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)

Next  ==  \E a \in Acceptor, b \in Ballot, v \in Value :
    \/ IncreaseCurrBal(a, b)
    \/ Propose(b, v)
    \/ VoteFor(a, b, v)
    \/ Crash(a)

Spec == Init /\ [][Next]_vars

SelfDisabling == 
    /\  TypeOK
    /\  \A a \in Acceptor, b \in Ballot, v \in Value :
        /\  voteForTaken[<<a,b,v>>] =>
            /\  \neg VoteFor_ENABLED(a, b, v)
            /\  <<b,v>> \in votes[a]
        /\  increaseCurrBalTaken[<<a,b>>] => 
            /\  \neg IncreaseCurrBal_ENABLED(a, b)
            /\  currBal[a] >= b
        /\  proposeTaken[<<b,v>>] => 
            /\  \neg Propose_ENABLED(b, v)
            /\   <<b,v>> \in proposals

THEOREM Spec => []SelfDisabling

=====================================================================================