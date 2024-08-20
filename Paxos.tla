------------------------------- MODULE Paxos -------------------------------

EXTENDS Integers

CONSTANTS
    Value,
    Acceptor,
    Quorum,
    Ballot

VARIABLES
    votes, \* 2b
    currBal,
    proposals, \* 2a
    crashed,
    goodBallot

vars == <<votes, currBal, proposals, crashed, goodBallot>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times Value)]
    /\ currBal \in [Acceptor -> Ballot\cup {-1}]
    /\ proposals \in SUBSET (Ballot\times Value)
    /\ crashed \in SUBSET Acceptor
    /\ goodBallot \in Ballot

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) ==
  \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ currBal[a] > b
                      /\ DidNotVoteAt(a, b)
NoneOtherChoosableAt(b, v) ==
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in Ballot : c < b => NoneOtherChoosableAt(c, v)

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
    /\ proposals = {}
    /\ crashed = {}
    /\ goodBallot \in Ballot

Crash(a) ==
    /\  crashed' = crashed \cup {a}
    /\  \E Q \in Quorum : \A a2 \in Q : a2 \notin crashed'
    /\  UNCHANGED <<votes, currBal, proposals, goodBallot>>

Propose(b, v) ==
    /\ \A prop \in proposals : prop[1] # b
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\  proposals' = proposals \cup {<<b,v>>}
    /\  UNCHANGED <<votes, currBal, crashed, goodBallot>>

Propose_ENABLED(b, v) ==
    /\ \A prop \in proposals : prop[1] # b
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)

IncreaseCurrBal(a, b) ==
  /\ a \notin crashed
  \* once a good ballot started, we cannot increase currBal beyond it:
  /\ goodBallot > -1 => b <= goodBallot
  /\ b > currBal[a]
  /\ currBal' = [currBal EXCEPT ![a] = b]
  /\ UNCHANGED <<votes, proposals, crashed, goodBallot>>

IncreaseCurrBal_ENABLED(a, b) ==
  /\ a \notin crashed
  /\ goodBallot > -1 => b <= goodBallot
  /\ b > currBal[a]

VoteFor(a, b, v) ==
    /\ a \notin crashed
    /\ currBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ <<b,v>> \in proposals
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ currBal' = [currBal EXCEPT ![a] = b]
    /\ UNCHANGED <<crashed, proposals, goodBallot>>

VoteFor_ENABLED(a, b, v) ==
    /\ a \notin crashed
    /\ currBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ <<b,v>> \in proposals

Next  ==  \E a \in Acceptor, b \in Ballot, v \in Value :
    \/ IncreaseCurrBal(a, b)
    \/ Propose(b, v)
    \/ VoteFor(a, b, v)
    \/ Crash(a)

Spec == Init /\ [][Next]_vars

ProposalsSafe == \A b \in Ballot, v \in Value :
    <<b, v>> \in proposals => SafeAt(b, v)

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
        /\  (VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2)) => v1 = v2
        /\  (<<b,v1>> \in proposals /\ <<b,v2>> \in proposals) => v1 = v2

VoteForProposal == \A a \in Acceptor, b \in Ballot, v \in Value :
    VotedFor(a, b, v) => <<b,v>> \in proposals

NoVoteAfterCurrBal == \A a \in Acceptor, b \in Ballot, v \in Value :
    <<b,v>> \in votes[a] => /\ b <= currBal[a]

Consistency == \A v,w \in chosen : v = w

\* This invariant is inductive and establishes consistency:
Invariant ==
  /\ TypeOK
  /\ VoteForProposal
  /\ OneValuePerBallot
  /\ NoVoteAfterCurrBal
  /\ ProposalsSafe
  /\ Consistency
Invariant_ == Invariant

\* NOTE: TLC can handle ENABLED, but not Apalache
Liveness ==
    (/\ goodBallot > -1
     /\ \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ \neg IncreaseCurrBal_ENABLED(a, b)
        /\ \neg VoteFor_ENABLED(a, b, v)
        /\ \neg Propose_ENABLED(b, v))
    => chosen # {}

\* Check this with TLC to catch potential errors:
ENABLED_OK ==
    \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ IncreaseCurrBal_ENABLED(a, b) = ENABLED IncreaseCurrBal(a, b)
        /\ VoteFor_ENABLED(a, b, v) = ENABLED VoteFor(a, b, v)
        /\ Propose_ENABLED(b, v) = ENABLED Propose(b, v)

NothingAfterGoodBallot == goodBallot > -1 =>
    \A a \in Acceptor, b \in Ballot, v \in Value :
        VotedFor(a, b, v) \/ <<b,v>> \in proposals \/ b = currBal[a] => b <= goodBallot

\* Supporting invariant for liveness:
LivenessInvariant ==
    /\  TypeOK
    /\  VoteForProposal
    /\  OneValuePerBallot
    /\  NothingAfterGoodBallot
    /\  \E Q \in Quorum : Q \cap crashed = {}
LivenessInvariant_ == LivenessInvariant

Liveness_ ==
    LivenessInvariant
    
Canary1 == \neg (
    \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ \neg IncreaseCurrBal_ENABLED(a, b)
        /\ \neg VoteFor_ENABLED(a, b, v)
        /\ \neg Propose_ENABLED(b, v)
)

\* Now let's try with temporal logic:

RealLiveness == [](goodBallot > -1 => <>(chosen # {}))

LiveSpec == 
    /\  Init
    /\  [][Next]_vars
    /\  \A a \in Acceptor, b \in Ballot, v \in Value :
            /\  WF_vars( IncreaseCurrBal(a, b) )
            /\  WF_vars( VoteFor(a, b, v) )
            /\  WF_vars( Propose(b, v) )

=====================================================================================