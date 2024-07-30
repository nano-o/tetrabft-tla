--------------------- MODULE TetraBFT ---------------------

(*********************************************************************************)
(* This is a high-level specification of the TetraBFT consensus algorithm. There *)
(* is no network or messages at this level of abstraction, but we do model       *)
(* Byzantine failures.                                                           *)
(*********************************************************************************)

\* WIP: liveness

EXTENDS Integers

CONSTANTS
    V \* the set of values to decide on
,   P \* the set of processes (typically 3f+1 nodes)
,   Quorum \* the set of quorums (typically sets of 2f+1 nodes out of 3f+1)
,   Blocking \* the set of blocking sets (typically sets of f+1 nodes out of 3f+1)
,   Round \* the set of rounds

\* Each round consists of 4 phases:
Phase == 1..4
\* A vote is cast in a phase of a round and for a value:
\* @typeAlias: voteType = {round : Int, value : V, phase : Int};
Vote == [round: Round, phase: Phase, value: V]

NotAVote == [round |-> -1, phase |-> 1, value |-> CHOOSE v \in V : TRUE]

\* Whether vote v is maximal in S
\* @type: ($voteType, Set($voteType)) => Bool;
Maximal(vt, S) ==
    /\ vt \in S
    /\ \A vt2 \in S : vt2.round <= vt.round

\* A maximal element in the set S, if such exists, and otherwise the default value provided:
Max(S, default) ==
    IF \E e \in S : Maximal(e, S)
    THEN CHOOSE e \in S : Maximal(e, S)
    ELSE default

\* We now specify the behaviors of the algorithm:

VARIABLES 
    B, \* B is the set of Byzantine processes
    votes,
    round,
    goodRound \* set to true to indicate we are starting a round that lasts "long enough"
vars == <<B, round, votes, goodRound>>

TypeOK ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Round]
    /\ B \in SUBSET P
    /\ goodRound \in BOOLEAN
TypeOK_ == TypeOK

decided == {v \in V : \E Q \in Quorum, r \in Round : \A p \in Q \ B :
    [round |-> r, phase |-> 4, value |-> v] \in votes[p] }

\* largest vote of p in phase `phase' before round r
HighestVote(p, phase, r) ==
    LET vs == {v \in votes[p] : v.phase = phase /\ v.round < r} IN
      Max(vs, NotAVote)

\* second largest vote (for a value different from the highest vote) of p in phase `phase' before round r
SecondHighestVote(p, phase, r) ==
    LET largest == HighestVote(p, phase, r)
        vs == {v \in votes[p] : v.phase = phase /\ v.round < r /\ v.value # largest.value}
    IN Max(vs, NotAVote)

\* `v' is safe in round `r2' according to the votes of process `p' in phase `phase' before round r:
ClaimsSafeAt(v, r, r2, p, phase) ==
    \/ r2 = 0
    \/ LET mv == HighestVote(p, 1, r) IN \* Highest vote of p in phase 1 before round r
         /\ r2 <= mv.round
         /\ mv.value = v
    \/ r2 <= SecondHighestVote(p, 1, r).round

\* Whether value v is safe to vote for/propose in round r by process p
\* In case of a vote, we'll use phaseA=4 and phaseB=1
\* In case of a proposal, we'll use phaseA=3 and phaseB=2
ShowsSafeAt(Q, v, r, phaseA, phaseB) ==
    \/ r = 0
    \/  /\ \A q \in Q : round[q] >= r \* every member of Q is in round at least r
        /\  \/ \A q \in Q : HighestVote(q, phaseA, r).round = -1 \* members of Q never voted in phaseA before r
            \/ \E r2 \in Round :
                /\ 0 <= r2 /\ r2 < r
                \* no member of Q voted in phaseA in round r2 or later, and
                \* all members of Q that voted in r2 voted for v:
                /\ \A q \in Q : LET hvq == HighestVote(q, phaseA, r) IN
                    /\ hvq.round <= r2
                    /\ hvq.round = r2 => hvq.value = v
                /\ \* v must be safe at r2
                    \/ \E S \in Blocking : \A q \in S : ClaimsSafeAt(v, r, r2, q, phaseB)
                    \/ \E S1,S2 \in Blocking : \E v1,v2 \in V : \E r3,r4 \in Round :
                        /\ v1 # v2
                        /\ r2 <= r3 /\ r3 < r4 /\ r4 < r
                        /\ \A q \in S1 : ClaimsSafeAt(v1, r, r3, q, phaseB)
                        /\ \A q \in S2 : ClaimsSafeAt(v2, r, r4, q, phaseB)

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> 0]
    /\ B \in {P \ Q : Q \in Quorum}
    /\ goodRound = FALSE

DoVote(p, v, r, phase) ==
    \* never voted before in this round and phase:
    /\ \A w \in V : [round |-> r, phase |-> phase, value |-> w] \notin votes[p]
    \* cast the vote:
    /\ votes' = [votes EXCEPT ![p] = @ \union {[round |-> r, phase |-> phase, value |-> v]}]
    /\ UNCHANGED <<round, B, goodRound>>

Vote1(p, v, r) ==
    /\ r = round[p]
    /\ \E Q \in Quorum : ShowsSafeAt(Q, v, r, 4, 1)
    /\ DoVote(p, v, r, 1)

\* whether v has been voted for by a quorum of p in phase `phase' of round `r':
Accepted(p, v, r, phase) == \E Q \in Quorum :
    /\ p \in Q
    /\ \A q \in Q : [round |-> r, phase |-> phase, value |-> v] \in votes[q]

Vote2(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 1)
    /\ DoVote(p, v, r, 2)

Vote3(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 2)
    /\ DoVote(p, v, r, 3)

Vote4(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 3)
    /\ DoVote(p, v, r, 4)

StartRound(p, r) ==
    /\  round[p] < r
    /\  round' = [round EXCEPT ![p] = r]
    /\  \/  /\  goodRound' = TRUE
            /\  UNCHANGED <<votes, B>>
        \/  /\  UNCHANGED <<votes, B, goodRound>>

\* This models malicious behavior
ByzantineHavoc ==
    \E new_votes \in [B -> SUBSET Vote] : \E new_round \in [B -> Round] :
    /\  votes' = [p \in P |-> IF p \in B THEN new_votes[p] ELSE votes[p]]
    /\  round' = [p \in P |-> IF p \in B THEN new_round[p] ELSE round[p]]
    /\  UNCHANGED <<B, goodRound>>

Next ==
    \/  ByzantineHavoc
    \/  \E p \in P, v \in V, r \in Round :
        \/ Vote1(p, v, r)
        \/ Vote2(p, v, r)
        \/ Vote3(p, v, r)
        \/ Vote4(p, v, r)
        \/ StartRound(p, r)

Spec == Init /\ [][Next]_vars

Safety == \A v1,v2 \in decided : v1 = v2

\* Simple properties

VotedFor(p, r, v) ==  [round |-> r, phase |-> 4, value |-> v] \in votes[p]

NoFutureVote == \A p \in P \ B : \A vt \in votes[p] : vt.round <= round[p]

OneValuePerPhasePerRound == \A p \in P \ B : \A vt \in votes[p] :
    \A vt2 \in votes[p] : vt2.round = vt.round /\ vt2.phase = vt.phase => vt2.value = vt.value

VoteHasQuorumInPreviousPhase == \A p \in P \ B : \A vt \in votes[p] : vt.phase > 1 =>
    \E Q \in Quorum : \A q \in Q \ B :
        [round |-> vt.round, phase |-> (vt.phase)-1, value |-> vt.value] \in votes[q]

Invariant1 ==
    /\  NoFutureVote
    /\  OneValuePerPhasePerRound
    /\  VoteHasQuorumInPreviousPhase
Invariant1_ == TypeOK /\ Invariant1

\* Now the main invariant

DidNotVoteAt(p, r) == \A v \in V : \neg VotedFor(p, r, v)

CannotVoteAt(p, r) == round[p] > r /\ DidNotVoteAt(p, r)

NoneOtherChoosableAt(r, v) == \E Q \in Quorum :
    \A p \in Q \ B : VotedFor(p, r, v) \/ CannotVoteAt(p, r)

SafeAt(r, v) == \A c \in Round : 0 <= c /\ c < r => NoneOtherChoosableAt(c, v)

VotesSafe == \A p \in P \ B : \A vt \in votes[p] :
    SafeAt(vt.round, vt.value)
VotesSafe_ == TypeOK /\ Invariant1 /\ VotesSafe

\* The full inductive invariant:
Invariant ==
    /\  TypeOK
    /\  NoFutureVote
    /\  OneValuePerPhasePerRound
    \* It's interesting that we don't need the fact that there's at most one value voted by well-behaved processes in phases > 1
    /\  VoteHasQuorumInPreviousPhase
    /\  VotesSafe
    /\  Safety
Invariant_ == Invariant

=============================================================================