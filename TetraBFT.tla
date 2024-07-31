--------------------- MODULE TetraBFT ---------------------

(*********************************************************************************)
(* This is a high-level specification of the TetraBFT consensus algorithm. There *)
(* is no network or messages at this level of abstraction, but we do model       *)
(* Byzantine failures.                                                           *)
(*********************************************************************************)

\* WIP: liveness
\* TODO: model leader proposal

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
    Byz, \* Byz is the set of Byzantine processes
    votes,
    round,
    proposal,
    goodRound \* set to true to indicate we are starting a round that lasts "long enough"
vars == <<Byz, round, votes, proposal, goodRound>>

TypeOK ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Round \cup {-1}]
    /\ proposal \in [Round -> V]
    /\ Byz \in SUBSET P
    /\ goodRound \in BOOLEAN
TypeOK_ == TypeOK

decided == {v \in V : \E Q \in Quorum, r \in Round : \A p \in Q \ Byz :
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
    /\ round = [p \in P |-> -1]
    /\ Byz \in {P \ Q : Q \in Quorum}
    /\ proposal = [r \in Round |-> CHOOSE v \in V : TRUE]
    /\ goodRound = FALSE

\* just a helper:
DoVote(p, v, r, phase) ==
    \* never voted before in this round and phase:
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # phase
    \* cast the vote:
    /\ votes' = [votes EXCEPT ![p] = @ \union {[round |-> r, phase |-> phase, value |-> v]}]
    /\ UNCHANGED <<round, Byz, proposal, goodRound>>

StartRound(p, r) ==
    /\  p \notin Byz
    /\  goodRound => \E p2 \in P \ Byz : r <= round[p2]\* a good round lasts "long enough", i.e. forever
    /\  round[p] < r
    /\  round' = [round EXCEPT ![p] = r]
    /\  \/  /\  \A p2 \in P \ Byz : round[p2] < r
            /\  \E v \in V :
                    /\  \E Q \in Quorum : ShowsSafeAt(Q, v, r, 3, 2)
                    /\  proposal' = [proposal EXCEPT ![r] = v]
            /\  goodRound' = TRUE
            /\  UNCHANGED <<votes, Byz>>
        \/  /\  UNCHANGED <<votes, Byz, proposal, goodRound>>

Vote1(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ goodRound => v = proposal[r]
    /\ \E Q \in Quorum : ShowsSafeAt(Q, v, r, 4, 1)
    /\ DoVote(p, v, r, 1)


\* whether v has been voted for by a quorum in phase `phase' of round `r':
Accepted(p, v, r, phase) == \E Q \in Quorum :
    \A q \in Q : [round |-> r, phase |-> phase, value |-> v] \in votes[q]

Vote2(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ Accepted(p, v, r, 1)
    /\ DoVote(p, v, r, 2)

Vote3(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ Accepted(p, v, r, 2)
    /\ DoVote(p, v, r, 3)

Vote4(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ Accepted(p, v, r, 3)
    /\ DoVote(p, v, r, 4)

\* This models malicious behavior
ByzantineHavoc ==
    \E new_votes \in [Byz -> SUBSET Vote] : \E new_round \in [Byz -> Round] :
    /\  votes' = [p \in P |-> IF p \in Byz THEN new_votes[p] ELSE votes[p]]
    /\  round' = [p \in P |-> IF p \in Byz THEN new_round[p] ELSE round[p]]
    /\  UNCHANGED <<Byz, proposal, goodRound>>

Next ==
    \E p \in P, v \in V, r \in Round :
        \/ Vote1(p, v, r)
        \/ Vote2(p, v, r)
        \/ Vote3(p, v, r)
        \/ Vote4(p, v, r)
        \/ StartRound(p, r)
        \* \/ ByzantineHavoc

Spec == Init /\ [][Next]_vars

Safety == \A v1,v2 \in decided : v1 = v2

\* Manual encoding of ENABLED for Apalache:

Vote1_ENABLED(p, v, r) ==
    /\ p \notin Byz
    /\ goodRound => v = proposal[r]
    /\ r = round[p]
    /\ \E Q \in Quorum : ShowsSafeAt(Q, v, r, 4, 1)
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # 1
    
Vote2_ENABLED(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ Accepted(p, v, r, 1)
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # 2
    
Vote3_ENABLED(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ Accepted(p, v, r, 2)
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # 3

Vote4_ENABLED(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ Accepted(p, v, r, 3)
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # 4

StartRound_ENABLED(p, r) == round[p] < r /\ p \notin Byz

\* For use with TLC to catch errors in the ENABLED predicates:
ENABLED_OK == \A p \in P, v \in V, r \in Round :
    /\  (ENABLED Vote1(p, v, r)) = Vote1_ENABLED(p, v, r)
    /\  (ENABLED Vote2(p, v, r)) = Vote2_ENABLED(p, v, r)
    /\  (ENABLED Vote3(p, v, r)) = Vote3_ENABLED(p, v, r)
    /\  (ENABLED Vote4(p, v, r)) = Vote4_ENABLED(p, v, r)
    /\  (ENABLED StartRound(p, r)) = StartRound_ENABLED(p, r)

Liveness ==
    /\  goodRound
    /\  \A p \in P \ Byz, v \in V, r \in Round :
        /\ \neg Vote1_ENABLED(p, v, r)
        /\ \neg Vote2_ENABLED(p, v, r)
        /\ \neg Vote3_ENABLED(p, v, r)
        /\ \neg Vote4_ENABLED(p, v, r)
        /\ \neg StartRound_ENABLED(p, r)
    =>  decided # {}

\* Simple properties

VotedFor(p, r, v) ==  [round |-> r, phase |-> 4, value |-> v] \in votes[p]

NoFutureVote == \A p \in P \ Byz : \A vt \in votes[p] : vt.round <= round[p]

OneValuePerPhasePerRound == \A p \in P \ Byz : \A vt \in votes[p] :
    \A vt2 \in votes[p] : vt2.round = vt.round /\ vt2.phase = vt.phase => vt2.value = vt.value

VoteHasQuorumInPreviousPhase == \A p \in P \ Byz : \A vt \in votes[p] : vt.phase > 1 =>
    \E Q \in Quorum : \A q \in Q \ Byz :
        [round |-> vt.round, phase |-> (vt.phase)-1, value |-> vt.value] \in votes[q]

Invariant1 ==
    /\  NoFutureVote
    /\  OneValuePerPhasePerRound
    /\  VoteHasQuorumInPreviousPhase
    /\  \E Q \in Quorum : Byz = P \ Q
Invariant1_ == TypeOK /\ Invariant1

\* Now the main invariant

DidNotVoteAt(p, r) == \A v \in V : \neg VotedFor(p, r, v)

CannotVoteAt(p, r) == round[p] > r /\ DidNotVoteAt(p, r)

NoneOtherChoosableAt(r, v) == \E Q \in Quorum :
    \A p \in Q \ Byz : VotedFor(p, r, v) \/ CannotVoteAt(p, r)

SafeAt(r, v) == \A c \in Round : 0 <= c /\ c < r => NoneOtherChoosableAt(c, v)

VotesSafe == \A p \in P \ Byz : \A vt \in votes[p] :
    SafeAt(vt.round, vt.value)
VotesSafe_ == TypeOK /\ Invariant1 /\ VotesSafe

\* The full inductive invariant:
Invariant ==
    /\  TypeOK
    /\  \E Q \in Quorum : Byz = P \ Q
    /\  NoFutureVote
    /\  OneValuePerPhasePerRound
    \* It's interesting that we don't need the fact that there's at most one value voted by well-behaved processes in phases > 1
    /\  VoteHasQuorumInPreviousPhase
    /\  VotesSafe
    /\  Safety
Invariant_ == Invariant

=============================================================================