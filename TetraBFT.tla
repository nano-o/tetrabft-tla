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
,   FailProneSets \* the set of fail-prone sets
,   Round \* the set of rounds
,   Byz \* the set of Byzantine processes

ASSUME
    /\  \A F \in FailProneSets : \E Q \in Quorum : Q \subseteq P \ F
    /\  \A F1, F2, F3 \in FailProneSets : P \ (F1 \cup F2 \cup F3) # {}

\* Each round consists of 4 phases:
Phase == 1..4
\* A vote is cast in a phase of a round and for a value:
\* @typeAlias: voteType = {round : Int, value : V, phase : Int};
Vote == [round: Round, phase: Phase, value: V]

NotAVote == [round |-> -1, phase |-> 1, value |-> CHOOSE v \in V : TRUE]

\* Whether vote v is maximal in S
\* @type: ($voteType, Set($voteType)) => Bool;
MaximalVote(vt, S) ==
    /\ vt \in S
    /\ \A vt2 \in S : vt2.round <= vt.round

\* A maximal element in the set S, if such exists, and otherwise the default value provided:
MaxVote(S, default) ==
    IF \E e \in S : MaximalVote(e, S)
    THEN CHOOSE e \in S : MaximalVote(e, S)
    ELSE default

\* We now specify the behaviors of the algorithm:

VARIABLES 
    \* Byz, \* Byz is the set of Byzantine processes
    votes,
    round,
    proposed, \* whether a proposal has been made in the good round
    proposal, \* the good-round proposal
    goodRound \* the round that lasts long enough
vars == <<round, votes, proposed, proposal, goodRound>>

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> -1]
    \* /\ Byz \in FailProneSets
    /\ proposed = FALSE
    /\ proposal = CHOOSE v \in V : TRUE
    \* TODO: allow -1 to not have a good round
    /\ goodRound \in Round \* \cup {-1} \* we "guess" the good round

TypeOK ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Round \cup {-1}]
    /\ proposed \in BOOLEAN
    /\ proposal \in V
    \* /\ Byz \in SUBSET P
    /\ goodRound \in Round \cup {-1}
TypeOK_ == TypeOK

decided == {v \in V : \E Q \in Quorum, r \in Round : \A p \in Q \ Byz :
    [round |-> r, phase |-> 4, value |-> v] \in votes[p] }

\* `v' is safe in round `r2' according to the votes of process `p' in phase `phase' before round r:
ClaimsSafeAt(v, r, r2, p, phase) ==
    \/ r2 = 0
    \/ \E vt1 \in votes[p] :
        /\  vt1.round < r /\ r2 <= vt1.round /\ vt1.phase = phase
        /\  \/ vt1.value = v
            \/ \E vt2 \in votes[p] :
                /\ r2 <= vt2.round /\ vt2.round < vt1.round
                /\ vt2.phase = phase /\ vt2.value # vt1.value

\* Whether value v is safe to vote for/propose in round r by process p
\* In case of a vote, we'll use phaseA=4 and phaseB=1
\* In case of a proposal, we'll use phaseA=3 and phaseB=2
ShowsSafeAt(Q, v, r, phaseA, phaseB) ==
    \/ r = 0
    \/  /\ \A q \in Q : round[q] >= r \* every member of Q is in round at least r
        /\  \/ \A q \in Q : \A vt \in votes[q] : vt.round < r => vt.phase # phaseA \* members of Q never voted in phaseA before round r
            \/ \E r2 \in Round :
                /\ 0 <= r2 /\ r2 < r
                \* no member of Q voted in phaseA after r2 and before r, and
                \* all members of Q that voted in r2 voted for v:
                /\ \A q \in Q : \A vt \in votes[q] : vt.round < r =>
                    /\  vt.phase = phaseA => vt.round <= r2
                    /\  vt.phase = phaseA /\ vt.round = r2 => vt.value = v
                /\ \* v must be safe at r2
                    \E S \in Blocking : \A q \in S : ClaimsSafeAt(v, r, r2, q, phaseB)

\* just a helper:
DoVote(p, v, r, phase) ==
    \* never voted before in this round and phase:
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # phase
    \* cast the vote:
    /\ votes' = [votes EXCEPT ![p] = @ \union {[round |-> r, phase |-> phase, value |-> v]}]

StartRound(p, r) ==
    /\  p \notin Byz
    /\  goodRound > -1 => r <= goodRound \* a good round lasts "long enough", i.e. forever
    /\  round[p] < r
    /\  round' = [round EXCEPT ![p] = r]
    /\  UNCHANGED <<votes, proposed, proposal, goodRound>>

Propose(v) ==
    /\  goodRound > -1
    /\  \neg proposed
    /\  \E Q \in Quorum : ShowsSafeAt(Q, v, goodRound, 3, 2)
    /\  proposed' = TRUE
    /\  proposal' = v
    /\  UNCHANGED <<votes, round, goodRound>>

Vote1(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ r = goodRound => proposed /\ v = proposal
    /\ \E Q \in Quorum : ShowsSafeAt(Q, v, r, 4, 1)
    /\ DoVote(p, v, r, 1)
    /\ UNCHANGED <<round, proposed, proposal, goodRound>>

\* whether v has been voted for by a quorum in phase `phase' of round `r':
Accepted(p, v, r, phase) == \E Q \in Quorum :
    \A q \in Q : [round |-> r, phase |-> phase, value |-> v] \in votes[q]

Vote2(p, v, r) ==
    /\ p \notin Byz
    /\ round[p] <= r
    /\ Accepted(p, v, r, 1)
    /\ DoVote(p, v, r, 2)
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<proposed, proposal, goodRound>>

Vote3(p, v, r) ==
    /\ p \notin Byz
    /\ round[p] <= r
    /\ Accepted(p, v, r, 2)
    /\ DoVote(p, v, r, 3)
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<proposed, proposal, goodRound>>

Vote4(p, v, r) ==
    /\ p \notin Byz
    /\ round[p] <= r
    /\ Accepted(p, v, r, 3)
    /\ DoVote(p, v, r, 4)
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<proposed, proposal, goodRound>>

\* This models malicious behavior
\* ByzantineHavoc ==
\*     \E new_votes \in [Byz -> SUBSET Vote] : \E new_round \in [Byz -> Round] :
\*     /\  votes' = [p \in P |-> IF p \in Byz THEN new_votes[p] ELSE votes[p]]
\*     /\  round' = [p \in P |-> IF p \in Byz THEN new_round[p] ELSE round[p]]
\*     /\  UNCHANGED <<Byz, proposal, goodRound>>
ByzantineHavoc ==
    /\  \E p \in Byz :
            /\  \E new_votes \in SUBSET Vote : votes' = [votes EXCEPT ![p] = new_votes]
            /\  \E new_round \in Round : round' = [round EXCEPT ![p] = new_round]
    /\  UNCHANGED <<proposed, proposal, goodRound>>

Next ==
    \E p \in P, v \in V, r \in Round :
        \/ ByzantineHavoc
        \/ Vote1(p, v, r)
        \/ Vote2(p, v, r)
        \/ Vote3(p, v, r)
        \/ Vote4(p, v, r)
        \/ StartRound(p, r)
        \/ Propose(v)

Spec == Init /\ [][Next]_vars

Safety == \A v1,v2 \in decided : v1 = v2

\* Manual encoding of ENABLED for Apalache:

Propose_ENABLED(v) ==
    /\  goodRound > -1
    /\  \neg proposed
    /\  \E Q \in Quorum : ShowsSafeAt(Q, v, goodRound, 3, 2)

Vote1_ENABLED(p, v, r) ==
    /\ p \notin Byz
    /\ r = goodRound => proposed /\ v = proposal
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

StartRound_ENABLED(p, r) == 
    /\  p \notin Byz
    /\  goodRound > -1 => r <= goodRound
    /\  round[p] < r

\* For use with TLC to catch errors in the ENABLED predicates:
ENABLED_OK == \A p \in P, v \in V, r \in Round :
    /\  (ENABLED Propose(v)) = Propose_ENABLED(v)
    /\  (ENABLED Vote1(p, v, r)) = Vote1_ENABLED(p, v, r)
    /\  (ENABLED Vote2(p, v, r)) = Vote2_ENABLED(p, v, r)
    /\  (ENABLED Vote3(p, v, r)) = Vote3_ENABLED(p, v, r)
    /\  (ENABLED Vote4(p, v, r)) = Vote4_ENABLED(p, v, r)
    /\  (ENABLED StartRound(p, r)) = StartRound_ENABLED(p, r)

Liveness ==
    /\  goodRound > -1
    /\  \A p \in P \ Byz, v \in V, r \in Round :
        /\ \neg Propose_ENABLED(v)
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

Invariant ==
    /\  VotesSafe
    \* /\  Safety
Invariant_ == TypeOK /\ Invariant1 /\ Invariant

\* Now liveness!

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

LivenessInvariant1 == goodRound > -1 /\ proposed =>
    \/  goodRound = 0
    \/  \E Q \in Quorum :
        /\ \A p \in Q \ Byz : round[p] = goodRound
        /\  \* no member voted in phase 3 before round goodRound
            \/ \A p \in Q \ Byz : \A vt \in votes[p] : \neg (vt.phase = 3 /\ vt.round < goodRound)
            \* highest ...
            \/ \E r \in Round :
                /\ 0 <= r /\ r < goodRound
                /\ \A p \in Q \ Byz : \A vt \in votes[p] : vt.phase = 3 /\ vt.round < goodRound =>
                    /\  vt.round <= r
                    /\  vt.round = r => vt.value = proposal
                /\ \E p \in P \ Byz : ClaimsSafeAt(proposal, goodRound, r, p, 2)
LivenessInvariant1_ == 
    /\  TypeOK
    /\ \A p \in P \ Byz :
        /\  round[p] <= goodRound
        /\  \A vt \in votes[p] : vt.round <= goodRound
    /\  \E Q \in Quorum : Byz = P \ Q
    /\  OneValuePerPhasePerRound
    /\  VoteHasQuorumInPreviousPhase
    /\  LivenessInvariant1

LivenessInvariant2 ==
    goodRound > -1 =>
        /\  \A p \in P \ Byz : \neg StartRound_ENABLED(p, goodRound) => round[p] = goodRound
        /\  (\A v \in V : \neg Propose_ENABLED(v)) /\ (\A p \in P \ Byz : round[p] = goodRound) => proposed
LivenessInvariant2_ ==
    /\ goodRound = 2
    /\ TypeOK
    /\ \E Q \in Quorum : Byz = P \ Q
    /\  OneValuePerPhasePerRound
    /\  VoteHasQuorumInPreviousPhase
    /\  \A p \in P \ Byz : \A vt \in votes[p] : \A r \in Round :
             vt.round < r /\ vt.round = goodRound /\ vt.phase = 3 => \E Q \in Quorum :
                \A q \in Q \ Byz : ClaimsSafeAt(vt.value, r, goodRound, q, 2)
    /\  \A p \in P \ Byz : \A vt \in votes[p] : vt.round = goodRound => proposed
    /\  goodRound > -1 =>
        /\ \A p \in P \ Byz :
            /\  round[p] <= goodRound
            /\  \A vt \in votes[p] : vt.round <= goodRound
        /\  \A p \in P \ Byz : \neg StartRound_ENABLED(p, goodRound) => round[p] = goodRound
        /\  (\A v \in V : \neg Propose_ENABLED(v)) /\ (\A p \in P \ Byz : round[p] = goodRound) => proposed

=============================================================================