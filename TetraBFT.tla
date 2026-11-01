--------------------- MODULE TetraBFT ---------------------

(*********************************************************************************)
(* This is a high-level specification of the TetraBFT consensus algorithm. There *)
(* is no network or messages at this level of abstraction, but we do model       *)
(* Byzantine failures.                                                           *)
(*********************************************************************************)

EXTENDS Integers

CONSTANTS
    V \* the set of values to decide on
,   P \* the set of processes (typically 3f+1 nodes)
,   Quorum \* the set of quorums (typically sets of 2f+1 nodes out of 3f+1)
,   Blocking \* the set of blocking sets (typically sets of f+1 nodes out of 3f+1)
,   FailProneSets \* the set of fail-prone sets
,   Round \* the set of rounds

ASSUME
    /\  \A F \in FailProneSets : \E Q \in Quorum : Q \subseteq P \ F
    /\  \A F1, F2, F3 \in FailProneSets : P \ (F1 \cup F2 \cup F3) # {}

\* Each round consists of 4 phases:
Phase == 1..4
\* A vote is cast in a phase of a round and for a value:
Vote == [round: Round, phase: Phase, value: V]

\* We now specify the behaviors of the algorithm:

VARIABLES
    Byz, \* Byz is the set of Byzantine processes, chosen arbitrarily at initialization
    votes,
    round,
    proposed, \* whether a proposal has been made in the good round
    proposal, \* the good-round proposal
    goodRound \* the round that lasts long enough
vars == <<round, votes, proposed, proposal, goodRound, Byz>>

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> -1]
    /\ Byz \in FailProneSets
    /\ proposed = FALSE
    /\ proposal = CHOOSE v \in V : TRUE
    /\ goodRound \in Round \cup {-1}

TypeOK ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Round \cup {-1}]
    /\ proposed \in BOOLEAN
    /\ proposal \in V
    /\ Byz \in SUBSET P
    /\ goodRound \in Round \cup {-1}

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
    \/ r= 0
    \/  /\ \A q \in Q : round[q] >= r \* every member of Q is in round at least r
        /\  \/ \A q \in Q : \A vt \in votes[q] : vt.round < r => vt.phase # phaseA
            \* members of Q never voted in phaseA before round r
            \/ \E r2 \in Round :
                /\ 0 <= r2 /\ r2 < r
                \* no member of Q voted in phaseA after r2 and before r, and
                \* all members of Q that voted in r2 voted for v:
                /\ \A q \in Q : \A vt \in votes[q] : vt.round < r /\ vt.phase = phaseA =>
                    /\  vt.round <= r2
                    /\  vt.round = r2 => vt.value = v
                /\ \* v must be safe at r2
                    \E S \in Blocking : \A q \in S : ClaimsSafeAt(v, r, r2, q, phaseB)

\* just a helper:
DoVote(p, v, r, phase) ==
    \* never voted before in this round and phase:
    /\ \A vt \in votes[p] : vt.round # r \/ vt.phase # phase
    \* cast the vote:
    /\ votes' = [votes EXCEPT ![p] = @ \union {[round |-> r, phase |-> phase, value |-> v]}]

\* Now the actions

StartRound(p, r) ==
    /\  p \notin Byz
    /\  goodRound > -1 => r <= goodRound \* a good round lasts "long enough", i.e. forever
    /\  round[p] < r
    /\  round' = [round EXCEPT ![p] = r]
    /\  UNCHANGED <<votes, proposed, proposal, goodRound, Byz>>

\* propose in the goodRound
Propose(v) ==
    /\  goodRound > -1
    /\  \neg proposed
    /\  \E Q \in Quorum : ShowsSafeAt(Q, v, goodRound, 3, 2)
    /\  proposed' = TRUE
    /\  proposal' = v
    /\  UNCHANGED <<votes, round, goodRound, Byz>>

Vote1(p, v, r) ==
    /\ p \notin Byz
    /\ r = round[p]
    /\ r = goodRound => proposed /\ v = proposal
    /\ \E Q \in Quorum : ShowsSafeAt(Q, v, r, 4, 1)
    /\ DoVote(p, v, r, 1)
    /\ UNCHANGED <<round, proposed, proposal, goodRound, Byz>>

\* whether v has been voted for by a quorum in phase `phase' of round `r':
Accepted(p, v, r, phase) == \E Q \in Quorum :
    \A q \in Q : [round |-> r, phase |-> phase, value |-> v] \in votes[q]

Vote2(p, v, r) ==
    /\ p \notin Byz
    /\ round[p] <= r
    /\ Accepted(p, v, r, 1)
    /\ DoVote(p, v, r, 2)
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<proposed, proposal, goodRound, Byz>>

Vote3(p, v, r) ==
    /\ p \notin Byz
    /\ round[p] <= r
    /\ Accepted(p, v, r, 2)
    /\ DoVote(p, v, r, 3)
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<proposed, proposal, goodRound, Byz>>

Vote4(p, v, r) ==
    /\ p \notin Byz
    /\ round[p] <= r
    /\ Accepted(p, v, r, 3)
    /\ DoVote(p, v, r, 4)
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<proposed, proposal, goodRound, Byz>>

\* This models malicious behavior
ByzantineHavoc ==
    /\  \E p \in Byz :
            /\  \E new_votes \in SUBSET Vote : votes' = [votes EXCEPT ![p] = new_votes]
            /\  \E new_round \in Round : round' = [round EXCEPT ![p] = new_round]
    /\  UNCHANGED <<proposed, proposal, goodRound, Byz>>

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

Consistency == \A v1,v2 \in decided : v1 = v2

\* Candidate safety invariant; no TLAPS proof has been supplied yet.

VotedFor(p, r, v) ==  [round |-> r, phase |-> 4, value |-> v] \in votes[p]

NoFutureVote == \A p \in P \ Byz : \A vt \in votes[p] : vt.round <= round[p]

OneValuePerPhasePerRound == \A p \in P \ Byz : \A vt \in votes[p] :
    \A vt2 \in votes[p] : vt2.round = vt.round /\ vt2.phase = vt.phase => vt2.value = vt.value

VoteHasQuorumInPreviousPhase == \A p \in P \ Byz : \A vt \in votes[p] : vt.phase > 1 =>
    \E Q \in Quorum : \A q \in Q \ Byz :
        [round |-> vt.round, phase |-> (vt.phase)-1, value |-> vt.value] \in votes[q]

DidNotVoteAt(p, r) == \A v \in V : \neg VotedFor(p, r, v)

CannotVoteAt(p, r) == round[p] > r /\ DidNotVoteAt(p, r)

NoneOtherChoosableAt(r, v) == \E Q \in Quorum :
    \A p \in Q \ Byz : VotedFor(p, r, v) \/ CannotVoteAt(p, r)

SafeAt(r, v) == \A c \in Round : 0 <= c /\ c < r => NoneOtherChoosableAt(c, v)

VotesSafe == \A p \in P \ Byz : \A vt \in votes[p] :
    SafeAt(vt.round, vt.value)

ConsistencyInvariant ==
    /\  TypeOK
    /\  Byz \in FailProneSets
    /\  NoFutureVote
    /\  OneValuePerPhasePerRound
    /\  VoteHasQuorumInPreviousPhase
    /\  VotesSafe

=============================================================================
