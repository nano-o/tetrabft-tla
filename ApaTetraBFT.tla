------------------ MODULE ApaTetraBFT ------------------

EXTENDS Integers

\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
V == {"V1_OF_V", "V2_OF_V"}
\* Quorums are any 3 out of 4:
\* FailProneSets == {{"P1_OF_P"}, {"P2_OF_P"}, {"P3_OF_P"}}
\* Quorum == {{"P1_OF_P", "P2_OF_P", "P3_OF_P"}, {"P1_OF_P", "P2_OF_P", "P4_OF_P"}, {"P1_OF_P", "P3_OF_P", "P4_OF_P"}, {"P2_OF_P", "P3_OF_P", "P4_OF_P"}}
\* Blocking sets are any 2 out of 4:
\* Blocking == {{"P1_OF_P","P2_OF_P"}, {"P1_OF_P","P3_OF_P"}, {"P1_OF_P","P4_OF_P"}, {"P2_OF_P","P3_OF_P"}, {"P2_OF_P","P4_OF_P"}, {"P3_OF_P","P4_OF_P"}}
\* With 3 processes, let's say only p1 and p3 may be Byzantine:
Quorum == {{"P1_OF_P", "P2_OF_P"}, {"P2_OF_P", "P3_OF_P"}}
Blocking == {{"P2_OF_P"}}
FailProneSets == {{"P1_OF_P"}, {"P3_OF_P"}}
Byz == {"P1_OF_P"}

MaxRound == 2
Round == 0..MaxRound

VARIABLES
    \* @type: P -> Int;
    round,
    \* @type: P -> Set({round : Int, value : V, phase : Int});
    votes,
    \* @type: Int;
    goodRound,
    \* @type: Bool;
    proposed,
    \* @type: V;
    proposal
    \* type: Set(P);
    \* Byz,

INSTANCE TetraBFT

===========================================================