------------------ MODULE ApaTetraBFT ------------------

EXTENDS Integers

MaxRound == 1
Round == 0..MaxRound

\* A configuration with 3 processes
\* 2 minute with MaxRound == 1 and 2 values
\* 7 minutes with MaxRound == 2 and 2 values

V == {"V1_OF_V", "V2_OF_V"}
\* V == {"V1_OF_V", "V2_OF_V", "V3_OF_V"}
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
\* Only p1 or p3 may be Byzantine:
FailProneSets == {{"P1_OF_P"}, {"P3_OF_P"}}
Quorum == {{"P1_OF_P", "P2_OF_P"}, {"P2_OF_P", "P3_OF_P"}}
Blocking == {{"P2_OF_P"}}

\* A configuration with 4 processes
\* OOM with MaxRound == 2 and 2 values

\* V == {"V1_OF_V", "V2_OF_V"}
\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}
\* Quorum == {{"P1_OF_P", "P2_OF_P", "P3_OF_P"}, {"P1_OF_P", "P2_OF_P", "P4_OF_P"}, {"P1_OF_P", "P3_OF_P", "P4_OF_P"}, {"P2_OF_P", "P3_OF_P", "P4_OF_P"}}
\* FailProneSets == {{"P1_OF_P"}, {"P2_OF_P"}, {"P3_OF_P"}, {"P4_OF_P"}}
\* Blocking == {{"P1_OF_P","P2_OF_P"}, {"P1_OF_P","P3_OF_P"}, {"P1_OF_P","P4_OF_P"}, {"P2_OF_P","P3_OF_P"}, {"P2_OF_P","P4_OF_P"}, {"P3_OF_P","P4_OF_P"}}

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
    proposal,
    \* @type: Set(P);
    Byz

INSTANCE TetraBFT

===========================================================
