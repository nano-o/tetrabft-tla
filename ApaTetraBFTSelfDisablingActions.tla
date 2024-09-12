--------------------------- MODULE ApaTetraBFTSelfDisablingActions -------------------------------

EXTENDS Integers

MaxRound == 1
Round == 0..MaxRound

V == {"V1_OF_V", "V2_OF_V"}
\* V == {"V1_OF_V", "V2_OF_V", "V3_OF_V"}
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
\* Only p1 or p3 may be Byzantine:
FailProneSets == {{"P1_OF_P"}, {"P3_OF_P"}}
Quorum == {{"P1_OF_P", "P2_OF_P"}, {"P2_OF_P", "P3_OF_P"}}
Blocking == {{"P2_OF_P"}}

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
    Byz,
    \* @type: <<P, Int>> -> Bool;
    startRoundTaken,
    \* @type: V -> Bool;
    proposeTaken,
    \* @type: <<P, V, Int>> -> Bool;
    vote1Taken,
    \* @type: <<P, V, Int>> -> Bool;
    vote2Taken,
    \* @type: <<P, V, Int>> -> Bool;
    vote3Taken,
    \* @type: <<P, V, Int>> -> Bool;
    vote4Taken

INSTANCE TetraBFTSelfDisablingActions

===================================================================================

