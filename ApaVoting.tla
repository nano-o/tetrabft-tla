------------------ MODULE ApaVoting ------------------

EXTENDS Integers

P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}
V == {"V1_OF_V", "V2_OF_V"}
\* Quorums are any 3 out of 4:
Quorum == {{"P1_OF_P", "P2_OF_P", "P3_OF_P"}, {"P1_OF_P", "P2_OF_P", "P4_OF_P"}, {"P1_OF_P", "P3_OF_P", "P4_OF_P"}, {"P2_OF_P", "P3_OF_P", "P4_OF_P"}}
\* Blocking sets are any 2 out of 4:
Blocking == {{"P1_OF_P","P2_OF_P"}, {"P1_OF_P","P3_OF_P"}, {"P1_OF_P","P4_OF_P"}, {"P2_OF_P","P3_OF_P"}, {"P2_OF_P","P4_OF_P"}, {"P3_OF_P","P4_OF_P"}}
\* Use those ones to speed up model-checking:
(* Quorum == {{"P1_OF_P", "P2_OF_P", "P3_OF_P"}, {"P1_OF_P", "P2_OF_P", "P4_OF_P"}} *)
(* Blocking == {{"P1_OF_P","P2_OF_P"}, {"P1_OF_P","P4_OF_P"}} *)
B == {"P1_OF_P"}
MaxRound == 3
Round == 0..MaxRound

VARIABLES
    \* @type: P -> Int;
    round,
    \* @type: P -> Set({round : Int, value : V, phase : Int});
    votes

INSTANCE Voting

===========================================================
