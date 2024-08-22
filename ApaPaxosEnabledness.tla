--------------------------- MODULE ApaPaxosEnabledness -------------------------------

EXTENDS Integers

Value == {"V1_OF_VALUE","V2_OF_VALUE","V3_OF_VALUE"}
\* Value == {"V1_OF_VALUE","V2_OF_VALUE"}
\* Value == {"V1_OF_VALUE"}
\* Acceptor == {"A1_OF_ACCEPTOR"}
Acceptor == {"A1_OF_ACCEPTOR","A2_OF_ACCEPTOR","A3_OF_ACCEPTOR"}
\* The quorums are the sets of 2 acceptors:
Quorum == {
    {"A1_OF_ACCEPTOR","A2_OF_ACCEPTOR"},
    {"A1_OF_ACCEPTOR","A3_OF_ACCEPTOR"},
    {"A2_OF_ACCEPTOR","A3_OF_ACCEPTOR"}}
\* Quorum == {{"A1_OF_ACCEPTOR"}}

MaxBal == 2
Ballot == 0..MaxBal \* NOTE: we have to make this a finite set for `^Apalache^'

Leader(b) ==
    CASE b = 0 -> "A1_OF_ACCEPTOR"
    []   b = 1 -> "A2_OF_ACCEPTOR"
    []   b = 2 -> "A3_OF_ACCEPTOR"
    
VARIABLES
    \* @type: ACCEPTOR -> Set(<<Int,VALUE>>);
    votes,
    \* @type: ACCEPTOR -> Int;
    currBal,
    \* @type: Set(<<Int,VALUE>>);
    proposals,
    \* @type: Set(ACCEPTOR);
    crashed,
    \* @type: Int;
    goodBallot,
    \* @type: <<ACCEPTOR, Int, VALUE>> -> Bool;
    voteForTaken,
    \* @type: <<Int, VALUE>> -> Bool;
    proposeTaken,
    \* @type: <<ACCEPTOR, Int>> -> Bool;
    increaseCurrBalTaken

INSTANCE PaxosEnabledness

===================================================================================