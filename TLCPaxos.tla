--------------------------- MODULE TLCPaxos -------------------------------

EXTENDS Paxos, TLC

Symm == Permutations(Acceptor) \cup Permutations(Value)

===================================================================================