--------------------------- MODULE TLCAbstractPaxos -------------------------------

EXTENDS AbstractPaxos, TLC

Symm == Permutations(Acceptor) \cup Permutations(Value)

===================================================================================