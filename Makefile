APA_RELEASE_URL=https://github.com/informalsystems/apalache/releases/download/v0.44.11/apalache-0.44.11.tgz
APA=apalache-0.44.11
APA_ARCHIVE=$(APA).tgz

all: check

# Download
$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

# Don't redownload stuff every time
.PRECIOUS: $(APA)

safety: $(APA) TetraBFT.tla ApaTetraBFT.tla
	APA=$(APA) ./check.sh -inductive Invariant TetraBFT

paxos: $(APA) Paxos.tla ApaPaxos.tla
	APA=$(APA) ./check.sh -inductive Invariant Paxos
	APA=$(APA) ./check.sh -implication Invariant Consistency Paxos
	APA=$(APA) ./check.sh -inductive LivenessInvariant Paxos
	APA=$(APA) ./check.sh -implication LivenessInvariant Liveness Paxos

.PHONY: safety
