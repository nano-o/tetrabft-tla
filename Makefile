APA_RELEASE_URL=https://github.com/informalsystems/apalache/releases/download/v0.44.11/apalache-0.44.11.tgz
APA=apalache-0.44.11
APA_ARCHIVE=$(APA).tgz
TLC_JAR=tla2tools.jar
TLC_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.7.3/tla2tools.jar

all: safety

$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

# Download the TLC_JAR if it does not exist
$(TLC_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TLC_JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(APA) $(TLC_JAR)

safety: $(APA) TetraBFT.tla ApaTetraBFT.tla
	APA=$(APA) ./check.sh -inductive Invariant1 TetraBFT
	APA=$(APA) ./check.sh -inductive SafetyInvariant TetraBFT

liveness: $(APA) TetraBFT.tla ApaTetraBFT.tla
	# java -XX:+UseParallelGC -jar tla2tools.jar -config TLCTetraBFT.cfg -workers 4 -deadlock TLCTetraBFT.tla
	# APA=$(APA) ./check.sh -inductive ProposalPropertyInvariant TetraBFT
	APA=$(APA) ./check.sh -implication Liveness_ante Liveness TetraBFT

paxos: $(APA) Paxos.tla ApaPaxos.tla ${TLC_JAR}
	APA=$(APA) ./check.sh -inductive ConsistencyInvariant Paxos
	APA=$(APA) ./check.sh -implication ConsistencyInvariant Consistency Paxos
	java -XX:+UseParallelGC -jar tla2tools.jar -config TLCPaxos.cfg -workers 4 TLCPaxos.tla
	APA=$(APA) ./check.sh -inductive LivenessInvariant Paxos
	APA=$(APA) ./check.sh -implication LivenessInvariant Liveness Paxos

.PHONY: safety
