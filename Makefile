APA_VERSION=0.45.2
APA_RELEASE_URL=https://github.com/apalache-mc/apalache/releases/download/v${APA_VERSION}/apalache-${APA_VERSION}.tgz
APA=apalache-${APA_VERSION}
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

tetrabft-safety: $(APA) TetraBFT.tla ApaTetraBFT.tla
	APA=$(APA) ./check.sh -inductive ConsistencyInvariant TetraBFT
	APA=$(APA) ./check.sh -implication ConsistencyInvariant Consistency TetraBFT

tetrabft-liveness: $(APA) TetraBFT.tla ApaTetraBFT.tla ${TLC_JAR} TLCTetraBFT.cfg TLCTetraBFT.tla
	# java -XX:+UseParallelGC -jar ${TLC_JAR} -config TLCTetraBFT.cfg -workers 4 -deadlock TLCTetraBFT.tla
	APA=$(APA) ./check.sh -inductive LivenessAuxiliaryInvariants TetraBFT
	APA=$(APA) ./check.sh -inductive ProposalAlwaysAcceptableInvariant TetraBFT
	APA=$(APA) ./check.sh -relative LivenessStep0_ LivenessStep0 TetraBFT
	APA=$(APA) ./check.sh -relative LivenessStep1_ LivenessStep1 TetraBFT
	APA=$(APA) ./check.sh -relative LivenessStep2_ LivenessStep2 TetraBFT
	# APA=$(APA) ./check.sh -implication LivenessInvariants Liveness TetraBFT

paxos-safety: $(APA) Paxos.tla ApaPaxos.tla
	APA=$(APA) ./check.sh -inductive ConsistencyInvariant Paxos
	APA=$(APA) ./check.sh -implication ConsistencyInvariant Consistency Paxos

paxos-liveness: $(APA) Paxos.tla ApaPaxos.tla ${TLC_JAR} TLCPaxos.cfg TLCPaxos.tla
	java -XX:+UseParallelGC -jar ${TLC_JAR} -config TLCPaxos.cfg -workers 4 TLCPaxos.tla
	APA=$(APA) ./check.sh -inductive LivenessInvariant Paxos
	APA=$(APA) ./check.sh -implication LivenessInvariant Liveness Paxos
	APA=$(APA) ./check.sh -inductive SelfDisabling PaxosEnabledness

.PHONY: safety
