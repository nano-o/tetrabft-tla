APA_VERSION=0.45.2
APA_RELEASE_URL=https://github.com/apalache-mc/apalache/releases/download/v${APA_VERSION}/apalache-${APA_VERSION}.tgz
APA=apalache-${APA_VERSION}
APA_ARCHIVE=$(APA).tgz
TLC_JAR=tla2tools.jar
TLC_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

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
	java -XX:+UseParallelGC -jar ${TLC_JAR} -config TLCTetraBFT.cfg -workers 4 -deadlock TLCTetraBFT.tla
	APA=$(APA) ./check.sh -inductive LivenessInvariants TetraBFT
	APA=$(APA) ./check.sh -implication LivenessInvariants Liveness TetraBFT
	APA=$(APA) ./check.sh -inductive SelfDisabling TetraBFTSelfDisablingActions

paxos-safety: $(APA) Paxos.tla ApaPaxos.tla
	APA=$(APA) ./check.sh -inductive ConsistencyInvariant Paxos
	APA=$(APA) ./check.sh -implication ConsistencyInvariant Consistency Paxos

paxos-liveness: $(APA) Paxos.tla ApaPaxos.tla ${TLC_JAR} TLCPaxos.cfg TLCPaxos.tla
	java -XX:+UseParallelGC -jar ${TLC_JAR} -config TLCPaxos.cfg -workers 4 TLCPaxos.tla
	java -XX:+UseParallelGC -jar ${TLC_JAR} -config TLCPaxosLiveness.cfg -workers 4 TLCPaxos.tla
	APA=$(APA) ./check.sh -inductive LivenessInvariant Paxos
	APA=$(APA) ./check.sh -implication LivenessInvariant Liveness Paxos
	APA=$(APA) ./check.sh -inductive SelfDisabling PaxosSelfDisablingActions

.PHONY: tetrabft-safety tetrabft-liveness paxos-safety paxos-liveness
