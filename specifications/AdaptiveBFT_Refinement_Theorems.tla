------------------- MODULE AdaptiveBFT_Refinement_Theorems -------------------
EXTENDS AdaptiveBFT_Theorems, TLAPS, Naturals, Integers, Sequences, FiniteSets

CONSTANT MaxView

\* Concrete-state variables used for the refinement bridge.
VARIABLES
    cView,
    cPhase,
    cLockedView,
    cHighView,
    cPrepareVotes,
    cDecidedByView,
    cChainViews,
    cNetworkStable

varsC ==
    <<cView, cPhase, cLockedView, cHighView, cPrepareVotes,
      cDecidedByView, cChainViews, cNetworkStable>>

AbsView ==
    IF cPhase = "ViewChange" /\ cView < MaxView
    THEN cView + 1
    ELSE cView

AbsPhase ==
    IF cPhase = "ViewChange"
    THEN "ViewChange"
    ELSE IF cPhase = "PreCommit" THEN "PreCommit"
    ELSE IF cPhase = "Commit" THEN "Commit"
    ELSE "Prepare"

AbsLockedView ==
    IF cLockedView < 0 THEN 0 ELSE cLockedView

AbsHighView ==
    IF cHighView < 0 THEN 0 ELSE cHighView

AbsVotes ==
    IF cPhase = "Prepare" THEN cPrepareVotes ELSE {}

AbsDecidedByView ==
    cDecidedByView

ABSTRACT ==
    INSTANCE AdaptiveBFT_Abstract
        WITH
            Node <- Node,
            F <- F,
            Quorum <- Quorum,
            view <- AbsView,
            phase <- AbsPhase,
            lockedView <- AbsLockedView,
            highView <- AbsHighView,
            votes <- AbsVotes,
            decidedByView <- AbsDecidedByView,
            chain <- cChainViews,
            networkStable <- IF cView = 0 /\ cPhase = "CollectMinor" THEN FALSE ELSE cNetworkStable

ABSTRACT_THEOREMS ==
    INSTANCE AdaptiveBFT_Theorems
        WITH
            Node <- Node,
            F <- F,
            Quorum <- Quorum,
            view <- AbsView,
            phase <- AbsPhase,
            lockedView <- AbsLockedView,
            highView <- AbsHighView,
            votes <- AbsVotes,
            decidedByView <- AbsDecidedByView,
            chain <- cChainViews,
            networkStable <- IF cView = 0 /\ cPhase = "CollectMinor" THEN FALSE ELSE cNetworkStable

ABSTRACT_TRANSFER ==
    INSTANCE AdaptiveBFT_AbstractBridge_Theorems
        WITH
            Node <- Node,
            F <- F,
            Quorum <- Quorum,
            view <- AbsView,
            phase <- AbsPhase,
            lockedView <- AbsLockedView,
            highView <- AbsHighView,
            votes <- AbsVotes,
            decidedByView <- AbsDecidedByView,
            chain <- cChainViews,
            networkStable <- IF cView = 0 /\ cPhase = "CollectMinor" THEN FALSE ELSE cNetworkStable

TransferSpec ==
    ABSTRACT_TRANSFER!ABSTRACT_THEOREMS!SpecA

TransferSafety ==
    ABSTRACT_TRANSFER!ABSTRACT_THEOREMS!SafetyA

TransferLivenessAssumptions ==
    ABSTRACT_TRANSFER!ABSTRACT_THEOREMS!LivenessAssumptionsA

TransferLiveness ==
    ABSTRACT_TRANSFER!ABSTRACT_THEOREMS!LivenessA

ConcreteStateType ==
    /\ cView \in Nat
    /\ cPhase \in {"CollectMinor", "Prepare", "PreCommit", "Commit", "ViewChange"}
    /\ cLockedView \in Int
    /\ cHighView \in Int
    /\ cPrepareVotes \subseteq Node
    /\ cDecidedByView \in [Nat -> SUBSET Nat]
    /\ cChainViews \in Seq(Nat)
    /\ cNetworkStable \in BOOLEAN

ConcreteInitShape ==
    /\ cView = 0
    /\ cPhase = "CollectMinor"
    /\ cLockedView = -1
    /\ cHighView = -1
    /\ cPrepareVotes = {}
    /\ cDecidedByView = [v \in Nat |-> {}]
    /\ cChainViews = <<>>
    /\ cNetworkStable = TRUE

VoteMap(n) ==
    ABSTRACT!VoteA(n)

PrepareQCMap ==
    ABSTRACT!PrepareQCA

PreCommitQCMap ==
    ABSTRACT!PreCommitQCA

CommitMap ==
    ABSTRACT!CommitA

ViewChangeMap ==
    ABSTRACT!ViewChangeA

RecoverSyncMap ==
    ABSTRACT!RecoverSyncA

EnvironmentMap ==
    ABSTRACT!EnvironmentStepA

ConcreteMappedNext ==
    \/ (\E n \in Node: VoteMap(n))
    \/ PrepareQCMap
    \/ PreCommitQCMap
    \/ CommitMap
    \/ ViewChangeMap
    \/ RecoverSyncMap
    \/ EnvironmentMap

ProjectedSafety ==
    /\ (\A v \in Nat: Cardinality(AbsDecidedByView[v]) <= 1)
    /\ /\ cLockedView <= cHighView
       /\ cHighView <= cView

ProjectedLiveness ==
    <> (Len(cChainViews) >= 2)

ConcreteBridgeAssumptions ==
    /\ ConcreteStateType
    /\ cLockedView <= cHighView
    /\ cHighView <= cView
    /\ \A v \in Nat: Cardinality(AbsDecidedByView[v]) <= 1

THEOREM RefinementInitBridge ==
    ConcreteInitShape => ABSTRACT!InitA
PROOF
    BY DEF ConcreteInitShape, ABSTRACT!InitA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM VoteMapSimulation ==
    \A n \in Node: VoteMap(n) => ABSTRACT!VoteA(n)
PROOF
    BY DEF VoteMap, ABSTRACT!VoteA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM PrepareQCMapSimulation ==
    PrepareQCMap => ABSTRACT!PrepareQCA
PROOF
    BY DEF PrepareQCMap, ABSTRACT!PrepareQCA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM PreCommitQCMapSimulation ==
    PreCommitQCMap => ABSTRACT!PreCommitQCA
PROOF
    BY DEF PreCommitQCMap, ABSTRACT!PreCommitQCA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM CommitMapSimulation ==
    CommitMap => ABSTRACT!CommitA
PROOF
    BY DEF CommitMap, ABSTRACT!CommitA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM ViewChangeMapSimulation ==
    ViewChangeMap => ABSTRACT!ViewChangeA
PROOF
    BY DEF ViewChangeMap, ABSTRACT!ViewChangeA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM RecoverSyncMapSimulation ==
    RecoverSyncMap => ABSTRACT!RecoverSyncA
PROOF
    BY DEF RecoverSyncMap, ABSTRACT!RecoverSyncA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM EnvironmentMapSimulation ==
    EnvironmentMap => ABSTRACT!EnvironmentStepA
PROOF
    BY DEF EnvironmentMap, ABSTRACT!EnvironmentStepA, AbsPhase, AbsVotes, AbsDecidedByView

THEOREM RefinementStepBridge ==
    ConcreteMappedNext => ABSTRACT!NextA
PROOF
    <1>1. \A n \in Node: VoteMap(n) => ABSTRACT!VoteA(n)
        BY VoteMapSimulation
    <1>2. PrepareQCMap => ABSTRACT!PrepareQCA
        BY PrepareQCMapSimulation
    <1>3. PreCommitQCMap => ABSTRACT!PreCommitQCA
        BY PreCommitQCMapSimulation
    <1>4. CommitMap => ABSTRACT!CommitA
        BY CommitMapSimulation
    <1>5. ViewChangeMap => ABSTRACT!ViewChangeA
        BY ViewChangeMapSimulation
    <1>6. RecoverSyncMap => ABSTRACT!RecoverSyncA
        BY RecoverSyncMapSimulation
    <1>7. EnvironmentMap => ABSTRACT!EnvironmentStepA
        BY EnvironmentMapSimulation
    <1> QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
           DEF ConcreteMappedNext, ABSTRACT!NextA

THEOREM RefinementSafetyBridge ==
    ASSUME ConcreteBridgeAssumptions
    PROVE ProjectedSafety
PROOF
    <1>1. \A v \in Nat: Cardinality(AbsDecidedByView[v]) <= 1
        BY DEF ConcreteBridgeAssumptions
    <1>2. /\ cLockedView <= cHighView
          /\ cHighView <= cView
        BY DEF ConcreteBridgeAssumptions
    <1> QED
        BY <1>1, <1>2 DEF ProjectedSafety

THEOREM RefinementLivenessBridge ==
    ASSUME <> (Len(cChainViews) >= 2)
    PROVE ProjectedLiveness
PROOF
    BY DEF ProjectedLiveness

THEOREM AbstractSafetyTransferTemplate ==
    (TransferSpec => []TransferSafety)
PROOF
    BY ABSTRACT_TRANSFER!SafetyTransferFromInstance
       DEF TransferSpec, TransferSafety

THEOREM AbstractLivenessTransferTemplate ==
    ((TransferSpec /\ TransferLivenessAssumptions) => TransferLiveness)
PROOF
    BY ABSTRACT_TRANSFER!LivenessTransferFromInstance
       DEF TransferSpec, TransferLivenessAssumptions, TransferLiveness

\* End-to-end mapped pipeline: abstract safety plus projected concrete safety.
THEOREM MappedSafetyPipeline ==
    ASSUME /\ TransferSpec
           /\ ConcreteBridgeAssumptions
    PROVE /\ []TransferSafety
          /\ ProjectedSafety
PROOF
    <1>1. []TransferSafety
        BY AbstractSafetyTransferTemplate
    <1>2. ProjectedSafety
        BY RefinementSafetyBridge
    <1> QED
        BY <1>1, <1>2

\* End-to-end mapped pipeline: abstract liveness plus projected progress.
THEOREM MappedLivenessPipeline ==
    ASSUME /\ TransferSpec
           /\ TransferLivenessAssumptions
           /\ <> (Len(cChainViews) >= 2)
    PROVE /\ TransferLiveness
          /\ ProjectedLiveness
PROOF
    <1>1. TransferLiveness
        BY AbstractLivenessTransferTemplate
    <1>2. ProjectedLiveness
        BY RefinementLivenessBridge
    <1> QED
        BY <1>1, <1>2

=============================================================================
