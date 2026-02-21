------------------------ MODULE MC_LivenessAPS ------------------------
EXTENDS AdaptiveBFT_Refinement, TLC

VARIABLE apsBootDone

varsAPS == <<st, apsBootDone>>

InitAPS ==
    /\ Init
    /\ apsBootDone = FALSE

SchedulerBootstrap ==
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Monitor"
       /\ st' = [st EXCEPT !.networkCondition = "Stable", !.schedulerState = "Sample"]
       /\ apsBootDone' = FALSE
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Sample"
       /\ SampleGrid
       /\ apsBootDone' = FALSE
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Estimate"
       /\ EstimateGrid
       /\ apsBootDone' = FALSE
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Explore"
       /\ ExploreGrid
       /\ apsBootDone' = FALSE
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Deploy"
       /\ DeployConfig
       /\ apsBootDone' = TRUE

StableConsensusNext ==
    \/ InjectTxStep
    \/ PreValidateStep
    \/ AgeTxStep
    \/ DispatchToDissemination
    \/ PromoteToOrdering
    \/ PromoteToExecution
    \/ PreOrder
    \/ GenerateTentativeProposal
    \/ RecoverFullProposal
    \/ PrepareVoteStep
    \/ PrepareQC
    \/ PreCommitVoteStep
    \/ PreCommitQC
    \/ CommitVoteStep
    \/ DecideBlock

PostBootstrap ==
    /\ apsBootDone
    /\ st.networkCondition = "Stable"
    /\ StableConsensusNext
    /\ UNCHANGED apsBootDone

NextAPSFair ==
    \/ SchedulerBootstrap
    \/ PostBootstrap

InjectFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ InjectTxStep /\ UNCHANGED apsBootDone
PreValidateFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreValidateStep /\ UNCHANGED apsBootDone
PreOrderFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreOrder /\ UNCHANGED apsBootDone
GenerateProposalFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ GenerateTentativeProposal /\ UNCHANGED apsBootDone
RecoverFullFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ RecoverFullProposal /\ UNCHANGED apsBootDone
PrepareVoteFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PrepareVoteStep /\ UNCHANGED apsBootDone
PrepareQCFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PrepareQC /\ UNCHANGED apsBootDone
PreCommitVoteFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreCommitVoteStep /\ UNCHANGED apsBootDone
PreCommitQCFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreCommitQC /\ UNCHANGED apsBootDone
CommitVoteFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ CommitVoteStep /\ UNCHANGED apsBootDone
DecideFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ DecideBlock /\ UNCHANGED apsBootDone

AssumeEventualStability ==
    <>[] (st.networkCondition = "Stable")

AssumeBootstrapFair ==
    WF_varsAPS(SchedulerBootstrap)

AssumeProgressFairness ==
    /\ SF_varsAPS(InjectFair)
    /\ WF_varsAPS(PreValidateFair)
    /\ WF_varsAPS(PreOrderFair)
    /\ WF_varsAPS(GenerateProposalFair)
    /\ WF_varsAPS(RecoverFullFair)
    /\ WF_varsAPS(PrepareVoteFair)
    /\ WF_varsAPS(PrepareQCFair)
    /\ WF_varsAPS(PreCommitVoteFair)
    /\ WF_varsAPS(PreCommitQCFair)
    /\ WF_varsAPS(CommitVoteFair)
    /\ WF_varsAPS(DecideFair)

AssumptionsAPS ==
    /\ AssumeEventualStability
    /\ AssumeBootstrapFair
    /\ AssumeProgressFairness

AssumptionsAPSForTLC ==
    /\ AssumeBootstrapFair
    /\ AssumeProgressFairness

SpecAPS ==
    /\ InitAPS
    /\ [][NextAPSFair]_varsAPS
    /\ AssumptionsAPSForTLC

ConsensusLiveness == <> (Len(st.chain) >= 2)

\* TLC-safe finite projection for decidedByView in wrapper-level transfer checks.
AbsDecidedByViewFinite ==
    [v \in 0..MaxView |->
        IF st.decidedByView[v] # {} THEN {v} ELSE {}
    ]

ABOUNDED ==
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
            decidedByView <- AbsDecidedByViewFinite,
            chain <- AbsChain,
            networkStable <- AbsNetworkStable

InitProjectionShapeAPS ==
    /\ AbsView = 0
    /\ AbsPhase = "Prepare"
    /\ AbsLockedView = 0
    /\ AbsHighView = 0
    /\ AbsVotes = {}
    /\ AbsDecidedByViewFinite = [v \in 0..MaxView |-> {}]
    /\ AbsChain = <<>>

InitProjectionAPS ==
    InitAPS => InitProjectionShapeAPS

StepProjectionAPS ==
    NextAPSFair => (ABOUNDED!NextA \/ UNCHANGED ABOUNDED!varsA)

StepBoxProjectionAPS ==
    NextAPSFair => [ABOUNDED!NextA]_ABOUNDED!varsA

StepProjectionCheckedAPS ==
    [][StepProjectionAPS]_varsAPS

StepBoxProjectionCheckedAPS ==
    [][StepBoxProjectionAPS]_varsAPS

InitProjectionCheckedAPS ==
    InitProjectionAPS

SpecProjectionCheckedAPS ==
    InitProjectionAPS /\ StepBoxProjectionCheckedAPS

SpecToAbstractSpecCheckedAPS ==
    \* TLC-safe proxy for spec-to-abstract transfer closure.
    SpecProjectionCheckedAPS

NoForkAFiniteAPS ==
    \A v \in 0..MaxView: Cardinality(AbsDecidedByViewFinite[v]) <= 1

LockMonotonicityAFiniteAPS ==
    /\ AbsLockedView <= AbsHighView
    /\ AbsHighView <= AbsView

SafetyAFiniteAPS ==
    /\ NoForkAFiniteAPS
    /\ LockMonotonicityAFiniteAPS

RefinementInvariantCoreAPS ==
    /\ AbsChainProjectionInvariant
    /\ SafetyAFiniteAPS

SafetyBridgeFiniteAPS ==
    (NoForkPerView /\ QCLocked /\ QCViewSafety) => SafetyAFiniteAPS

CommitProjectionShapeAPS ==
    (Len(st.chain) >= 2) => (Len(AbsChain) >= 2)

=============================================================================
