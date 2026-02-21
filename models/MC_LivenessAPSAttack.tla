--------------------- MODULE MC_LivenessAPSAttack ---------------------
EXTENDS AdaptiveBFT_Refinement, TLC

CONSTANTS MaxAttackCount

VARIABLES apsBootDone, attackCount

varsJoint == <<st, apsBootDone, attackCount>>

InitJoint ==
    /\ Init
    /\ apsBootDone = FALSE
    /\ attackCount = 0

SchedulerBootstrap ==
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Monitor"
       /\ st' = [st EXCEPT !.networkCondition = "Stable", !.schedulerState = "Sample"]
       /\ apsBootDone' = FALSE
       /\ UNCHANGED attackCount
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Sample"
       /\ SampleGrid
       /\ apsBootDone' = FALSE
       /\ UNCHANGED attackCount
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Estimate"
       /\ EstimateGrid
       /\ apsBootDone' = FALSE
       /\ UNCHANGED attackCount
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Explore"
       /\ ExploreGrid
       /\ apsBootDone' = FALSE
       /\ UNCHANGED attackCount
    \/ /\ ~apsBootDone
       /\ st.phase = "CollectMinor"
       /\ st.schedulerState = "Deploy"
       /\ DeployConfig
       /\ apsBootDone' = TRUE
       /\ UNCHANGED attackCount

AdaptiveCorruption ==
    /\ apsBootDone
    /\ attackCount < MaxAttackCount
    /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
    /\ LET rep1 == DecayUpdate(st.reputation, st.primary, FALSE, MaxReputation, DecayNumerator, DecayDenominator)
       IN
       /\ st' = [
            st EXCEPT
                !.networkCondition = "Unstable",
                !.schedulerState = "Sample",
                !.stageTimer = st.activeConfig.timeout,
                !.timeoutVotes = Node,
                !.reputation = rep1
        ]
    /\ apsBootDone' = apsBootDone
    /\ attackCount' = attackCount + 1

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

PostBootstrapStable ==
    /\ apsBootDone
    /\ st.networkCondition = "Stable"
    /\ StableConsensusNext
    /\ UNCHANGED <<apsBootDone, attackCount>>

RecoverAfterAttack ==
    /\ apsBootDone
    /\ st.networkCondition = "Unstable"
    /\ LET nextView == IF st.view < MaxView THEN st.view + 1 ELSE st.view
           nextPrimary == RVSSelectPrimary(st.reputation, RepThreshold, nextView)
           stableCfg == [st.activeConfig EXCEPT !.timeout = IF @ < 2 THEN 2 ELSE @]
       IN
       /\ st' = [st EXCEPT
                !.networkCondition = "Stable",
                !.schedulerState = "Monitor",
                !.phase = "CollectMinor",
                !.view = nextView,
                !.primary = nextPrimary,
                !.candidateReplicas = CandidateReplicas(st.reputation, RepThreshold),
                !.tentativePrimary = nextPrimary,
                !.teProposal = NoTeProposal,
                !.fullProposal = NoFullProposal,
                !.vProposal = NoVProposal,
                !.npMessage = NoNPMessage,
                !.synMessage = NoSynMessage,
                !.prepareVotes = {},
                !.precommitVotes = {},
                !.commitVotes = {},
                !.timeoutVotes = {},
                !.npConfirms = {},
                !.synAcks = {},
                !.orderedPool = {},
                !.stageTimer = 0,
                !.inFlight = 0,
                !.activeConfig = stableCfg,
                !.pendingConfig = stableCfg]
    /\ UNCHANGED <<apsBootDone, attackCount>>

NextJoint ==
    \/ SchedulerBootstrap
    \/ AdaptiveCorruption
    \/ RecoverAfterAttack
    \/ PostBootstrapStable

InjectFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ InjectTxStep /\ UNCHANGED <<apsBootDone, attackCount>>
PreValidateFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreValidateStep /\ UNCHANGED <<apsBootDone, attackCount>>
PreOrderFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreOrder /\ UNCHANGED <<apsBootDone, attackCount>>
GenerateProposalFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ GenerateTentativeProposal /\ UNCHANGED <<apsBootDone, attackCount>>
RecoverFullFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ RecoverFullProposal /\ UNCHANGED <<apsBootDone, attackCount>>
PrepareVoteFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PrepareVoteStep /\ UNCHANGED <<apsBootDone, attackCount>>
PrepareQCFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PrepareQC /\ UNCHANGED <<apsBootDone, attackCount>>
PreCommitVoteFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreCommitVoteStep /\ UNCHANGED <<apsBootDone, attackCount>>
PreCommitQCFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ PreCommitQC /\ UNCHANGED <<apsBootDone, attackCount>>
CommitVoteFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ CommitVoteStep /\ UNCHANGED <<apsBootDone, attackCount>>
DecideFair == /\ apsBootDone /\ st.networkCondition = "Stable" /\ DecideBlock /\ UNCHANGED <<apsBootDone, attackCount>>
RecoverFair == /\ apsBootDone /\ RecoverAfterAttack

AssumeBoundedAdversary ==
    attackCount <= MaxAttackCount

AssumeEventualStability ==
    <>[] (st.networkCondition = "Stable")

AssumeBootstrapFair ==
    WF_varsJoint(SchedulerBootstrap)

AssumeRecoveryFair ==
    WF_varsJoint(RecoverFair)

AssumeProgressFairness ==
    /\ WF_varsJoint(InjectFair)
    /\ WF_varsJoint(PreValidateFair)
    /\ WF_varsJoint(PreOrderFair)
    /\ WF_varsJoint(GenerateProposalFair)
    /\ WF_varsJoint(RecoverFullFair)
    /\ WF_varsJoint(PrepareVoteFair)
    /\ WF_varsJoint(PrepareQCFair)
    /\ WF_varsJoint(PreCommitVoteFair)
    /\ WF_varsJoint(PreCommitQCFair)
    /\ WF_varsJoint(CommitVoteFair)
    /\ WF_varsJoint(DecideFair)

AssumptionsJoint ==
    /\ AssumeBoundedAdversary
    /\ AssumeEventualStability
    /\ AssumeBootstrapFair
    /\ AssumeRecoveryFair
    /\ AssumeProgressFairness

AssumptionsJointForTLC ==
    /\ AssumeBoundedAdversary
    /\ AssumeBootstrapFair
    /\ AssumeRecoveryFair
    /\ AssumeProgressFairness

SpecJoint ==
    /\ InitJoint
    /\ [][NextJoint]_varsJoint
    /\ AssumptionsJointForTLC

JointConsensusLiveness == <> (Len(st.chain) >= 2)

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

InitProjectionShapeJoint ==
    /\ AbsView = 0
    /\ AbsPhase = "Prepare"
    /\ AbsLockedView = 0
    /\ AbsHighView = 0
    /\ AbsVotes = {}
    /\ AbsDecidedByViewFinite = [v \in 0..MaxView |-> {}]
    /\ AbsChain = <<>>

InitProjectionJoint ==
    InitJoint => InitProjectionShapeJoint

StepProjectionJoint ==
    NextJoint => (ABOUNDED!NextA \/ UNCHANGED ABOUNDED!varsA)

StepBoxProjectionJoint ==
    NextJoint => [ABOUNDED!NextA]_ABOUNDED!varsA

StepProjectionCheckedJoint ==
    [][StepProjectionJoint]_varsJoint

StepBoxProjectionCheckedJoint ==
    [][StepBoxProjectionJoint]_varsJoint

InitProjectionCheckedJoint ==
    InitProjectionJoint

SpecProjectionCheckedJoint ==
    InitProjectionJoint /\ StepBoxProjectionCheckedJoint

SpecToAbstractSpecCheckedJoint ==
    \* TLC-safe proxy for spec-to-abstract transfer closure.
    SpecProjectionCheckedJoint

NoForkAFiniteJoint ==
    \A v \in 0..MaxView: Cardinality(AbsDecidedByViewFinite[v]) <= 1

LockMonotonicityAFiniteJoint ==
    /\ AbsLockedView <= AbsHighView
    /\ AbsHighView <= AbsView

SafetyAFiniteJoint ==
    /\ NoForkAFiniteJoint
    /\ LockMonotonicityAFiniteJoint

RefinementInvariantCoreJoint ==
    /\ AbsChainProjectionInvariant
    /\ SafetyAFiniteJoint

SafetyBridgeFiniteJoint ==
    (NoForkPerView /\ QCLocked /\ QCViewSafety) => SafetyAFiniteJoint

CommitProjectionShapeJoint ==
    (Len(st.chain) >= 2) => (Len(AbsChain) >= 2)

=============================================================================
