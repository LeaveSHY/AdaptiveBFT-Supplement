----------------------- MODULE MC_AdaptiveAttack -----------------------
EXTENDS AdaptiveBFT_Refinement, TLC

CONSTANTS MaxAttackCount

VARIABLE attackCount

varsAttack == <<st, attackCount>>

InitAttack ==
    /\ Init
    /\ attackCount = 0

AdaptiveCorruption ==
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
    /\ attackCount' = attackCount + 1

\* Safety-only acceleration:
\* collapse per-replica voting/ack interleavings into quorum-completion steps
\* to keep adaptive-attack exploration tractable.
PrepareFast ==
    /\ st.phase = "Prepare"
    /\ st.fullProposal # NoFullProposal
    /\ Cardinality(st.prepareVotes) < Quorum
    /\ st' =
        [st EXCEPT
            !.prepareVotes = Node,
            !.highQC = QC(st.view),
            !.phase = "PreCommit",
            !.precommitVotes = {},
            !.stageTimer = 0]

PreCommitFast ==
    /\ st.phase = "PreCommit"
    /\ Cardinality(st.precommitVotes) < Quorum
    /\ st' =
        [st EXCEPT
            !.precommitVotes = Node,
            !.lockedQC = st.highQC,
            !.phase = "Commit",
            !.commitVotes = {},
            !.stageTimer = 0]

CommitFast ==
    /\ st.phase = "Commit"
    /\ st.fullProposal # NoFullProposal
    /\ Cardinality(st.commitVotes) < Quorum
    /\ st' = [st EXCEPT !.commitVotes = Node]

TimeoutQuorumFast ==
    /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
    /\ st.stageTimer >= st.activeConfig.timeout
    /\ Cardinality(st.timeoutVotes) < Quorum
    /\ st' = [st EXCEPT !.timeoutVotes = Node]

ConfirmNewPrimaryFast ==
    /\ st.phase = "ViewChange"
    /\ st.npMessage # NoNPMessage
    /\ NPMessageHasValidSortition(st.npMessage, st.reputation)
    /\ Cardinality(st.npConfirms) < Quorum
    /\ st' = [st EXCEPT !.npConfirms = Node]

SendSynAckFast ==
    /\ st.phase = "ViewChange"
    /\ st.synMessage # NoSynMessage
    /\ st.synMessage.rv = st.reputation
    /\ Cardinality(st.synAcks) < Quorum
    /\ st' = [st EXCEPT !.synAcks = Node]

ConsensusNextAttack ==
    \/ InjectTxStep
    \/ PreValidateStep
    \/ AgeTxStep
    \/ DispatchToDissemination
    \/ PromoteToOrdering
    \/ PromoteToExecution
    \/ PreOrder
    \/ GenerateTentativeProposal
    \/ RecoverFullProposal
    \/ PrepareFast
    \/ PreCommitFast
    \/ CommitFast
    \/ DecideBlock
    \/ Tick
    \/ TimeoutQuorumFast
    \/ StartViewChange
    \/ BroadcastNP
    \/ ConfirmNewPrimaryFast
    \/ BroadcastSyn
    \/ SendSynAckFast
    \/ CompleteViewChange

NextAttack ==
    \/ (ConsensusNextAttack /\ UNCHANGED attackCount)
    \/ AdaptiveCorruption

AssumeBoundedAttack ==
    attackCount <= MaxAttackCount

SpecAttack ==
    /\ InitAttack
    /\ [][NextAttack]_varsAttack
    /\ AssumeBoundedAttack
    /\ WF_varsAttack(InjectTxStep /\ UNCHANGED attackCount)
    /\ WF_varsAttack(PreValidateStep /\ UNCHANGED attackCount)

LivenessUnderAttack == <> (Len(st.chain) >= 1)

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

InitProjectionShapeAttack ==
    /\ AbsView = 0
    /\ AbsPhase = "Prepare"
    /\ AbsLockedView = 0
    /\ AbsHighView = 0
    /\ AbsVotes = {}
    /\ AbsDecidedByViewFinite = [v \in 0..MaxView |-> {}]
    /\ AbsChain = <<>>

InitProjectionAttack ==
    InitAttack => InitProjectionShapeAttack

StepProjectionAttack ==
    NextAttack => (ABOUNDED!NextA \/ UNCHANGED ABOUNDED!varsA)

StepBoxProjectionAttack ==
    NextAttack => [ABOUNDED!NextA]_ABOUNDED!varsA

StepProjectionCheckedAttack ==
    [][StepProjectionAttack]_varsAttack

StepBoxProjectionCheckedAttack ==
    [][StepBoxProjectionAttack]_varsAttack

InitProjectionCheckedAttack ==
    InitProjectionAttack

SpecProjectionCheckedAttack ==
    InitProjectionAttack /\ StepBoxProjectionCheckedAttack

SpecToAbstractSpecCheckedAttack ==
    \* TLC does not support arbitrary temporal implication between two
    \* full specs with action components in PROPERTY checks.
    \* Use the TLC-safe transfer checklist proxy.
    SpecProjectionCheckedAttack

NoForkAFiniteAttack ==
    \A v \in 0..MaxView: Cardinality(AbsDecidedByViewFinite[v]) <= 1

LockMonotonicityAFiniteAttack ==
    /\ AbsLockedView <= AbsHighView
    /\ AbsHighView <= AbsView

SafetyAFiniteAttack ==
    /\ NoForkAFiniteAttack
    /\ LockMonotonicityAFiniteAttack

RefinementInvariantCoreAttack ==
    /\ AbsChainProjectionInvariant
    /\ SafetyAFiniteAttack

SafetyBridgeFiniteAttack ==
    (NoForkPerView /\ QCLocked /\ QCViewSafety) => SafetyAFiniteAttack

CommitProjectionShapeAttack ==
    (Len(st.chain) >= 2) => (Len(AbsChain) >= 2)

=============================================================================
