---------------------- MODULE AdaptiveBFT_Refinement ----------------------
EXTENDS AdaptiveBFT, Naturals, Sequences

\* Concrete-to-abstract projection used by the theorem track.
AbsView ==
    IF st.phase = "ViewChange" /\ st.view < MaxView
    THEN st.view + 1
    ELSE st.view

AbsPhase ==
    IF st.phase = "ViewChange"
    THEN "ViewChange"
    ELSE IF st.phase = "PreCommit" THEN "PreCommit"
    ELSE IF st.phase = "Commit" THEN "Commit"
    ELSE "Prepare"

AbsLockedView ==
    IF st.lockedQC.view < 0 THEN 0 ELSE st.lockedQC.view

AbsHighView ==
    IF st.highQC.view < 0 THEN 0 ELSE st.highQC.view

AbsVotes ==
    IF st.phase = "Prepare" THEN st.prepareVotes ELSE {}

AbsDecidedByView ==
    [v \in Nat |->
        IF v \in 0..MaxView THEN st.decidedByView[v] ELSE {}
    ]

AbsChain ==
    [i \in 1..Len(st.chain) |-> st.chain[i].view]

AbsNetworkStable ==
    IF st.view = 0 /\ st.phase = "CollectMinor"
    THEN FALSE
    ELSE (st.networkCondition = "Stable")

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
            chain <- AbsChain,
            networkStable <- AbsNetworkStable

AbsChainProjectionInvariant ==
    /\ Len(AbsChain) = Len(st.chain)
    /\ \A i \in 1..Len(st.chain): AbsChain[i] = st.chain[i].view

RefinementInvariant ==
    /\ TypeOK
    /\ AbsChainProjectionInvariant
    /\ ABSTRACT!NoForkA
    /\ ABSTRACT!LockMonotonicityA

THEOREM AbsChainProjection ==
    AbsChainProjectionInvariant
PROOF
    OBVIOUS

THEOREM ConcreteCommitProjection ==
    (Len(st.chain) >= 2) => (Len(AbsChain) >= 2)
PROOF
    OBVIOUS

THEOREM ConcreteSafetyImpliesAbstractSafety ==
    (NoForkPerView /\ QCLocked /\ QCViewSafety) => ABSTRACT!SafetyA
PROOF
    BY DEF NoForkPerView,
           QCLocked,
           QCViewSafety,
           AbsDecidedByView,
           AbsLockedView,
           AbsHighView,
           AbsView,
           ABSTRACT!SafetyA,
           ABSTRACT!NoForkA,
           ABSTRACT!LockMonotonicityA

THEOREM ConcreteLivenessShape ==
    EventuallyTwoCommits => ABSTRACT!LivenessA
PROOF
    BY ConcreteCommitProjection
       DEF EventuallyTwoCommits,
           ABSTRACT!LivenessA

=============================================================================
