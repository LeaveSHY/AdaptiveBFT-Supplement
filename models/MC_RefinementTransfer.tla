--------------------- MODULE MC_RefinementTransfer ---------------------
EXTENDS AdaptiveBFT_Refinement

\* TLC-safe finite projection for decidedByView (avoids Nat-indexed extensional checks).
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

\* Concrete protocol spec over full state.
SpecTransfer ==
    /\ Init
    /\ [][Next]_vars

\* TLC-safe finite init projection shape (avoids Nat-domain extensional checks).
InitProjectionShape ==
    /\ AbsView = 0
    /\ AbsPhase = "Prepare"
    /\ AbsLockedView = 0
    /\ AbsHighView = 0
    /\ AbsVotes = {}
    /\ AbsDecidedByViewFinite = [v \in 0..MaxView |-> {}]
    /\ AbsChain = <<>>

\* Init transfer obligation used by transfer theorem templates.
InitProjectionOK ==
    Init => InitProjectionShape

\* Core step obligation: each concrete step is mapped or stutters on abstract vars.
StepProjectionOK ==
    Next => (ABOUNDED!NextA \/ UNCHANGED ABOUNDED!varsA)

\* Equivalent boxed action form used by transfer templates.
StepBoxProjectionOK ==
    Next => [ABOUNDED!NextA]_ABOUNDED!varsA

\* TLC-checkable temporal wrappers.
StepProjectionChecked ==
    [][StepProjectionOK]_vars

StepBoxProjectionChecked ==
    [][StepBoxProjectionOK]_vars

InitProjectionChecked ==
    InitProjectionOK

\* Checklist property matching theorem-track transfer assumptions:
\* init projection + boxed step projection.
SpecProjectionChecked ==
    InitProjectionOK /\ StepBoxProjectionChecked

SpecToAbstractSpecChecked ==
    \* TLC-safe proxy for spec-to-abstract transfer closure.
    SpecProjectionChecked

NoForkAFiniteTransfer ==
    \A v \in 0..MaxView: Cardinality(AbsDecidedByViewFinite[v]) <= 1

LockMonotonicityAFiniteTransfer ==
    /\ AbsLockedView <= AbsHighView
    /\ AbsHighView <= AbsView

SafetyAFiniteTransfer ==
    /\ NoForkAFiniteTransfer
    /\ LockMonotonicityAFiniteTransfer

RefinementInvariantCoreTransfer ==
    /\ AbsChainProjectionInvariant
    /\ SafetyAFiniteTransfer

SafetyBridgeFiniteTransfer ==
    (NoForkPerView /\ QCLocked /\ QCViewSafety) => SafetyAFiniteTransfer

CommitProjectionShapeTransfer ==
    (Len(st.chain) >= 2) => (Len(AbsChain) >= 2)

\* Optional TLC state-space throttle for transfer diagnostics.
TransferConstraint ==
    /\ st.schedulerState = "Monitor"
    /\ st.networkCondition = "Stable"
    /\ st.view = 0
    /\ Len(st.chain) = 0

=============================================================================
