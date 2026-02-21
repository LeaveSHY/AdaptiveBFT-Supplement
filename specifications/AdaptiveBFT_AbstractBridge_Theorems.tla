------------------ MODULE AdaptiveBFT_AbstractBridge_Theorems ------------------
EXTENDS TLAPS

CONSTANTS Node, F, Quorum

VARIABLES
    view,
    phase,
    lockedView,
    highView,
    votes,
    decidedByView,
    chain,
    networkStable

ABSTRACT_THEOREMS ==
    INSTANCE AdaptiveBFT_Theorems
        WITH
            Node <- Node,
            F <- F,
            Quorum <- Quorum,
            view <- view,
            phase <- phase,
            lockedView <- lockedView,
            highView <- highView,
            votes <- votes,
            decidedByView <- decidedByView,
            chain <- chain,
            networkStable <- networkStable

THEOREM SafetyTransferFromInstance ==
    ABSTRACT_THEOREMS!SpecA => []ABSTRACT_THEOREMS!SafetyA
PROOF
    BY ABSTRACT_THEOREMS!AbstractSafetyTheorem

THEOREM LivenessTransferFromInstance ==
    (ABSTRACT_THEOREMS!SpecA /\ ABSTRACT_THEOREMS!LivenessAssumptionsA)
    => ABSTRACT_THEOREMS!LivenessA
PROOF
    BY ABSTRACT_THEOREMS!AbstractLivenessTheorem

=============================================================================
