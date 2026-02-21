------------------- MODULE AdaptiveBFT_MainClaim_Theorems -------------------
EXTENDS AdaptiveBFT_Transfer_Kernel, TLAPS

\* Top-level assumption envelope for assumption-explicit theorem claims.
ConcreteAssumptionEnvelope ==
    /\ KernelAbstractSpecEnvelope
    /\ TransferLivenessAssumptions
    /\ ConcreteBridgeAssumptions
    /\ <> (Len(cChainViews) >= 2)

THEOREM EnvelopeImpliesSpecAndAssumptions ==
    ConcreteAssumptionEnvelope =>
    /\ KernelAbstractSpecEnvelope
    /\ TransferLivenessAssumptions
    /\ ConcreteBridgeAssumptions
    /\ <> (Len(cChainViews) >= 2)
PROOF
    BY DEF ConcreteAssumptionEnvelope

THEOREM MainSafetyClaimTemplate ==
    ASSUME /\ KernelAbstractSpecEnvelope
           /\ ConcreteBridgeAssumptions
    PROVE /\ []TransferSafety
          /\ ProjectedSafety
PROOF
    BY KernelTransferSafetySubgoal

THEOREM MainLivenessClaimTemplate ==
    ASSUME /\ KernelAbstractSpecEnvelope
           /\ TransferLivenessAssumptions
           /\ <> (Len(cChainViews) >= 2)
    PROVE /\ TransferLiveness
          /\ ProjectedLiveness
PROOF
    BY KernelTransferLivenessSubgoal

THEOREM MainCorrectnessClaimTemplate ==
    ASSUME ConcreteAssumptionEnvelope
    PROVE /\ []TransferSafety
          /\ TransferLiveness
          /\ ProjectedSafety
          /\ ProjectedLiveness
PROOF
    <1>1. /\ KernelAbstractSpecEnvelope
          /\ TransferLivenessAssumptions
          /\ ConcreteBridgeAssumptions
          /\ <> (Len(cChainViews) >= 2)
        BY DEF ConcreteAssumptionEnvelope
    <1>2. /\ []TransferSafety
          /\ TransferLiveness
          /\ ProjectedSafety
          /\ ProjectedLiveness
        BY KernelTransferClosureChecklist, <1>1
    <1> QED
        BY <1>2

=============================================================================
