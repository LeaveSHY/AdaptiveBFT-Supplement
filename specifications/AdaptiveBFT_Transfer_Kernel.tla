-------------------- MODULE AdaptiveBFT_Transfer_Kernel --------------------
EXTENDS AdaptiveBFT_Refinement_Kernel, AdaptiveBFT_Liveness_Theorems, TLAPS

\* TLAPS-friendly transfer subgoals over the mapped abstract envelope.
\* This module stays on the non-recursive theorem stack so it can be used
\* as a machine-checked gate for transfer-closure progress.

KernelAbstractSpecEnvelope ==
    TransferSpec

THEOREM KernelSpecEnvelopeImpliesSpecA ==
    KernelAbstractSpecEnvelope => TransferSpec
PROOF
    BY DEF KernelAbstractSpecEnvelope

THEOREM KernelTransferSafetySubgoal ==
    ASSUME /\ KernelAbstractSpecEnvelope
           /\ ConcreteBridgeAssumptions
    PROVE /\ []TransferSafety
          /\ ProjectedSafety
PROOF
    <1>1. TransferSpec
        BY KernelSpecEnvelopeImpliesSpecA
    <1>2. /\ []TransferSafety
          /\ ProjectedSafety
        BY KernelMappedSafetySummary, <1>1
    <1> QED
        BY <1>2

THEOREM KernelTransferLivenessSubgoal ==
    ASSUME /\ KernelAbstractSpecEnvelope
           /\ TransferLivenessAssumptions
           /\ <> (Len(cChainViews) >= 2)
    PROVE /\ TransferLiveness
          /\ ProjectedLiveness
PROOF
    <1>1. TransferSpec
        BY KernelSpecEnvelopeImpliesSpecA
    <1>2. /\ TransferLiveness
          /\ ProjectedLiveness
        BY KernelMappedLivenessSummary, <1>1
    <1> QED
        BY <1>2

THEOREM KernelTransferClosureChecklist ==
    ASSUME /\ KernelAbstractSpecEnvelope
           /\ TransferLivenessAssumptions
           /\ ConcreteBridgeAssumptions
           /\ <> (Len(cChainViews) >= 2)
    PROVE /\ []TransferSafety
          /\ TransferLiveness
          /\ ProjectedSafety
          /\ ProjectedLiveness
PROOF
    <1>1. /\ []TransferSafety
          /\ ProjectedSafety
        BY KernelTransferSafetySubgoal
    <1>2. /\ TransferLiveness
          /\ ProjectedLiveness
        BY KernelTransferLivenessSubgoal
    <1> QED
        BY <1>1, <1>2

=============================================================================
