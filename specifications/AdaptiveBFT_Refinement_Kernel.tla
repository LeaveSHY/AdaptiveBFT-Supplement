------------------- MODULE AdaptiveBFT_Refinement_Kernel -------------------
EXTENDS AdaptiveBFT_Refinement_Theorems, TLAPS

\* Kernel-level refinement summary that stays within TLAPS-supported
\* (non-recursive) operators while reusing the mapped bridge theorems.

THEOREM KernelInitToAbstractInit ==
    ConcreteInitShape => ABSTRACT!InitA
PROOF
    BY RefinementInitBridge

THEOREM KernelStepToAbstractStepOrStutter ==
    ConcreteMappedNext => [ABSTRACT!NextA]_ABSTRACT!varsA
PROOF
    <1>1. ConcreteMappedNext => ABSTRACT!NextA
        BY RefinementStepBridge
    <1> QED
        BY <1>1 DEF ABSTRACT!varsA

THEOREM KernelMappedSafetySummary ==
    ASSUME /\ TransferSpec
           /\ ConcreteBridgeAssumptions
    PROVE /\ []TransferSafety
          /\ ProjectedSafety
PROOF
    BY MappedSafetyPipeline

THEOREM KernelMappedLivenessSummary ==
    ASSUME /\ TransferSpec
           /\ TransferLivenessAssumptions
           /\ <> (Len(cChainViews) >= 2)
    PROVE /\ TransferLiveness
          /\ ProjectedLiveness
PROOF
    BY MappedLivenessPipeline

THEOREM KernelEndToEndChecklist ==
    ASSUME /\ TransferSpec
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
        BY KernelMappedSafetySummary
    <1>2. /\ TransferLiveness
          /\ ProjectedLiveness
        BY KernelMappedLivenessSummary
    <1> QED
        BY <1>1, <1>2

=============================================================================
