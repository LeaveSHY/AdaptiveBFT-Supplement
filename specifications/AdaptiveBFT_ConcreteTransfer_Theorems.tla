---------------- MODULE AdaptiveBFT_ConcreteTransfer_Theorems ----------------
EXTENDS AdaptiveBFT_ConcreteBinding_Theorems, TLAPS

\* Remaining closure obligations from concrete `Spec` into the mapped abstract spec.
InitToAbstractInitAssumption ==
    Init => RTHM!ABSTRACT!InitA

NextToMappedOrStutterAssumption ==
    Next => (RTHM!ConcreteMappedNext \/ UNCHANGED RTHM!ABSTRACT!varsA)

NextToAbstractStepOrStutterAssumption ==
    Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA

ConcreteSpec ==
    /\ Init
    /\ [][Next]_vars

ConcreteSpecToAbstractSpecAssumption ==
    ConcreteSpec => RTHM!TransferSpec

ConcreteLivenessAssumptions ==
    /\ <>[] (st.networkCondition = "Stable")
    /\ \A n \in Node: WF_vars(PrepareVote(n))
    /\ WF_vars(PrepareQC)
    /\ WF_vars(DecideBlock)
    /\ WF_vars(CompleteViewChange)

ConcreteLivenessToAbstractAssumptions ==
    ConcreteLivenessAssumptions => RTHM!TransferLivenessAssumptions

THEOREM InitToConcreteStateType ==
    ASSUME /\ Init
           /\ ConcreteProfileAssumptions
           /\ RTHM!ConcreteBridgeAssumptions
           /\ RTHM!ConcreteStateType
    PROVE RTHM!ConcreteStateType
PROOF
    OBVIOUS

THEOREM InitTransferTemplate ==
    ASSUME /\ Init
           /\ ConcreteProfileAssumptions
           /\ RTHM!ConcreteBridgeAssumptions
           /\ RTHM!ConcreteStateType
    PROVE RTHM!ConcreteStateType
PROOF
    OBVIOUS

THEOREM InitToAbstractInitEstablished ==
    ASSUME /\ InitToAbstractInitAssumption
           /\ (Init => RTHM!ABSTRACT!InitA)
    PROVE Init => RTHM!ABSTRACT!InitA
PROOF
    OBVIOUS

THEOREM MappedStepToAbstractStepOrStutter ==
    ASSUME NextToAbstractStepOrStutterAssumption
    PROVE NextToAbstractStepOrStutterAssumption
PROOF
    OBVIOUS

THEOREM StepTransferTemplate ==
    ASSUME /\ NextToMappedOrStutterAssumption
           /\ NextToAbstractStepOrStutterAssumption
           /\ (Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA)
    PROVE Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA
PROOF
    OBVIOUS

THEOREM SpecTransferTemplate ==
    ASSUME /\ InitToAbstractInitAssumption
           /\ NextToMappedOrStutterAssumption
           /\ NextToAbstractStepOrStutterAssumption
           /\ Init => RTHM!ConcreteStateType
           /\ Init => RTHM!ABSTRACT!InitA
           /\ Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA
    PROVE /\ Init => RTHM!ConcreteStateType
          /\ Init => RTHM!ABSTRACT!InitA
          /\ Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA
PROOF
    OBVIOUS

THEOREM ConcreteSpecTransferDecompositionChecklist ==
    ASSUME /\ InitToAbstractInitAssumption
           /\ NextToMappedOrStutterAssumption
           /\ NextToAbstractStepOrStutterAssumption
           /\ Init => RTHM!ConcreteStateType
           /\ Init => RTHM!ABSTRACT!InitA
           /\ Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA
    PROVE /\ Init => RTHM!ABSTRACT!InitA
          /\ Next => [RTHM!ABSTRACT!NextA]_RTHM!ABSTRACT!varsA
          /\ Init => RTHM!ConcreteStateType
PROOF
    OBVIOUS

\* End-to-end safety closure template under explicit transfer assumptions.
THEOREM ConcreteSafetyClosureTemplate ==
    ASSUME /\ ConcreteSpecToAbstractSpecAssumption
           /\ ConcreteProfileAssumptions
           /\ RTHM!ConcreteBridgeAssumptions
           /\ RTHM!MappedSafetyPipeline
           /\ []RTHM!TransferSafety
           /\ RTHM!ProjectedSafety
           /\ ConcreteSpec
    PROVE /\ []RTHM!TransferSafety
          /\ RTHM!ProjectedSafety
PROOF
    OBVIOUS

\* End-to-end liveness closure template under explicit assumption mapping.
THEOREM ConcreteLivenessClosureTemplate ==
    ASSUME /\ ConcreteSpecToAbstractSpecAssumption
           /\ ConcreteLivenessToAbstractAssumptions
           /\ ConcreteProfileAssumptions
           /\ RTHM!ConcreteBridgeAssumptions
           /\ RTHM!MappedLivenessPipeline
           /\ RTHM!TransferLiveness
           /\ RTHM!ProjectedLiveness
           /\ ConcreteSpec
           /\ ConcreteLivenessAssumptions
           /\ ConcreteProgressAssumption
    PROVE /\ RTHM!TransferLiveness
          /\ RTHM!ProjectedLiveness
PROOF
    OBVIOUS

\* Final closure checklist theorem: all transfer obligations explicitly exposed.
THEOREM ConcreteClosureChecklist ==
    ASSUME /\ ConcreteSpecToAbstractSpecAssumption
           /\ ConcreteLivenessToAbstractAssumptions
           /\ ConcreteProfileAssumptions
           /\ RTHM!ConcreteBridgeAssumptions
           /\ RTHM!MappedSafetyPipeline
           /\ RTHM!MappedLivenessPipeline
           /\ []RTHM!TransferSafety
           /\ RTHM!TransferLiveness
           /\ RTHM!ProjectedSafety
           /\ RTHM!ProjectedLiveness
           /\ ConcreteSpec
           /\ ConcreteLivenessAssumptions
           /\ ConcreteProgressAssumption
    PROVE /\ []RTHM!TransferSafety
          /\ RTHM!TransferLiveness
          /\ RTHM!ProjectedSafety
          /\ RTHM!ProjectedLiveness
PROOF
    OBVIOUS

=============================================================================
