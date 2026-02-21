------------------- MODULE AdaptiveBFT_Liveness_Theorems -------------------
EXTENDS AdaptiveBFT_Refinement_Theorems, TLAPS

\* Explicitly expose the liveness assumption envelope used by theorem claims.
LivenessAssumptionEnvelopeA ==
    /\ EventuallyStableA
    /\ FairVoteA
    /\ WF_varsA(PrepareQCA)
    /\ WF_varsA(PreCommitQCA)
    /\ WF_varsA(CommitA)
    /\ WF_varsA(RecoverSyncA)

THEOREM LivenessAssumptionsDecompose ==
    LivenessAssumptionsA => LivenessAssumptionEnvelopeA
PROOF
    BY DEF LivenessAssumptionsA, LivenessAssumptionEnvelopeA

THEOREM AbstractLivenessClosure ==
    (SpecA /\ LivenessAssumptionsA) => LivenessA
PROOF
    BY AbstractLivenessTheorem

\* Refinement-facing template:
\* if projected concrete execution satisfies abstract assumptions and projected
\* commit progress, both abstract and projected liveness follow.
THEOREM RefinementLivenessTemplate ==
    ASSUME /\ TransferSpec
           /\ TransferLivenessAssumptions
           /\ <> (Len(cChainViews) >= 2)
    PROVE /\ TransferLiveness
          /\ ProjectedLiveness
PROOF
    <1>1. TransferLiveness
        BY AbstractLivenessTransferTemplate
    <1>2. ProjectedLiveness
        BY RefinementLivenessBridge
    <1> QED
        BY <1>1, <1>2

=============================================================================
