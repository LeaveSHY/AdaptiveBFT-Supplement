--------------------- MODULE AdaptiveBFT_Properties ---------------------
EXTENDS AdaptiveBFT

(***************************************************************************)
(* Figure-E artifact: correctness properties only (safety + liveness).     *)
(***************************************************************************)

I1_TypeOK == TypeOK
I2_Consistency == Consistency
I3_NoForkPerView == NoForkPerView
I4_PipelineBounded == PipelineBounded
I5_QCLocked == QCLocked
I6_QCViewSafety == QCViewSafety
I7_MempoolSoundness == MempoolSoundness
I8_ProposalFlowSafety == ProposalFlowSafety
I9_ViewChangeMessageSafety == ViewChangeMessageSafety
I10_ChainParentSafety == ChainParentSafety
I11_PrimaryEligibilitySafety == PrimaryEligibilitySafety
I12_ReconfigurationSafety == ReconfigurationSafety
I13_DecoupledPipelineSafety == DecoupledPipelineSafety

SafetyProfile ==
    /\ I1_TypeOK
    /\ I2_Consistency
    /\ I3_NoForkPerView
    /\ I4_PipelineBounded
    /\ I5_QCLocked
    /\ I6_QCViewSafety
    /\ I7_MempoolSoundness
    /\ I8_ProposalFlowSafety
    /\ I9_ViewChangeMessageSafety
    /\ I10_ChainParentSafety
    /\ I11_PrimaryEligibilitySafety
    /\ I12_ReconfigurationSafety
    /\ I13_DecoupledPipelineSafety

L1_EventuallyOneCommit == EventuallyOneCommit
L2_EventuallyTwoCommits == EventuallyTwoCommits
L3_InfiniteCollectMinor == InfiniteCollectMinor
L4_EventuallyViewProgress == EventuallyViewProgress

\* Safety abstraction used in manuscript text.
\* It aggregates the protocol's core safety requirements.
Safety == SafetyProfile

\* Liveness abstraction used in manuscript text.
\* The main reported goal is eventual progress to at least two committed blocks.
Liveness == L2_EventuallyTwoCommits

=============================================================================
