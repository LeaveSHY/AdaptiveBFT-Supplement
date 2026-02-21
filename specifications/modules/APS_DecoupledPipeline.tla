------------------- MODULE APS_DecoupledPipeline -------------------
EXTENDS Naturals, FiniteSets

TakeBounded(pool, limit) ==
    IF pool = {}
    THEN {}
    ELSE
        CHOOSE chosen \in SUBSET pool:
            /\ chosen # {}
            /\ Cardinality(chosen) <= limit

DispatchFromPool(pool, currentBuffer, limit) ==
    TakeBounded(pool \ currentBuffer, limit)

PromoteBuffer(sourceBuffer, targetBuffer, limit) ==
    TakeBounded(sourceBuffer \ targetBuffer, limit)

DecouplingInvariant(
    dissemination,
    ordering,
    execution,
    computeQueued,
    computeReady,
    txUniverse
) ==
    /\ dissemination \subseteq txUniverse
    /\ ordering \subseteq txUniverse
    /\ execution \subseteq txUniverse
    /\ computeQueued \subseteq txUniverse
    /\ computeReady \subseteq txUniverse

DecouplingFlowSafety(
    validatedPool,
    orderedPool,
    fullProposalTxs,
    dissemination,
    ordering,
    execution,
    computeQueued,
    computeReady
) ==
    /\ ordering \subseteq dissemination \cup orderedPool \cup fullProposalTxs \cup validatedPool
    /\ execution \subseteq ordering \cup orderedPool \cup fullProposalTxs \cup validatedPool
    /\ computeQueued \subseteq ordering \cup execution \cup orderedPool \cup fullProposalTxs \cup validatedPool
    /\ computeReady \subseteq ordering \cup execution \cup orderedPool \cup fullProposalTxs \cup validatedPool
    /\ orderedPool \subseteq dissemination \cup ordering \cup execution \cup validatedPool

=============================================================================
