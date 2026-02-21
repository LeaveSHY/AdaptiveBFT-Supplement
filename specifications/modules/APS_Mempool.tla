-------------------------- MODULE APS_Mempool --------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Figure-D artifact: APS scheduler + mempool support definitions.         *)
(***************************************************************************)

\* ========================= APS_Scheduler =========================

APSConfigType(maxBatch, maxPipeline, maxTimeout) ==
    [
        batchSize : 1..maxBatch,
        pipelineDepth : 1..maxPipeline,
        timeout : 1..maxTimeout
    ]

ConfigSatisfiesNetwork(cfg, networkCondition) ==
    IF networkCondition = "Unstable"
    THEN /\ cfg.timeout >= 2
         /\ cfg.batchSize <= 2
         /\ cfg.pipelineDepth <= 2
    ELSE /\ cfg.timeout >= 1
         /\ cfg.batchSize >= 1
         /\ cfg.pipelineDepth >= 1

LatencyScore(cfg, networkCondition) ==
    IF networkCondition = "Unstable"
    THEN (2 * cfg.timeout) + cfg.batchSize + cfg.pipelineDepth
    ELSE cfg.timeout + cfg.batchSize

ThroughputScore(cfg) == cfg.batchSize * cfg.pipelineDepth

PerformanceScore(cfg, networkCondition) ==
    (2 * LatencyScore(cfg, networkCondition)) - ThroughputScore(cfg)

ChooseBetterConfig(current, candidate, networkCondition) ==
    IF PerformanceScore(candidate, networkCondition)
        <= PerformanceScore(current, networkCondition)
    THEN candidate
    ELSE current

RefineTimeout(timeout, networkCondition, maxTimeout) ==
    IF networkCondition = "Unstable"
    THEN IF timeout < maxTimeout THEN timeout + 1 ELSE maxTimeout
    ELSE 1

AdvanceSchedulerState(state) ==
    IF state = "Monitor" THEN "Sample"
    ELSE IF state = "Sample" THEN "Estimate"
    ELSE IF state = "Estimate" THEN "Explore"
    ELSE IF state = "Explore" THEN "Deploy"
    ELSE "Monitor"

\* ============================ Mempool ============================

PriorityClass(tx, age, hotTx, warmTx, agingThreshold) ==
    IF tx \in hotTx \/ age[tx] >= agingThreshold THEN "High"
    ELSE IF tx \in warmTx THEN "Mid"
    ELSE "Low"

PriorityBucket(pool, age, hotTx, warmTx, agingThreshold, class) ==
    {tx \in pool:
        PriorityClass(tx, age, hotTx, warmTx, agingThreshold) = class}

PriorityFront(pool, age, hotTx, warmTx, agingThreshold) ==
    LET hi ==
            PriorityBucket(
                pool,
                age,
                hotTx,
                warmTx,
                agingThreshold,
                "High"
            )
        mid ==
            PriorityBucket(
                pool,
                age,
                hotTx,
                warmTx,
                agingThreshold,
                "Mid"
            )
        low ==
            PriorityBucket(
                pool,
                age,
                hotTx,
                warmTx,
                agingThreshold,
                "Low"
            )
    IN IF hi # {} THEN hi ELSE IF mid # {} THEN mid ELSE low

SelectBatch(pool, age, hotTx, warmTx, agingThreshold, limit) ==
    CHOOSE chosen \in SUBSET pool:
        /\ chosen # {}
        /\ Cardinality(chosen) <= limit
        /\ chosen \subseteq
            PriorityFront(pool, age, hotTx, warmTx, agingThreshold)

RecoverTransactions(abstractSet, validatedPool) ==
    abstractSet \cap validatedPool

AgeMapBump(age, tx, maxAge) ==
    [age EXCEPT ![tx] = IF age[tx] < maxAge THEN age[tx] + 1 ELSE maxAge]

ResetAges(age, txs) ==
    [t \in DOMAIN age |-> IF t \in txs THEN 0 ELSE age[t]]

=============================================================================
