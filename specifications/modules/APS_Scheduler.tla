----------------------- MODULE APS_Scheduler -----------------------
EXTENDS Naturals, FiniteSets

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
    IF PerformanceScore(candidate, networkCondition) <= PerformanceScore(current, networkCondition)
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

=============================================================================
