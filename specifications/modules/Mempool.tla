--------------------------- MODULE Mempool ---------------------------
EXTENDS Naturals, FiniteSets

PriorityClass(tx, age, hotTx, warmTx, agingThreshold) ==
    IF tx \in hotTx \/ age[tx] >= agingThreshold THEN "High"
    ELSE IF tx \in warmTx THEN "Mid"
    ELSE "Low"

PriorityBucket(pool, age, hotTx, warmTx, agingThreshold, class) ==
    {tx \in pool: PriorityClass(tx, age, hotTx, warmTx, agingThreshold) = class}

PriorityFront(pool, age, hotTx, warmTx, agingThreshold) ==
    LET hi == PriorityBucket(pool, age, hotTx, warmTx, agingThreshold, "High")
        mid == PriorityBucket(pool, age, hotTx, warmTx, agingThreshold, "Mid")
        low == PriorityBucket(pool, age, hotTx, warmTx, agingThreshold, "Low")
    IN IF hi # {} THEN hi ELSE IF mid # {} THEN mid ELSE low

SelectBatch(pool, age, hotTx, warmTx, agingThreshold, limit) ==
    CHOOSE chosen \in SUBSET pool:
        /\ chosen # {}
        /\ Cardinality(chosen) <= limit
        /\ chosen \subseteq PriorityFront(pool, age, hotTx, warmTx, agingThreshold)

RecoverTransactions(abstractSet, validatedPool) ==
    abstractSet \cap validatedPool

AgeMapBump(age, tx, maxAge) ==
    [age EXCEPT ![tx] = IF age[tx] < maxAge THEN age[tx] + 1 ELSE maxAge]

ResetAges(age, txs) ==
    [t \in DOMAIN age |-> IF t \in txs THEN 0 ELSE age[t]]

=============================================================================
