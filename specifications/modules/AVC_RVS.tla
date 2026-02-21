------------------------- MODULE AVC_RVS -------------------------
EXTENDS Naturals, Integers, FiniteSets,
        RVS_CryptoAbstraction, Reputation_Game

Clamp(v, maxV) ==
    IF v < 0 THEN 0 ELSE IF v > maxV THEN maxV ELSE v

SumRep(reputation, nodes) ==
    LET bound == MaxNat({reputation[n] : n \in nodes})
    IN
        Cardinality(
            {p \in (nodes \X (1..bound)) : p[2] <= reputation[p[1]]}
        )

AverageRep(reputation) ==
    LET nodes == DOMAIN reputation
        card == Cardinality(nodes)
    IN IF card = 0 THEN 0 ELSE SumRep(reputation, nodes) \div card

CanonicalReporters(reputation) == DOMAIN reputation

CanonicalReports(reputation) ==
    CanonicalSelfReports(CanonicalReporters(reputation), reputation)

RecomputeReputation(reputation, maxRep, decayNumerator, decayDenominator) ==
    LET nodes == DOMAIN reputation
    IN
        ReputationFromReports(
            CanonicalReports(reputation),
            reputation,
            nodes,
            nodes,
            decayNumerator,
            decayDenominator,
            maxRep
        )

CandidateReplicas(reputation, threshold) ==
    LET allNodes == DOMAIN reputation
        base == {n \in allNodes: reputation[n] >= threshold}
        avg == AverageRep(reputation)
        weighted == {n \in base: reputation[n] >= avg}
    IN
        IF weighted # {}
        THEN weighted
        ELSE IF base # {} THEN base ELSE allNodes

RVSKappa(candidates, threshold) ==
    LET card == Cardinality(candidates)
        base == IF threshold < 1 THEN 1 ELSE threshold
    IN
        IF card = 0
        THEN 1
        ELSE IF base <= card THEN base ELSE card

RVSContext(reputation, threshold) ==
    LET cand == CandidateReplicas(reputation, threshold)
        maxRep == MaxNat({reputation[n] : n \in DOMAIN reputation})
    IN
        [
            candidates |-> cand,
            maxRep |-> maxRep,
            totalWeight |-> SumRep(reputation, cand),
            kappa |-> RVSKappa(cand, threshold)
        ]

RVSSelectPrimary(reputation, threshold, view) ==
    LET ctx == RVSContext(reputation, threshold)
        winners ==
            ValidWinners(
                reputation,
                ctx.candidates,
                view,
                ctx.totalWeight,
                ctx.kappa,
                ctx.maxRep
            )
    IN
        PickWinner(
            reputation,
            winners,
            view,
            ctx.totalWeight,
            ctx.kappa,
            ctx.maxRep
        )

RVSPrimaryEvidence(reputation, threshold, view, leader) ==
    LET ctx == RVSContext(reputation, threshold)
        result ==
            SortitionResult(
                reputation,
                leader,
                view,
                ctx.totalWeight,
                ctx.kappa,
                ctx.maxRep
            )
    IN
        [ticket |-> result.ticket, strikes |-> result.strikes, proof |-> result.proof]

RVSVerifyPrimary(reputation, threshold, view, leader, ticket, strikes, proof) ==
    LET ctx == RVSContext(reputation, threshold)
        draws == ctx.kappa
        result ==
            SortitionResult(
                reputation,
                leader,
                view,
                ctx.totalWeight,
                draws,
                ctx.maxRep
            )
        winners ==
            ValidWinners(
                reputation,
                ctx.candidates,
                view,
                ctx.totalWeight,
                draws,
                ctx.maxRep
            )
        verified ==
            SortitionVerify(
                reputation,
                leader,
                view,
                ctx.totalWeight,
                draws,
                ctx.maxRep,
                result
            )
    IN
        /\ leader \in ctx.candidates
        /\ leader \in winners
        /\ result.ticket = ticket
        /\ result.strikes = strikes
        /\ result.proof = proof
        /\ verified

TemporalDecay(previous, observed, decayNumerator, decayDenominator) ==
    ((decayNumerator * previous) + ((decayDenominator - decayNumerator) * observed)) \div decayDenominator

DecayUpdateByObservation(reputation, node, observed, maxRep, decayNumerator, decayDenominator) ==
    LET boundedObserved == Clamp(observed, maxRep)
        blended == TemporalDecay(reputation[node], boundedObserved, decayNumerator, decayDenominator)
        base == [reputation EXCEPT ![node] = Clamp(blended, maxRep)]
        recomputed ==
            RecomputeReputation(
                base,
                maxRep,
                decayNumerator,
                decayDenominator
            )
    IN
        [n \in DOMAIN recomputed |-> Clamp(recomputed[n], maxRep)]

DecayUpdate(reputation, node, isHonest, maxRep, decayNumerator, decayDenominator) ==
    LET observed == IF isHonest THEN maxRep ELSE 0
    IN DecayUpdateByObservation(reputation, node, observed, maxRep, decayNumerator, decayDenominator)

=============================================================================
