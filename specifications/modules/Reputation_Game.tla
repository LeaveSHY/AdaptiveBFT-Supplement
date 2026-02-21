---------------------- MODULE Reputation_Game ----------------------
EXTENDS Naturals, Integers, FiniteSets

\* Reputation-game domain types (bounded finite vectors).
BeliefVectorType(nodes, maxRep) == [nodes -> 0..maxRep]

ReportProfileType(reporters, nodes, maxRep) ==
    [reporters -> BeliefVectorType(nodes, maxRep)]

CanonicalSelfReports(nodes, reputation) ==
    [r \in nodes |-> [n \in nodes |-> reputation[n]]]

MinRep(a, b) == IF a <= b THEN a ELSE b

SafeDiv(num, den) ==
    IF den = 0 THEN 0 ELSE num \div den

AbsDiff(a, b) ==
    IF a >= b THEN a - b ELSE b - a

MaxNatGame(S) ==
    IF S = {}
    THEN 0
    ELSE CHOOSE x \in S: \A y \in S: x >= y

\* TLAPS 1.5 does not support recursive operator definitions reliably.
\* We encode finite sums as cardinalities of tagged unit sets.
NatUnits(values, nodes) ==
    LET bound == MaxNatGame({values[n] : n \in nodes})
    IN {p \in (nodes \X (1..bound)) : p[2] <= values[p[1]]}

NatWeightedUnits(values, weights, nodes) ==
    LET bound == MaxNatGame({(values[n] * weights[n]) : n \in nodes})
    IN {p \in (nodes \X (1..bound)) : p[2] <= (values[p[1]] * weights[p[1]])}

SumNatVector(values, nodes) ==
    Cardinality(NatUnits(values, nodes))

SumNatWeighted(values, weights, nodes) ==
    Cardinality(NatWeightedUnits(values, weights, nodes))

SumReport(report, nodes) ==
    SumNatVector(report, nodes)

NormalizeReport(report, nodes, maxRep) ==
    LET total == SumReport(report, nodes)
        card == Cardinality(nodes)
        uniform == SafeDiv(maxRep, card)
    IN
        IF total = 0
        THEN [n \in nodes |-> uniform]
        ELSE [n \in nodes |-> MinRep(maxRep, SafeDiv(report[n] * maxRep, total))]

NormalizedProfile(profile, reporters, nodes, maxRep) ==
    [r \in reporters |-> NormalizeReport(profile[r], nodes, maxRep)]

SumNodeBelief(profile, reporters, node) ==
    SumNatVector([r \in reporters |-> profile[r][node]], reporters)

AggregateBeliefs(profile, reporters, nodes) ==
    [n \in nodes |-> SumNodeBelief(profile, reporters, n)]

SumIncoming(profile, rho, reporters, node, maxRep) ==
    LET contribs ==
            [r \in reporters |->
                SafeDiv(profile[r][node] * rho[r], IF maxRep = 0 THEN 1 ELSE maxRep)]
    IN
        SumNatVector(contribs, reporters)

BlendReputation(prior, ranked, alphaNum, alphaDen, maxRep, nodes) ==
    [n \in nodes |->
        MinRep(
            maxRep,
            SafeDiv(
                (alphaNum * ranked[n]) + ((alphaDen - alphaNum) * prior[n]),
                alphaDen
            )
        )
    ]

PageRankStep(profile, rho, reporters, nodes, alphaNum, alphaDen, maxRep) ==
    LET cardR == Cardinality(reporters)
        cardN == Cardinality(nodes)
        base == SafeDiv(maxRep, cardN)
    IN
        [n \in nodes |->
            LET incomingRaw == SumIncoming(profile, rho, reporters, n, maxRep)
                incoming == MinRep(maxRep, SafeDiv(incomingRaw, cardR))
                blended ==
                    SafeDiv(
                        (alphaNum * incoming) + ((alphaDen - alphaNum) * base),
                        alphaDen
                    )
            IN MinRep(maxRep, blended)
        ]

IteratePageRank(rounds, rho, profile, reporters, nodes, alphaNum, alphaDen, maxRep) ==
    IF rounds = 0 THEN
        rho
    ELSE
        LET r1 == PageRankStep(profile, rho, reporters, nodes, alphaNum, alphaDen, maxRep)
        IN
            IF rounds = 1 THEN r1
            ELSE PageRankStep(profile, r1, reporters, nodes, alphaNum, alphaDen, maxRep)

ReputationFromReports(
    profile,
    prior,
    reporters,
    nodes,
    alphaNum,
    alphaDen,
    maxRep
) ==
    LET normProfile == NormalizedProfile(profile, reporters, nodes, maxRep)
        cardN == Cardinality(nodes)
        base == SafeDiv(maxRep, cardN)
        rho0 == [n \in nodes |-> IF n \in DOMAIN prior THEN prior[n] ELSE base]
        rounds == IF cardN <= 1 THEN 1 ELSE 2
        rhoStar == IteratePageRank(rounds, rho0, normProfile, reporters, nodes, alphaNum, alphaDen, maxRep)
    IN BlendReputation(prior, rhoStar, alphaNum, alphaDen, maxRep, nodes)

\* ----- Utility / truthful-report abstraction (Bayesian game style) -----

SumReporterWeight(profile, reporters, node) ==
    SumNatVector([r \in reporters |-> profile[r][node]], reporters)

ContributionWeight(profile, globalReputation, reporters, node, maxRep) ==
    LET denom == SumReporterWeight(profile, reporters, node)
    IN SafeDiv(globalReputation[node] * (IF maxRep = 0 THEN 1 ELSE maxRep), denom)

SumWeighted(vector, weights, nodes) ==
    SumNatWeighted(vector, weights, nodes)

ReporterUtility(report, profile, globalReputation, reward, reporters, nodes, maxRep) ==
    LET phi == [n \in nodes |-> ContributionWeight(profile, globalReputation, reporters, n, maxRep)]
    IN SafeDiv(reward * SumWeighted(report, phi, nodes), IF maxRep = 0 THEN 1 ELSE maxRep)

SumAbsDiff(report, belief, nodes) ==
    SumNatVector([n \in nodes |-> AbsDiff(report[n], belief[n])], nodes)

ReportCost(report, belief, penalty, nodes) ==
    penalty * SumAbsDiff(report, belief, nodes)

ReporterPayoffGame(
    report,
    belief,
    profile,
    globalReputation,
    reward,
    penalty,
    reporters,
    nodes,
    maxRep
) ==
    ReporterUtility(report, profile, globalReputation, reward, reporters, nodes, maxRep)
        - ReportCost(report, belief, penalty, nodes)

\* Compatibility wrapper used by earlier abstractions.
ReporterPayoff(report, globalReputation, reward, nodes) ==
    reward * SumWeighted(report, globalReputation, nodes)

TruthfulReportShape(report, belief, nodes) ==
    \A n \in nodes: report[n] = belief[n]

TruthfulBestResponse(
    belief,
    statedReport,
    profile,
    globalReputation,
    reward,
    penalty,
    reporters,
    nodes,
    maxRep
) ==
    LET truthful == NormalizeReport(belief, nodes, maxRep)
        truthfulPayoff ==
            ReporterPayoffGame(
                truthful,
                belief,
                profile,
                globalReputation,
                reward,
                penalty,
                reporters,
                nodes,
                maxRep
            )
        statedPayoff ==
            ReporterPayoffGame(
                statedReport,
                belief,
                profile,
                globalReputation,
                reward,
                penalty,
                reporters,
                nodes,
                maxRep
            )
    IN truthfulPayoff >= statedPayoff

RankingRefines(raw, ranked, nodes) ==
    \A a, b \in nodes:
        raw[a] >= raw[b] => ranked[a] >= ranked[b]

=============================================================================
