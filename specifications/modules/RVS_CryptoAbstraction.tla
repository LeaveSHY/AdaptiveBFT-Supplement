-------------------- MODULE RVS_CryptoAbstraction --------------------
EXTENDS Naturals, FiniteSets

\* Finite ticket domain used by the cryptographic sortition abstraction.
TicketBound(maxRep) == (maxRep + 1) * (maxRep + 2)

VRFTicket(reputation, n, view, maxRep) ==
    LET bound == TicketBound(maxRep)
    IN (reputation[n] + (view % bound)) % bound

VRFProof(n, view, ticket, strikes, kappa) ==
    [node |-> n, view |-> view, ticket |-> ticket, strikes |-> strikes, kappa |-> kappa]

VRFVerify(n, view, ticket, strikes, kappa, proof) ==
    proof = VRFProof(n, view, ticket, strikes, kappa)

ScaledPassThreshold(reputation, n, totalWeight, maxRep) ==
    LET bound == TicketBound(maxRep)
        denom == IF totalWeight = 0 THEN 1 ELSE totalWeight
    IN (reputation[n] * bound) \div denom

SortitionStrikes(reputation, n, view, totalWeight, kappa, maxRep) ==
    LET bound == TicketBound(maxRep)
        draws == IF kappa = 0 THEN 1 ELSE kappa
        ticket == VRFTicket(reputation, n, view, maxRep)
        passTh == ScaledPassThreshold(reputation, n, totalWeight, maxRep)
        passingDraws ==
            {
                j \in 1..draws:
                    ((ticket + (j * (reputation[n] + view + 1))) % bound) < passTh
            }
    IN Cardinality(passingDraws)

SortitionResult(reputation, n, view, totalWeight, kappa, maxRep) ==
    LET ticket == VRFTicket(reputation, n, view, maxRep)
        strikes == SortitionStrikes(reputation, n, view, totalWeight, kappa, maxRep)
    IN
        [
            ticket |-> ticket,
            strikes |-> strikes,
            proof |-> VRFProof(n, view, ticket, strikes, IF kappa = 0 THEN 1 ELSE kappa)
        ]

SortitionVerify(reputation, n, view, totalWeight, kappa, maxRep, result) ==
    LET draws == IF kappa = 0 THEN 1 ELSE kappa
        expectedTicket == VRFTicket(reputation, n, view, maxRep)
        expectedStrikes == SortitionStrikes(reputation, n, view, totalWeight, draws, maxRep)
        expectedProof == VRFProof(n, view, expectedTicket, expectedStrikes, draws)
    IN
        /\ result.ticket = expectedTicket
        /\ result.strikes = expectedStrikes
        /\ result.proof = expectedProof
        /\ VRFVerify(n, view, result.ticket, result.strikes, draws, result.proof)

MaxNat(S) ==
    IF S = {}
    THEN 0
    ELSE CHOOSE x \in S: \A y \in S: x >= y

SortitionPriority(reputation, n, view, totalWeight, kappa, maxRep) ==
    LET result == SortitionResult(reputation, n, view, totalWeight, kappa, maxRep)
        bound == TicketBound(maxRep)
    IN
        (result.strikes * (maxRep + 1) * bound)
            + (reputation[n] * bound)
            + ((bound - 1) - result.ticket)

ValidWinners(reputation, candidates, view, totalWeight, kappa, maxRep) ==
    LET draws == IF kappa = 0 THEN 1 ELSE kappa
        passed ==
            {
                n \in candidates:
                    LET result == SortitionResult(reputation, n, view, totalWeight, draws, maxRep)
                    IN
                        /\ result.strikes > 0
                        /\ SortitionVerify(reputation, n, view, totalWeight, draws, maxRep, result)
            }
        eligible == IF passed # {} THEN passed ELSE candidates
        bestScore ==
            MaxNat(
                {
                    SortitionPriority(reputation, n, view, totalWeight, draws, maxRep) : n \in eligible
                }
            )
    IN
        {
            n \in eligible:
                /\ SortitionPriority(reputation, n, view, totalWeight, draws, maxRep) = bestScore
                /\ LET result == SortitionResult(reputation, n, view, totalWeight, draws, maxRep)
                   IN SortitionVerify(reputation, n, view, totalWeight, draws, maxRep, result)
        }

PickWinner(reputation, candidates, view, totalWeight, kappa, maxRep) ==
    CHOOSE n \in ValidWinners(reputation, candidates, view, totalWeight, kappa, maxRep): TRUE

\* Basic sanity property for the abstract VRF object.
THEOREM VRFRoundTrip ==
    \A n, view, ticket, strikes, kappa:
        VRFVerify(
            n,
            view,
            ticket,
            strikes,
            kappa,
            VRFProof(n, view, ticket, strikes, kappa)
        )

=============================================================================
