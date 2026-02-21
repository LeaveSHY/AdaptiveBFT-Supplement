----------------------- MODULE AdaptiveBFT_Types -----------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

MsgType == {
    "Minor", "Full", "TeProposal", "ReProposal", "VProposal",
    "NPMessage", "SynMessage", "Vote"
}

ConsensusPhase == {
    "CollectMinor", "Prepare", "PreCommit", "Commit", "ViewChange"
}

SchedulerStateType == {"Monitor", "Sample", "Estimate", "Explore", "Deploy"}

NetworkConditionType == {"Stable", "Unstable"}

PriorityLevelType == {"High", "Mid", "Low"}

NilQC == [view |-> -1]

QC(view) == [view |-> view]

MinorMessage(view, abstract, qc, from) ==
    [type |-> "Minor", view |-> view, abstract |-> abstract, qc |-> qc, from |-> from]

FullMessage(view, txs, qc, parentView, from) ==
    [type |-> "Full", view |-> view, txs |-> txs, qc |-> qc, parentView |-> parentView, from |-> from]

TeProposal(view, alist, qc, parentView, from) ==
    [type |-> "TeProposal", view |-> view, alist |-> alist, qc |-> qc, parentView |-> parentView, from |-> from]

ReProposal(view, txs, qc, parentView, from) ==
    [type |-> "ReProposal", view |-> view, txs |-> txs, qc |-> qc, parentView |-> parentView, from |-> from]

VProposal(view, rv, qc, parentView, from) ==
    [type |-> "VProposal", view |-> view, rv |-> rv, qc |-> qc, parentView |-> parentView, from |-> from]

NPMessage(view, leader, ticket, strikes, proof, qc, from) ==
    [
        type |-> "NPMessage",
        view |-> view,
        leader |-> leader,
        ticket |-> ticket,
        strikes |-> strikes,
        proof |-> proof,
        qc |-> qc,
        from |-> from
    ]

SynMessage(view, leader, rv, qc, from) ==
    [type |-> "SynMessage", view |-> view, leader |-> leader, rv |-> rv, qc |-> qc, from |-> from]

VoteMessage(view, phase, voter) ==
    [type |-> "Vote", view |-> view, phase |-> phase, voter |-> voter]

Block(view, txs, parentView, proposer) ==
    [view |-> view, txs |-> txs, parentView |-> parentView, proposer |-> proposer]

MinNat(a, b) == IF a <= b THEN a ELSE b

SamePrefix(s1, s2) ==
    LET m == MinNat(Len(s1), Len(s2))
    IN \A i \in 1..m: s1[i] = s2[i]

=============================================================================
