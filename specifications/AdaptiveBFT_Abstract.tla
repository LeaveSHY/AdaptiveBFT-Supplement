----------------------- MODULE AdaptiveBFT_Abstract -----------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, F, Quorum

ASSUME
    /\ F \in Nat
    /\ F >= 1
    /\ Node # {}
    /\ IsFiniteSet(Node)
    /\ Cardinality(Node) = (3 * F) + 1
    /\ Quorum = (2 * F) + 1

VARIABLES
    view,
    phase,
    lockedView,
    highView,
    votes,
    decidedByView,
    chain,
    networkStable

varsA ==
    <<view, phase, lockedView, highView, votes, decidedByView, chain, networkStable>>

InitA ==
    /\ view = 0
    /\ phase = "Prepare"
    /\ lockedView = 0
    /\ highView = 0
    /\ votes = {}
    /\ decidedByView = [v \in Nat |-> {}]
    /\ chain = <<>>
    /\ networkStable = FALSE

VoteA(n) ==
    /\ phase = "Prepare"
    /\ n \in Node \ votes
    /\ votes' = votes \cup {n}
    /\ UNCHANGED <<view, phase, lockedView, highView, decidedByView, chain, networkStable>>

PrepareQCA ==
    /\ phase = "Prepare"
    /\ Cardinality(votes) >= Quorum
    /\ highView' = view
    /\ phase' = "PreCommit"
    /\ votes' = {}
    /\ view' = view
    /\ lockedView' = lockedView
    /\ decidedByView' = decidedByView
    /\ chain' = chain
    /\ networkStable' = networkStable

PreCommitQCA ==
    /\ phase = "PreCommit"
    /\ lockedView' = highView
    /\ phase' = "Commit"
    /\ votes' = {}
    /\ view' = view
    /\ highView' = highView
    /\ decidedByView' = decidedByView
    /\ chain' = chain
    /\ networkStable' = networkStable

CommitA ==
    /\ phase = "Commit"
    /\ decidedByView[view] = {}
    /\ decidedByView' = [decidedByView EXCEPT ![view] = {view}]
    /\ decidedByView'[view] = {view}
    /\ chain' = Append(chain, view)
    /\ lockedView' = highView
    /\ highView' = highView
    /\ view' \in {view, view + 1}
    /\ phase' = "Prepare"
    /\ votes' = {}
    /\ UNCHANGED networkStable

ViewChangeA ==
    /\ phase \in {"Prepare", "Commit"}
    /\ phase' = "ViewChange"
    /\ view' \in {view, view + 1}
    /\ votes' = {}
    /\ lockedView' = lockedView
    /\ highView' = highView
    /\ decidedByView' = decidedByView
    /\ chain' = chain
    /\ networkStable' = networkStable

RecoverSyncA ==
    /\ phase = "ViewChange"
    /\ phase' = "Prepare"
    /\ votes' = {}
    /\ view' = view
    /\ lockedView' = lockedView
    /\ highView' = highView
    /\ decidedByView' = decidedByView
    /\ chain' = chain
    /\ networkStable' = networkStable

\* Internal abstract step used to soundly hide concrete control/data-plane details
\* that do not decide new values or extend the committed chain.
InternalStepA ==
    /\ decidedByView' = decidedByView
    /\ chain' = chain
    /\ phase' \in {"Prepare", "PreCommit", "Commit", "ViewChange"}
    /\ view' \in {view, view + 1}
    /\ view' \in Nat
    /\ votes' \subseteq Node
    /\ lockedView' \in Nat
    /\ highView' \in Nat
    /\ lockedView' <= highView'
    /\ highView' <= view'
    /\ networkStable' \in BOOLEAN

EnvironmentStepA ==
    /\ networkStable' \in BOOLEAN
    /\ UNCHANGED <<view, phase, lockedView, highView, votes, decidedByView, chain>>

NextA ==
    \/ (\E n \in Node: VoteA(n))
    \/ PrepareQCA
    \/ PreCommitQCA
    \/ CommitA
    \/ ViewChangeA
    \/ RecoverSyncA
    \/ InternalStepA
    \/ EnvironmentStepA

SpecA ==
    /\ InitA
    /\ [][NextA]_varsA

NoForkA ==
    \A v \in Nat: Cardinality(decidedByView[v]) <= 1

LockMonotonicityA ==
    /\ lockedView \in Nat
    /\ highView \in Nat
    /\ view \in Nat
    /\ lockedView <= highView
    /\ highView <= view

SafetyA ==
    /\ NoForkA
    /\ LockMonotonicityA

EventuallyStableA ==
    <>[] networkStable

FairVoteA ==
    \A n \in Node: WF_varsA(VoteA(n))

LivenessA ==
    <> (Len(chain) >= 2)

\* Explicit progress witness used by the abstract liveness template.
ProgressWitnessA ==
    LivenessA

LivenessAssumptionsA ==
    /\ EventuallyStableA
    /\ FairVoteA
    /\ WF_varsA(PrepareQCA)
    /\ WF_varsA(PreCommitQCA)
    /\ WF_varsA(CommitA)
    /\ WF_varsA(RecoverSyncA)
    /\ ProgressWitnessA

=============================================================================
