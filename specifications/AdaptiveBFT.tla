-------------------------- MODULE AdaptiveBFT --------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC,
        AdaptiveBFT_Types, AVC_RVS, APS_Scheduler, APS_DecoupledPipeline, Mempool

CONSTANTS
    F,
    Node,
    Tx,
    ValidTx,
    HotTx,
    WarmTx,
    Quorum,
    MaxView,
    MaxBatchSize,
    MaxPipelineDepth,
    MaxTimeout,
    MaxTxPerBlock,
    MaxReputation,
    RepThreshold,
    AgingThreshold,
    MaxAge,
    DecayNumerator,
    DecayDenominator

ASSUME
    /\ F \in Nat
    /\ F >= 1
    /\ Node # {}
    /\ Cardinality(Node) = (3 * F) + 1
    /\ Tx # {}
    /\ ValidTx \subseteq Tx
    /\ HotTx \subseteq Tx
    /\ WarmTx \subseteq Tx
    /\ Quorum = (2 * F) + 1
    /\ MaxView \in Nat
    /\ MaxView >= 1
    /\ MaxBatchSize \in Nat
    /\ MaxBatchSize >= 1
    /\ MaxPipelineDepth \in Nat
    /\ MaxPipelineDepth >= 1
    /\ MaxTimeout \in Nat
    /\ MaxTimeout >= 2
    /\ MaxTxPerBlock \in Nat
    /\ MaxTxPerBlock >= 1
    /\ MaxReputation \in Nat
    /\ MaxReputation >= 2
    /\ RepThreshold \in 0..MaxReputation
    /\ AgingThreshold \in Nat
    /\ MaxAge \in Nat
    /\ MaxAge >= AgingThreshold
    /\ DecayDenominator \in Nat \ {0}
    /\ DecayNumerator \in 0..DecayDenominator

VARIABLE st

vars == <<st>>

Min2(a, b) == IF a <= b THEN a ELSE b

NPMessageHasValidSortition(np, reputation) ==
    RVSVerifyPrimary(
        reputation,
        RepThreshold,
        np.view,
        np.leader,
        np.ticket,
        np.strikes,
        np.proof
    )

ConfigType == APSConfigType(MaxBatchSize, MaxPipelineDepth, MaxTimeout)

QCType == {[view |-> v] : v \in -1..MaxView}

TeProposalType == {
    [
        type |-> "TeProposal",
        view |-> v,
        alist |-> a,
        qc |-> qc,
        parentView |-> p,
        from |-> n
    ] :
        v \in 0..MaxView,
        a \in SUBSET Tx,
        qc \in QCType,
        p \in -1..MaxView,
        n \in Node
}

FullProposalType == {
    [
        type |-> "Full",
        view |-> v,
        txs |-> t,
        qc |-> qc,
        parentView |-> p,
        from |-> n
    ] :
        v \in 0..MaxView,
        t \in SUBSET Tx,
        qc \in QCType,
        p \in -1..MaxView,
        n \in Node
}

VProposalType == {
    [
        type |-> "VProposal",
        view |-> v,
        rv |-> rv,
        qc |-> qc,
        parentView |-> p,
        from |-> n
    ] :
        v \in 0..MaxView,
        rv \in [Node -> 0..MaxReputation],
        qc \in QCType,
        p \in -1..MaxView,
        n \in Node
}

NPMessageType == {
    [
        type |-> "NPMessage",
        view |-> v,
        leader |-> l,
        ticket |-> ticket,
        strikes |-> strikes,
        proof |-> VRFProof(l, v, ticket, strikes, k),
        qc |-> qc,
        from |-> n
    ] :
        v \in 0..MaxView,
        l \in Node,
        ticket \in 0..(TicketBound(MaxReputation) - 1),
        strikes \in 0..Cardinality(Node),
        k \in 1..Cardinality(Node),
        qc \in QCType,
        n \in Node
}

SynMessageType == {
    [
        type |-> "SynMessage",
        view |-> v,
        leader |-> l,
        rv |-> rv,
        qc |-> qc,
        from |-> n
    ] :
        v \in 0..MaxView,
        l \in Node,
        rv \in [Node -> 0..MaxReputation],
        qc \in QCType,
        n \in Node
}

BlockType == {
    [
        view |-> v,
        txs |-> t,
        parentView |-> p,
        proposer |-> n
    ] :
        v \in 0..MaxView,
        t \in SUBSET Tx,
        p \in -1..MaxView,
        n \in Node
}

NoTeProposal ==
    [
        type |-> "NoTeProposal",
        view |-> 0,
        alist |-> {},
        qc |-> NilQC,
        parentView |-> -1,
        from |-> CHOOSE n \in Node: TRUE
    ]

NoFullProposal ==
    [
        type |-> "NoFullProposal",
        view |-> 0,
        txs |-> {},
        qc |-> NilQC,
        parentView |-> -1,
        from |-> CHOOSE n \in Node: TRUE
    ]

NoVProposal ==
    [
        type |-> "NoVProposal",
        view |-> 0,
        rv |-> [n \in Node |-> 0],
        qc |-> NilQC,
        parentView |-> -1,
        from |-> CHOOSE n \in Node: TRUE
    ]

NoNPMessage ==
    [
        type |-> "NoNPMessage",
        view |-> 0,
        leader |-> CHOOSE n \in Node: TRUE,
        ticket |-> 0,
        strikes |-> 0,
        proof |-> [
            node |-> CHOOSE n \in Node: TRUE,
            view |-> 0,
            ticket |-> 0,
            strikes |-> 0,
            kappa |-> 1
        ],
        qc |-> NilQC,
        from |-> CHOOSE n \in Node: TRUE
    ]

NoSynMessage ==
    [
        type |-> "NoSynMessage",
        view |-> 0,
        leader |-> CHOOSE n \in Node: TRUE,
        rv |-> [n \in Node |-> 0],
        qc |-> NilQC,
        from |-> CHOOSE n \in Node: TRUE
    ]

DefaultConfig == [batchSize |-> 1, pipelineDepth |-> 1, timeout |-> 1]

Init ==
    LET p0 == CHOOSE n \in Node: TRUE
        rep0 == [n \in Node |-> MaxReputation \div 2]
    IN
    /\ st = [
            view |-> 0,
            phase |-> "CollectMinor",
            primary |-> p0,
            highQC |-> NilQC,
            lockedQC |-> NilQC,
            teProposal |-> NoTeProposal,
            fullProposal |-> NoFullProposal,
            vProposal |-> NoVProposal,
            npMessage |-> NoNPMessage,
            synMessage |-> NoSynMessage,
            prepareVotes |-> {},
            precommitVotes |-> {},
            commitVotes |-> {},
            timeoutVotes |-> {},
            candidateReplicas |-> Node,
            tentativePrimary |-> p0,
            npConfirms |-> {},
            synAcks |-> {},
            rawMempool |-> {},
            validatedMempool |-> {},
            disseminationBuffer |-> {},
            orderingBuffer |-> {},
            executionBuffer |-> {},
            orderedPool |-> {},
            computeQueued |-> {},
            computeReady |-> {},
            txAge |-> [tx \in Tx |-> 0],
            reputation |-> rep0,
            chain |-> <<>>,
            localChain |-> [n \in Node |-> <<>>],
            decidedByView |-> [v \in 0..MaxView |-> {}],
            activeConfig |-> DefaultConfig,
            pendingConfig |-> DefaultConfig,
            schedulerState |-> "Monitor",
            networkCondition |-> "Stable",
            stageTimer |-> 0,
            inFlight |-> 0
        ]

TypeOK ==
    /\ st.view \in 0..MaxView
    /\ st.phase \in ConsensusPhase
    /\ st.primary \in Node
    /\ st.highQC \in QCType
    /\ st.lockedQC \in QCType
    /\ (st.teProposal = NoTeProposal \/ st.teProposal \in TeProposalType)
    /\ (st.fullProposal = NoFullProposal
        \/ st.fullProposal \in FullProposalType)
    /\ (st.vProposal = NoVProposal \/ st.vProposal \in VProposalType)
    /\ (st.npMessage = NoNPMessage \/ st.npMessage \in NPMessageType)
    /\ (st.synMessage = NoSynMessage \/ st.synMessage \in SynMessageType)
    /\ st.prepareVotes \subseteq Node
    /\ st.precommitVotes \subseteq Node
    /\ st.commitVotes \subseteq Node
    /\ st.timeoutVotes \subseteq Node
    /\ st.candidateReplicas \subseteq Node
    /\ st.candidateReplicas # {}
    /\ st.tentativePrimary \in Node
    /\ st.npConfirms \subseteq Node
    /\ st.synAcks \subseteq Node
    /\ st.rawMempool \subseteq Tx
    /\ st.validatedMempool \subseteq Tx
    /\ st.disseminationBuffer \subseteq Tx
    /\ st.orderingBuffer \subseteq Tx
    /\ st.executionBuffer \subseteq Tx
    /\ st.orderedPool \subseteq Tx
    /\ st.computeQueued \subseteq Tx
    /\ st.computeReady \subseteq Tx
    /\ st.txAge \in [Tx -> 0..MaxAge]
    /\ st.reputation \in [Node -> 0..MaxReputation]
    /\ \A i \in 1..Len(st.chain): st.chain[i] \in BlockType
    /\ \A n \in Node:
        \A i \in 1..Len(st.localChain[n]): st.localChain[n][i] \in BlockType
    /\ st.decidedByView \in [0..MaxView -> SUBSET (SUBSET Tx)]
    /\ st.activeConfig \in ConfigType
    /\ st.pendingConfig \in ConfigType
    /\ st.schedulerState \in SchedulerStateType
    /\ st.networkCondition \in NetworkConditionType
    /\ st.stageTimer \in 0..MaxTimeout
    /\ st.inFlight \in 0..MaxPipelineDepth

\* Scalable typing profile used by larger-node TLC sanity runs.
\* This avoids extensional membership in very large constructor sets
\* (e.g., NPMessageType) while preserving field-level type discipline.
TypeOKLite ==
    /\ st.view \in 0..MaxView
    /\ st.phase \in ConsensusPhase
    /\ st.primary \in Node
    /\ st.highQC.view \in -1..MaxView
    /\ st.lockedQC.view \in -1..MaxView
    /\ st.teProposal.type \in {"NoTeProposal", "TeProposal"}
    /\ st.teProposal.view \in 0..MaxView
    /\ st.teProposal.alist \subseteq Tx
    /\ st.teProposal.qc.view \in -1..MaxView
    /\ st.teProposal.parentView \in -1..MaxView
    /\ st.teProposal.from \in Node
    /\ st.fullProposal.type \in {"NoFullProposal", "Full"}
    /\ st.fullProposal.view \in 0..MaxView
    /\ st.fullProposal.txs \subseteq Tx
    /\ st.fullProposal.qc.view \in -1..MaxView
    /\ st.fullProposal.parentView \in -1..MaxView
    /\ st.fullProposal.from \in Node
    /\ st.vProposal.type \in {"NoVProposal", "VProposal"}
    /\ st.vProposal.view \in 0..MaxView
    /\ st.vProposal.qc.view \in -1..MaxView
    /\ st.vProposal.parentView \in -1..MaxView
    /\ st.vProposal.from \in Node
    /\ DOMAIN st.vProposal.rv = Node
    /\ \A n \in Node: st.vProposal.rv[n] \in 0..MaxReputation
    /\ st.npMessage.type \in {"NoNPMessage", "NPMessage"}
    /\ st.npMessage.view \in 0..MaxView
    /\ st.npMessage.leader \in Node
    /\ st.npMessage.ticket \in 0..(TicketBound(MaxReputation) - 1)
    /\ st.npMessage.strikes \in 0..Cardinality(Node)
    /\ st.npMessage.qc.view \in -1..MaxView
    /\ st.npMessage.from \in Node
    /\ st.synMessage.type \in {"NoSynMessage", "SynMessage"}
    /\ st.synMessage.view \in 0..MaxView
    /\ st.synMessage.leader \in Node
    /\ st.synMessage.qc.view \in -1..MaxView
    /\ st.synMessage.from \in Node
    /\ DOMAIN st.synMessage.rv = Node
    /\ \A n \in Node: st.synMessage.rv[n] \in 0..MaxReputation
    /\ st.prepareVotes \subseteq Node
    /\ st.precommitVotes \subseteq Node
    /\ st.commitVotes \subseteq Node
    /\ st.timeoutVotes \subseteq Node
    /\ st.npConfirms \subseteq Node
    /\ st.synAcks \subseteq Node
    /\ st.candidateReplicas \subseteq Node
    /\ st.candidateReplicas # {}
    /\ st.tentativePrimary \in Node
    /\ st.rawMempool \subseteq Tx
    /\ st.validatedMempool \subseteq Tx
    /\ st.disseminationBuffer \subseteq Tx
    /\ st.orderingBuffer \subseteq Tx
    /\ st.executionBuffer \subseteq Tx
    /\ st.orderedPool \subseteq Tx
    /\ st.computeQueued \subseteq Tx
    /\ st.computeReady \subseteq Tx
    /\ DOMAIN st.txAge = Tx
    /\ \A tx \in Tx: st.txAge[tx] \in 0..MaxAge
    /\ DOMAIN st.reputation = Node
    /\ \A n \in Node: st.reputation[n] \in 0..MaxReputation
    /\ \A i \in 1..Len(st.chain):
        /\ st.chain[i].view \in 0..MaxView
        /\ st.chain[i].txs \subseteq Tx
        /\ st.chain[i].parentView \in -1..MaxView
        /\ st.chain[i].proposer \in Node
    /\ DOMAIN st.localChain = Node
    /\ \A n \in Node:
        \A i \in 1..Len(st.localChain[n]):
            /\ st.localChain[n][i].view \in 0..MaxView
            /\ st.localChain[n][i].txs \subseteq Tx
            /\ st.localChain[n][i].parentView \in -1..MaxView
            /\ st.localChain[n][i].proposer \in Node
    /\ DOMAIN st.decidedByView = 0..MaxView
    /\ \A v \in 0..MaxView:
        \A s \in st.decidedByView[v]: s \subseteq Tx
    /\ st.activeConfig.timeout \in 1..MaxTimeout
    /\ st.activeConfig.batchSize \in 1..MaxBatchSize
    /\ st.activeConfig.pipelineDepth \in 1..MaxPipelineDepth
    /\ st.pendingConfig.timeout \in 1..MaxTimeout
    /\ st.pendingConfig.batchSize \in 1..MaxBatchSize
    /\ st.pendingConfig.pipelineDepth \in 1..MaxPipelineDepth
    /\ st.schedulerState \in SchedulerStateType
    /\ st.networkCondition \in NetworkConditionType
    /\ st.stageTimer \in 0..MaxTimeout
    /\ st.inFlight \in 0..MaxPipelineDepth

InjectTx(tx) ==
    /\ tx \in Tx
    /\ tx \notin st.rawMempool \cup st.validatedMempool
    /\ st' = [st EXCEPT !.rawMempool = @ \cup {tx}]

PreValidate(tx) ==
    /\ tx \in st.rawMempool
    /\ st' =
        IF tx \in ValidTx
        THEN [
            st EXCEPT
                !.rawMempool = @ \ {tx},
                !.validatedMempool = @ \cup {tx},
                !.txAge = [@ EXCEPT ![tx] = 0]
        ]
        ELSE [
            st EXCEPT
                !.rawMempool = @ \ {tx},
                !.txAge = [@ EXCEPT ![tx] = 0]
        ]

AgeTx(tx) ==
    /\ tx \in st.validatedMempool
    /\ st' = [st EXCEPT !.txAge = AgeMapBump(@, tx, MaxAge)]

DispatchToDissemination ==
    /\ st.phase = "CollectMinor"
    /\ st.orderedPool = {}
    /\ st.validatedMempool # {}
    /\ \E moved \in SUBSET (st.validatedMempool \ st.disseminationBuffer):
        /\ moved # {}
        /\ Cardinality(moved) <= st.activeConfig.batchSize
        /\ st' =
            [st EXCEPT
                !.disseminationBuffer = @ \cup moved]

PromoteToOrdering ==
    /\ st.phase = "CollectMinor"
    /\ st.orderedPool = {}
    /\ st.disseminationBuffer # {}
    /\ \E moved \in SUBSET (st.disseminationBuffer \ st.orderingBuffer):
        /\ moved # {}
        /\ Cardinality(moved) <= st.activeConfig.batchSize
        /\ st' =
            [st EXCEPT
                !.orderingBuffer = @ \cup moved,
                !.computeQueued = @ \cup moved,
                !.computeReady = @ \cup moved]

PromoteToExecution ==
    /\ st.phase = "CollectMinor"
    /\ st.orderedPool = {}
    /\ st.computeReady # {}
    /\ \E moved \in SUBSET ((st.orderingBuffer \ st.executionBuffer) \cap st.computeReady):
        /\ moved # {}
        /\ Cardinality(moved) <= st.activeConfig.batchSize
        /\ st' =
            [st EXCEPT
                !.executionBuffer = @ \cup moved]

PreOrder ==
    /\ st.phase = "CollectMinor"
    /\ st.orderedPool = {}
    /\ st.validatedMempool # {}
    /\ LET limit == Min2(st.activeConfig.batchSize, MaxTxPerBlock)
           source ==
            IF st.executionBuffer # {}
            THEN st.executionBuffer
            ELSE
                IF st.computeReady # {}
                THEN st.computeReady
                ELSE st.validatedMempool
           front ==
            PriorityFront(
                source,
                st.txAge,
                HotTx,
                WarmTx,
                AgingThreshold
            )
           chosen ==
            SelectBatch(
                front,
                st.txAge,
                HotTx,
                WarmTx,
                AgingThreshold,
                limit
            )
       IN
       /\ chosen # {}
       /\ st' =
            [st EXCEPT
                !.orderedPool = chosen,
                !.disseminationBuffer = @ \ chosen,
                !.orderingBuffer = @ \ chosen,
                !.executionBuffer = @ \ chosen,
                !.computeQueued = @ \ chosen,
                !.computeReady = @ \ chosen]

GenerateTentativeProposal ==
    /\ st.phase = "CollectMinor"
    /\ st.orderedPool # {}
    /\ st.inFlight < st.activeConfig.pipelineDepth
    /\ st.primary \in CandidateReplicas(st.reputation, RepThreshold)
    /\ (st.view < MaxView \/ st.decidedByView[st.view] = {})
    /\ st' =
        LET te ==
            TeProposal(
                st.view,
                st.orderedPool,
                st.highQC,
                st.highQC.view,
                st.primary
            )
        IN
        [st EXCEPT
            !.teProposal = te,
            !.fullProposal = NoFullProposal,
            !.phase = "Prepare",
            !.prepareVotes = {},
            !.precommitVotes = {},
            !.commitVotes = {},
            !.timeoutVotes = {},
            !.vProposal = NoVProposal,
            !.npMessage = NoNPMessage,
            !.synMessage = NoSynMessage,
            !.npConfirms = {},
            !.synAcks = {},
            !.stageTimer = 0,
            !.inFlight = @ + 1]

RecoverFullProposal ==
    /\ st.phase = "Prepare"
    /\ st.teProposal # NoTeProposal
    /\ LET recovered ==
            RecoverTransactions(
                st.teProposal.alist,
                st.validatedMempool
            )
           full ==
            FullMessage(
                st.view,
                recovered,
                st.teProposal.qc,
                st.teProposal.parentView,
                st.primary
            )
       IN
       /\ recovered # {}
       /\ st' = [st EXCEPT !.fullProposal = full]

PrepareVote(n) ==
    /\ st.phase = "Prepare"
    /\ st.fullProposal # NoFullProposal
    /\ n \in Node \ st.prepareVotes
    /\ st' = [st EXCEPT !.prepareVotes = @ \cup {n}]

PrepareQC ==
    /\ st.phase = "Prepare"
    /\ Cardinality(st.prepareVotes) >= Quorum
    /\ st' =
        [st EXCEPT
            !.highQC = QC(st.view),
            !.phase = "PreCommit",
            !.precommitVotes = {},
            !.stageTimer = 0]

PreCommitVote(n) ==
    /\ st.phase = "PreCommit"
    /\ n \in Node \ st.precommitVotes
    /\ st' = [st EXCEPT !.precommitVotes = @ \cup {n}]

PreCommitQC ==
    /\ st.phase = "PreCommit"
    /\ Cardinality(st.precommitVotes) >= Quorum
    /\ st' =
        [st EXCEPT
            !.lockedQC = st.highQC,
            !.phase = "Commit",
            !.commitVotes = {},
            !.stageTimer = 0]

CommitVote(n) ==
    /\ st.phase = "Commit"
    /\ n \in Node \ st.commitVotes
    /\ st' = [st EXCEPT !.commitVotes = @ \cup {n}]

DecideBlock ==
    /\ st.phase = "Commit"
    /\ st.fullProposal # NoFullProposal
    /\ Cardinality(st.commitVotes) >= Quorum
    /\ LET block ==
            Block(
                st.view,
                st.fullProposal.txs,
                st.fullProposal.parentView,
                st.primary
            )
           rep1 ==
            DecayUpdate(
                st.reputation,
                st.primary,
                TRUE,
                MaxReputation,
                DecayNumerator,
                DecayDenominator
            )
           nextView == IF st.view < MaxView THEN st.view + 1 ELSE st.view
           nextPrimary == RVSSelectPrimary(rep1, RepThreshold, nextView)
       IN
       /\ st' = [st EXCEPT
                !.chain = Append(@, block),
                !.localChain =
                    [n \in Node |-> Append(st.localChain[n], block)],
                !.decidedByView =
                    [@ EXCEPT ![st.view] = @ \cup {st.fullProposal.txs}],
                !.reputation = rep1,
                !.view = nextView,
                !.primary = nextPrimary,
                !.phase = "CollectMinor",
                !.highQC = QC(st.view),
                !.lockedQC = QC(st.view),
                !.teProposal = NoTeProposal,
                !.fullProposal = NoFullProposal,
                !.vProposal = NoVProposal,
                !.npMessage = NoNPMessage,
                !.synMessage = NoSynMessage,
                !.prepareVotes = {},
                !.precommitVotes = {},
                !.commitVotes = {},
                !.timeoutVotes = {},
                !.candidateReplicas =
                    CandidateReplicas(rep1, RepThreshold),
                !.tentativePrimary = nextPrimary,
                !.npConfirms = {},
                !.synAcks = {},
                !.rawMempool = @ \ st.fullProposal.txs,
                !.validatedMempool = @ \ st.fullProposal.txs,
                !.disseminationBuffer = @ \ st.fullProposal.txs,
                !.orderingBuffer = @ \ st.fullProposal.txs,
                !.executionBuffer = @ \ st.fullProposal.txs,
                !.orderedPool = {},
                !.computeQueued = @ \ st.fullProposal.txs,
                !.computeReady = @ \ st.fullProposal.txs,
                !.txAge = ResetAges(@, st.fullProposal.txs),
                !.stageTimer = 0,
                !.inFlight = IF @ > 0 THEN @ - 1 ELSE 0]

Tick ==
    /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
    /\ st.stageTimer < MaxTimeout
    /\ st' = [st EXCEPT !.stageTimer = @ + 1]

CastTimeoutVote(n) ==
    /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
    /\ st.stageTimer >= st.activeConfig.timeout
    /\ n \in Node \ st.timeoutVotes
    /\ st' = [st EXCEPT !.timeoutVotes = @ \cup {n}]

StartViewChange ==
    /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
    /\ Cardinality(st.timeoutVotes) >= Quorum
    /\ LET rep1 ==
            DecayUpdate(
                st.reputation,
                st.primary,
                FALSE,
                MaxReputation,
                DecayNumerator,
                DecayDenominator
            )
           cand == CandidateReplicas(rep1, RepThreshold)
           leader == RVSSelectPrimary(rep1, RepThreshold, st.view)
           vp ==
            VProposal(
                st.view,
                rep1,
                st.lockedQC,
                st.lockedQC.view,
                st.primary
            )
       IN
       /\ st' = [st EXCEPT
                !.phase = "ViewChange",
                !.reputation = rep1,
                !.candidateReplicas = cand,
                !.tentativePrimary = leader,
                !.vProposal = vp,
                !.npMessage = NoNPMessage,
                !.synMessage = NoSynMessage,
                !.teProposal = NoTeProposal,
                !.fullProposal = NoFullProposal,
                !.prepareVotes = {},
                !.precommitVotes = {},
                !.commitVotes = {},
                !.timeoutVotes = {},
                !.disseminationBuffer = {},
                !.orderingBuffer = {},
                !.executionBuffer = {},
                !.orderedPool = {},
                !.computeQueued = {},
                !.computeReady = {},
                !.npConfirms = {},
                !.synAcks = {},
                !.stageTimer = 0,
                !.inFlight = 0]

BroadcastNP ==
    /\ st.phase = "ViewChange"
    /\ st.vProposal # NoVProposal
    /\ st.npMessage = NoNPMessage
    /\ st.tentativePrimary \in st.candidateReplicas
    /\ st' =
        LET evidence ==
            RVSPrimaryEvidence(
                st.reputation,
                RepThreshold,
                st.view,
                st.tentativePrimary
            )
            np ==
            NPMessage(
                st.view,
                st.tentativePrimary,
                evidence.ticket,
                evidence.strikes,
                evidence.proof,
                st.highQC,
                st.tentativePrimary
            )
        IN
        [st EXCEPT
            !.npMessage = np,
            !.npConfirms = {}]

ConfirmNewPrimary(n) ==
    /\ st.phase = "ViewChange"
    /\ st.npMessage # NoNPMessage
    /\ NPMessageHasValidSortition(st.npMessage, st.reputation)
    /\ n \in Node \ st.npConfirms
    /\ st' = [st EXCEPT !.npConfirms = @ \cup {n}]

BroadcastSyn ==
    /\ st.phase = "ViewChange"
    /\ st.npMessage # NoNPMessage
    /\ NPMessageHasValidSortition(st.npMessage, st.reputation)
    /\ Cardinality(st.npConfirms) >= Quorum
    /\ st.synMessage = NoSynMessage
    /\ st' =
        LET syn ==
            SynMessage(
                st.view,
                st.npMessage.leader,
                st.reputation,
                st.highQC,
                st.npMessage.leader
            )
        IN
        [st EXCEPT
            !.synMessage = syn,
            !.synAcks = {}]

SendSynAck(n) ==
    /\ st.phase = "ViewChange"
    /\ st.synMessage # NoSynMessage
    /\ st.synMessage.rv = st.reputation
    /\ n \in Node \ st.synAcks
    /\ st' = [st EXCEPT !.synAcks = @ \cup {n}]

CompleteViewChange ==
    /\ st.phase = "ViewChange"
    /\ st.npMessage # NoNPMessage
    /\ st.synMessage # NoSynMessage
    /\ Cardinality(st.synAcks) >= Quorum
    /\ LET nextView == IF st.view < MaxView THEN st.view + 1 ELSE st.view
       IN
       /\ st' = [st EXCEPT
                !.view = nextView,
                !.primary = st.npMessage.leader,
                !.phase = "CollectMinor",
                !.teProposal = NoTeProposal,
                !.fullProposal = NoFullProposal,
                !.vProposal = NoVProposal,
                !.npMessage = NoNPMessage,
                !.synMessage = NoSynMessage,
                !.prepareVotes = {},
                !.precommitVotes = {},
                !.commitVotes = {},
                !.timeoutVotes = {},
                !.disseminationBuffer = {},
                !.orderingBuffer = {},
                !.executionBuffer = {},
                !.orderedPool = {},
                !.computeQueued = {},
                !.computeReady = {},
                !.candidateReplicas =
                    CandidateReplicas(st.reputation, RepThreshold),
                !.npConfirms = {},
                !.synAcks = {},
                !.stageTimer = 0]

DetectAnomaly ==
    /\ st.schedulerState = "Monitor"
    /\ st.phase = "CollectMinor"
    /\ \E nc \in NetworkConditionType:
        /\ st' =
            [st EXCEPT
                !.networkCondition = nc,
                !.schedulerState = "Sample"]

SampleGrid ==
    /\ st.schedulerState = "Sample"
    /\ st.phase = "CollectMinor"
    /\ \E cfg \in ConfigType:
        /\ cfg.timeout = st.activeConfig.timeout
        /\ st' =
            [st EXCEPT
                !.pendingConfig = cfg,
                !.schedulerState = "Estimate"]

EstimateGrid ==
    /\ st.schedulerState = "Estimate"
    /\ st.phase = "CollectMinor"
    /\ LET tunedTimeout ==
            RefineTimeout(
                st.pendingConfig.timeout,
                st.networkCondition,
                MaxTimeout
            )
           tunedCfg == [st.pendingConfig EXCEPT !.timeout = tunedTimeout]
       IN
       /\ tunedCfg \in ConfigType
       /\ st' =
            [st EXCEPT
                !.pendingConfig = tunedCfg,
                !.schedulerState = "Explore"]

ExploreGrid ==
    /\ st.schedulerState = "Explore"
    /\ st.phase = "CollectMinor"
    /\ \E candidate \in ConfigType:
        /\ ConfigSatisfiesNetwork(candidate, st.networkCondition)
        /\ LET chosen ==
                ChooseBetterConfig(
                    st.pendingConfig,
                    candidate,
                    st.networkCondition
                )
           IN st' =
                [st EXCEPT
                    !.pendingConfig = chosen,
                    !.schedulerState = "Deploy"]

DeployConfig ==
    /\ st.schedulerState = "Deploy"
    /\ st.phase = "CollectMinor"
    /\ st.pendingConfig \in ConfigType
    /\ ConfigSatisfiesNetwork(st.pendingConfig, st.networkCondition)
    /\ st' =
        [st EXCEPT
            !.activeConfig = st.pendingConfig,
            !.schedulerState = "Monitor"]

InjectTxStep == \E tx \in Tx: InjectTx(tx)
PreValidateStep == \E tx \in st.rawMempool: PreValidate(tx)
AgeTxStep == \E tx \in st.validatedMempool: AgeTx(tx)
PrepareVoteStep == \E n \in Node: PrepareVote(n)
PreCommitVoteStep == \E n \in Node: PreCommitVote(n)
CommitVoteStep == \E n \in Node: CommitVote(n)
CastTimeoutVoteStep == \E n \in Node: CastTimeoutVote(n)
ConfirmNewPrimaryStep == \E n \in Node: ConfirmNewPrimary(n)
SendSynAckStep == \E n \in Node: SendSynAck(n)

ConsensusNext ==
    \/ InjectTxStep
    \/ PreValidateStep
    \/ AgeTxStep
    \/ DispatchToDissemination
    \/ PromoteToOrdering
    \/ PromoteToExecution
    \/ PreOrder
    \/ GenerateTentativeProposal
    \/ RecoverFullProposal
    \/ PrepareVoteStep
    \/ PrepareQC
    \/ PreCommitVoteStep
    \/ PreCommitQC
    \/ CommitVoteStep
    \/ DecideBlock
    \/ Tick
    \/ CastTimeoutVoteStep
    \/ StartViewChange
    \/ BroadcastNP
    \/ ConfirmNewPrimaryStep
    \/ BroadcastSyn
    \/ SendSynAckStep
    \/ CompleteViewChange

APSNext ==
    \/ DetectAnomaly
    \/ SampleGrid
    \/ EstimateGrid
    \/ ExploreGrid
    \/ DeployConfig

Next == ConsensusNext \/ APSNext

Consistency ==
    \A n1, n2 \in Node: st.localChain[n1] = st.localChain[n2]

NoForkPerView ==
    \A v \in 0..MaxView: Cardinality(st.decidedByView[v]) <= 1

PipelineBounded == st.inFlight <= st.activeConfig.pipelineDepth

QCLocked == st.lockedQC.view <= st.highQC.view

QCViewSafety == st.highQC.view <= st.view

MempoolSoundness ==
    /\ st.orderedPool \subseteq st.validatedMempool
    /\ st.validatedMempool \subseteq Tx

ProposalFlowSafety ==
    /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
        => st.teProposal # NoTeProposal
    /\ st.phase \in {"PreCommit", "Commit"}
        => st.fullProposal # NoFullProposal
    /\ st.teProposal # NoTeProposal => st.teProposal.alist # {}
    /\ st.fullProposal # NoFullProposal => st.fullProposal.txs \subseteq Tx

ViewChangeMessageSafety ==
    /\ st.phase # "ViewChange" =>
        /\ st.vProposal = NoVProposal
        /\ st.npMessage = NoNPMessage
        /\ st.synMessage = NoSynMessage
    /\ st.phase = "ViewChange" =>
        /\ st.vProposal # NoVProposal
        /\ st.vProposal.view = st.view
        /\ st.vProposal.rv = st.reputation
        /\ st.vProposal.qc.view <= st.highQC.view
    /\ st.npMessage # NoNPMessage =>
        /\ st.npMessage.view = st.view
        /\ st.npMessage.leader \in st.candidateReplicas
        /\ NPMessageHasValidSortition(st.npMessage, st.reputation)
    /\ st.synMessage # NoSynMessage =>
        /\ st.synMessage.view = st.view
        /\ st.synMessage.leader = st.tentativePrimary
        /\ st.synMessage.rv = st.reputation

ChainParentSafety ==
    /\ \A i \in 1..Len(st.chain):
        /\ st.chain[i].parentView \in -1..MaxView
        /\ st.chain[i].parentView <= st.chain[i].view
        /\ (st.chain[i].parentView < st.chain[i].view
            \/ st.chain[i].view = MaxView)
    /\ \A i \in 2..Len(st.chain):
        /\ st.chain[i - 1].view < st.chain[i].view
        /\ st.chain[i].parentView >= st.chain[i - 1].view

PrimaryEligibilitySafety ==
    /\ st.phase = "ViewChange" =>
        /\ st.tentativePrimary \in st.candidateReplicas
        /\ (st.npMessage = NoNPMessage
            \/ /\ st.npMessage.leader \in st.candidateReplicas
               /\ NPMessageHasValidSortition(st.npMessage, st.reputation))
    /\ st.phase # "ViewChange" =>
        \/ st.primary \in CandidateReplicas(st.reputation, RepThreshold)
        \/ /\ st.phase \in {"Prepare", "PreCommit", "Commit"}
           /\ (st.stageTimer >= st.activeConfig.timeout
               \/ st.timeoutVotes # {})

ReconfigurationSafety ==
    /\ st.activeConfig \in ConfigType
    /\ st.pendingConfig \in ConfigType
    /\ st.schedulerState # "Monitor"
        \/ ConfigSatisfiesNetwork(
            st.activeConfig,
            st.networkCondition
        )

DecoupledPipelineSafety ==
    LET inv ==
            DecouplingInvariant(
                st.disseminationBuffer,
                st.orderingBuffer,
                st.executionBuffer,
                st.computeQueued,
                st.computeReady,
                Tx
            )
        flow ==
            DecouplingFlowSafety(
                st.validatedMempool,
                st.orderedPool,
                st.fullProposal.txs,
                st.disseminationBuffer,
                st.orderingBuffer,
                st.executionBuffer,
                st.computeQueued,
                st.computeReady
            )
    IN
        /\ inv
        /\ flow

EventuallyOneCommit == <> (Len(st.chain) >= 1)
EventuallyTwoCommits == <> (Len(st.chain) >= 2)
InfiniteCollectMinor == []<>(st.phase = "CollectMinor")
EventuallyViewProgress == <> (st.view >= 1)

=============================================================================
