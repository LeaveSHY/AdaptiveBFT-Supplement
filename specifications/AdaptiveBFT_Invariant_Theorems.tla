------------------ MODULE AdaptiveBFT_Invariant_Theorems ------------------
EXTENDS AdaptiveBFT_Abstract, TLAPS, Integers, FiniteSetTheorems

\* Machine-checked inductive core for lock monotonicity.

THEOREM InitEstablishesLockMonotonicity ==
    InitA => LockMonotonicityA
PROOF
    BY DEF InitA, LockMonotonicityA

THEOREM InitEstablishesNoFork ==
    InitA => NoForkA
PROOF
    BY DEF InitA, NoForkA

THEOREM VotePreservesLockMonotonicity ==
    ASSUME NEW n \in Node
    PROVE LockMonotonicityA /\ VoteA(n) => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, VoteA

THEOREM PrepareQCPreservesLockMonotonicity ==
    LockMonotonicityA /\ PrepareQCA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, PrepareQCA, SimpleArithmetic

THEOREM PreCommitQCPreservesLockMonotonicity ==
    LockMonotonicityA /\ PreCommitQCA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, PreCommitQCA, SimpleArithmetic

THEOREM CommitPreservesLockMonotonicity ==
    LockMonotonicityA /\ CommitA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, CommitA, SimpleArithmetic

THEOREM ViewChangePreservesLockMonotonicity ==
    LockMonotonicityA /\ ViewChangeA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, ViewChangeA, SimpleArithmetic

THEOREM RecoverSyncPreservesLockMonotonicity ==
    LockMonotonicityA /\ RecoverSyncA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, RecoverSyncA

THEOREM InternalStepPreservesLockMonotonicity ==
    LockMonotonicityA /\ InternalStepA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, InternalStepA

THEOREM EnvironmentStepPreservesLockMonotonicity ==
    LockMonotonicityA /\ EnvironmentStepA => LockMonotonicityA'
PROOF
    BY DEF LockMonotonicityA, EnvironmentStepA

THEOREM VotePreservesNoFork ==
    ASSUME NEW n \in Node
    PROVE NoForkA /\ VoteA(n) => NoForkA'
PROOF
    BY DEF NoForkA, VoteA

THEOREM PrepareQCPreservesNoFork ==
    NoForkA /\ PrepareQCA => NoForkA'
PROOF
    BY DEF NoForkA, PrepareQCA

THEOREM PreCommitQCPreservesNoFork ==
    NoForkA /\ PreCommitQCA => NoForkA'
PROOF
    BY DEF NoForkA, PreCommitQCA

THEOREM CommitPreservesNoFork ==
    NoForkA /\ CommitA => NoForkA'
PROOF
    <1>1. \A v \in Nat: NoForkA /\ CommitA => Cardinality(decidedByView'[v]) <= 1
        <2>1. ASSUME NEW v \in Nat, NoForkA /\ CommitA
              PROVE Cardinality(decidedByView'[v]) <= 1
            <3>1. CASE v = view
                <4>1. decidedByView'[v] = {view}
                    BY <2>1, <3>1 DEF CommitA
                <4>2. Cardinality({view}) = 1
                    BY FS_Singleton
                <4> QED
                    BY <4>1, <4>2, SimpleArithmetic
            <3>2. CASE v # view
                <4>1. decidedByView'[v] = decidedByView[v]
                    BY <2>1, <3>2 DEF CommitA
                <4>2. Cardinality(decidedByView[v]) <= 1
                    BY <2>1 DEF NoForkA
                <4> QED
                    BY <4>1, <4>2, SimpleArithmetic
            <3> QED
                BY <3>1, <3>2
        <2> QED
            BY <2>1
    <1> QED
        BY <1>1 DEF NoForkA

THEOREM ViewChangePreservesNoFork ==
    NoForkA /\ ViewChangeA => NoForkA'
PROOF
    BY DEF NoForkA, ViewChangeA

THEOREM RecoverSyncPreservesNoFork ==
    NoForkA /\ RecoverSyncA => NoForkA'
PROOF
    BY DEF NoForkA, RecoverSyncA

THEOREM InternalStepPreservesNoFork ==
    NoForkA /\ InternalStepA => NoForkA'
PROOF
    BY DEF NoForkA, InternalStepA

THEOREM EnvironmentStepPreservesNoFork ==
    NoForkA /\ EnvironmentStepA => NoForkA'
PROOF
    BY DEF NoForkA, EnvironmentStepA

THEOREM NoForkPreservedByNext ==
    NoForkA /\ NextA => NoForkA'
PROOF
    <1>1. \A n \in Node: NoForkA /\ VoteA(n) => NoForkA'
        BY VotePreservesNoFork
    <1>2. NoForkA /\ PrepareQCA => NoForkA'
        BY PrepareQCPreservesNoFork
    <1>3. NoForkA /\ PreCommitQCA => NoForkA'
        BY PreCommitQCPreservesNoFork
    <1>4. NoForkA /\ CommitA => NoForkA'
        BY CommitPreservesNoFork
    <1>5. NoForkA /\ ViewChangeA => NoForkA'
        BY ViewChangePreservesNoFork
    <1>6. NoForkA /\ RecoverSyncA => NoForkA'
        BY RecoverSyncPreservesNoFork
    <1>7. NoForkA /\ InternalStepA => NoForkA'
        BY InternalStepPreservesNoFork
    <1>8. NoForkA /\ EnvironmentStepA => NoForkA'
        BY EnvironmentStepPreservesNoFork
    <1> QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF NextA

THEOREM NoForkPreservedByBoxNext ==
    NoForkA /\ [NextA]_varsA => NoForkA'
PROOF
    <1>1. NoForkA /\ NextA => NoForkA'
        BY NoForkPreservedByNext
    <1>2. NoForkA /\ UNCHANGED varsA => NoForkA'
        BY DEF NoForkA, varsA
    <1> QED
        BY <1>1, <1>2 DEF NextA, varsA

THEOREM AbstractNoForkByInduction ==
    SpecA => []NoForkA
PROOF
    <1>1. InitA => NoForkA
        BY InitEstablishesNoFork
    <1>2. NoForkA /\ [NextA]_varsA => NoForkA'
        BY NoForkPreservedByBoxNext
    <1> QED
        BY <1>1, <1>2, PTL DEF SpecA

THEOREM LockMonotonicityPreservedByNext ==
    LockMonotonicityA /\ NextA => LockMonotonicityA'
PROOF
    <1>1. \A n \in Node: LockMonotonicityA /\ VoteA(n) => LockMonotonicityA'
        BY VotePreservesLockMonotonicity
    <1>2. LockMonotonicityA /\ PrepareQCA => LockMonotonicityA'
        BY PrepareQCPreservesLockMonotonicity
    <1>3. LockMonotonicityA /\ PreCommitQCA => LockMonotonicityA'
        BY PreCommitQCPreservesLockMonotonicity
    <1>4. LockMonotonicityA /\ CommitA => LockMonotonicityA'
        BY CommitPreservesLockMonotonicity
    <1>5. LockMonotonicityA /\ ViewChangeA => LockMonotonicityA'
        BY ViewChangePreservesLockMonotonicity
    <1>6. LockMonotonicityA /\ RecoverSyncA => LockMonotonicityA'
        BY RecoverSyncPreservesLockMonotonicity
    <1>7. LockMonotonicityA /\ InternalStepA => LockMonotonicityA'
        BY InternalStepPreservesLockMonotonicity
    <1>8. LockMonotonicityA /\ EnvironmentStepA => LockMonotonicityA'
        BY EnvironmentStepPreservesLockMonotonicity
    <1> QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF NextA

THEOREM LockMonotonicityPreservedByBoxNext ==
    LockMonotonicityA /\ [NextA]_varsA => LockMonotonicityA'
PROOF
    <1>1. LockMonotonicityA /\ NextA => LockMonotonicityA'
        BY LockMonotonicityPreservedByNext
    <1>2. LockMonotonicityA /\ UNCHANGED varsA => LockMonotonicityA'
        BY DEF LockMonotonicityA, varsA
    <1> QED
        BY <1>1, <1>2 DEF NextA, varsA

THEOREM AbstractLockSafetyByInduction ==
    SpecA => []LockMonotonicityA
PROOF
    <1>1. InitA => LockMonotonicityA
        BY InitEstablishesLockMonotonicity
    <1>2. LockMonotonicityA /\ [NextA]_varsA => LockMonotonicityA'
        BY LockMonotonicityPreservedByBoxNext
    <1> QED
        BY <1>1, <1>2, PTL DEF SpecA

=============================================================================
