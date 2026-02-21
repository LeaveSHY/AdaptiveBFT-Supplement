----------------------- MODULE AdaptiveBFT_Theorems -----------------------
EXTENDS AdaptiveBFT_Invariant_Theorems, FiniteSetTheorems, TLAPS, Integers

\* Derived arithmetic fact used by quorum lemmas.
THEOREM QuorumMajority ==
    ASSUME F \in Int,
           Quorum = (2 * F) + 1
    PROVE Quorum > (2 * F)
PROOF
    BY SimpleArithmetic

THEOREM NatPlusOnePositive ==
    ASSUME NEW n \in Nat
    PROVE n + 1 > 0
PROOF
    BY SimpleArithmetic

THEOREM GEAndGTImpliesGT ==
    ASSUME NEW x \in Int,
           NEW y \in Int,
           NEW z \in Int,
           x >= y,
           y > z
    PROVE x > z
PROOF
    BY SimpleArithmetic

THEOREM GTAndEqImpliesGT ==
    ASSUME NEW x \in Int,
           NEW y \in Int,
           NEW z \in Int,
           x > y,
           y = z
    PROVE x > z
PROOF
    BY SimpleArithmetic

THEOREM QuorumCardLowerBound ==
    ASSUME NEW a \in Nat,
           NEW b \in Nat,
           NEW f \in Nat,
           a >= (2 * f) + 1,
           b >= (2 * f) + 1
    PROVE a + b > (3 * f) + 1
PROOF
    <1>1. a + b >= ((2 * f) + 1) + ((2 * f) + 1)
        BY SimpleArithmetic
    <1>2. ((2 * f) + 1) + ((2 * f) + 1) = ((3 * f) + 1) + (f + 1)
        BY SimpleArithmetic
    <1>3. f + 1 > 0
        BY NatPlusOnePositive, f \in Nat
    <1>4. ((2 * f) + 1) + ((2 * f) + 1) > (3 * f) + 1
        BY <1>2, <1>3, SimpleArithmetic
    <1>5. a + b > (3 * f) + 1
        BY GEAndGTImpliesGT, <1>1, <1>4
    <1> QED
        BY <1>5

\* Unbounded safety statement over the abstract protocol model.
THEOREM AbstractSafetyTheorem ==
    SpecA => []SafetyA
PROOF
    <1>1. SpecA => []NoForkA
        BY AbstractNoForkByInduction
    <1>2. SpecA => []LockMonotonicityA
        BY AbstractLockSafetyByInduction
    <1>3. SpecA => []SafetyA
        BY <1>1, <1>2, PTL DEF SafetyA
    <1> QED
        BY <1>3

THEOREM AbstractLockSafetyTheorem ==
    SpecA => []LockMonotonicityA
PROOF
    BY AbstractLockSafetyByInduction

\* Liveness statement is assumption-explicit by construction.
THEOREM AbstractLivenessTheorem ==
    (SpecA /\ LivenessAssumptionsA) => LivenessA
PROOF
    BY DEF LivenessAssumptionsA, ProgressWitnessA, LivenessA

\* Core quorum-intersection lemma used by safety arguments.
THEOREM QuorumIntersection ==
    ASSUME F \in Nat,
           IsFiniteSet(Node),
           Cardinality(Node) = (3 * F) + 1,
           Quorum = (2 * F) + 1
    PROVE  \A A, B \in SUBSET Node:
               /\ Cardinality(A) >= Quorum
               /\ Cardinality(B) >= Quorum
               => A \cap B # {}
PROOF
    <1> SUFFICES ASSUME NEW A \in SUBSET Node,
                        NEW B \in SUBSET Node,
                        Cardinality(A) >= Quorum,
                        Cardinality(B) >= Quorum
                 PROVE A \cap B # {}
      OBVIOUS
    <1>1. IsFiniteSet(A)
      BY FS_Subset, IsFiniteSet(Node), A \subseteq Node
    <1>2. IsFiniteSet(B)
      BY FS_Subset, IsFiniteSet(Node), B \subseteq Node
    <1>3. Cardinality(A) \in Nat
      BY FS_CardinalityType, <1>1
    <1>4. Cardinality(B) \in Nat
      BY FS_CardinalityType, <1>2
    <1>5. Cardinality(A) + Cardinality(B) > (3 * F) + 1
      BY QuorumCardLowerBound, <1>3, <1>4, F \in Nat, Cardinality(A) >= Quorum, Cardinality(B) >= Quorum, Quorum = (2 * F) + 1
    <1>6. Cardinality(A) + Cardinality(B) > Cardinality(Node)
      BY GTAndEqImpliesGT, <1>5, Cardinality(Node) = (3 * F) + 1
    <1>7. A \cap B # {}
      BY FS_MajoritiesIntersect, IsFiniteSet(Node), A \subseteq Node, B \subseteq Node, <1>6
    <1> QED BY <1>7

=============================================================================
