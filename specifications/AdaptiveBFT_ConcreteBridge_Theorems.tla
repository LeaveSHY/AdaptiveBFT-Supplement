---------------- MODULE AdaptiveBFT_ConcreteBridge_Theorems ----------------
EXTENDS AdaptiveBFT_Refinement, TLAPS

\* Concrete safety profile implies abstract safety over the projected state.
THEOREM ConcreteSafetyToAbstractSafetyA ==
    (NoForkPerView /\ QCLocked /\ QCViewSafety) => ABSTRACT!SafetyA
PROOF
    BY ConcreteSafetyImpliesAbstractSafety

\* Concrete commit-progress shape implies projected abstract liveness shape.
THEOREM ConcreteTwoCommitsToAbstractLiveness ==
    EventuallyTwoCommits => ABSTRACT!LivenessA
PROOF
    BY ConcreteLivenessShape

\* Concrete profile packaged as a refinement invariant entry point.
THEOREM ConcreteProfileToRefinementInvariant ==
    (TypeOK /\ NoForkPerView /\ QCLocked /\ QCViewSafety) => RefinementInvariant
PROOF
    BY ConcreteSafetyToAbstractSafetyA
       DEF RefinementInvariant,
           AbsChainProjectionInvariant,
           AbsChain,
           ABSTRACT!SafetyA

=============================================================================
