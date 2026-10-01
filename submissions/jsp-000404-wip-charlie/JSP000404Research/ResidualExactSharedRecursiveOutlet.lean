import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import JSP000404Research.ResidualExactPairStateClassification
import Mathlib.Tactic

/-!
# Recursive refinement of an exact shared overload

An ExactSharedOutlet says how a shared word from an exact source meets a
strict, exact, or loss neighbour.  This file refines its exact--exact branch
through the existing ordered exact-pair classifier.

The source exactness is kept as an explicit theorem hypothesis instead of
being duplicated inside the outlet datatype.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive ExactRecursiveOutlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (source : V) : Prop
  | strictPaid
      (w : V)
      (hwStrict : exponent w < projectedFree C w)
      (hpaid :
        (retainedCompletionWords C source ∩
          retainedCompletionWords C w).card
          ≤
        dyadicProfileSurplus exponent (projectedFree C) w)
  | mixedUnpaid
      (w : V)
      (hrel : MixedUnpaidChild C exponent source w)
  | exactActiveSafe
      (a b : V)
      (hab : a < b)
      (haExact : ExactProjectedBudget C exponent a)
      (hbExact : ExactProjectedBudget C exponent b)
      (word : Fin n → Bool)
      (haWord : word ∈ retainedCompletionWords C a)
      (hbWord : word ∈ retainedCompletionWords C b)
      (hactive :
        ∃ c : Fin n,
          c ∉ residualForbidden C a b ∧
          ((c ∈ retainedActive C a ∧
              c ∉ retainedActive C b) ∨
           (c ∉ retainedActive C a ∧
              c ∈ retainedActive C b)))
  | exactPositiveReduced
      (a b : V)
      (hab : a < b)
      (haExact : ExactProjectedBudget C exponent a)
      (hbExact : ExactProjectedBudget C exponent b)
      (word : Fin n → Bool)
      (haWord : word ∈ retainedCompletionWords C a)
      (hbWord : word ∈ retainedCompletionWords C b)
      (hno : NoActiveSafeCoordinate C a b)
      (haPos :
        (commonInactiveRetained C a b).card < exponent a)
      (hbPos :
        (commonInactiveRetained C a b).card < exponent b)
      (hcap :
        2 ^ exponent a + 2 ^ exponent b
          ≤
        2 ^
          (n -
            ((incomingRetained C b).card +
             (outgoingRetained C a).card)))
  | exactReducedZero
      (a b : V)
      (hab : a < b)
      (haExact : ExactProjectedBudget C exponent a)
      (hbExact : ExactProjectedBudget C exponent b)
      (word : Fin n → Bool)
      (haWord : word ∈ retainedCompletionWords C a)
      (hbWord : word ∈ retainedCompletionWords C b)
      (hno : NoActiveSafeCoordinate C a b)
      (hzero :
        exponent a = (commonInactiveRetained C a b).card
        ∨
        exponent b = (commonInactiveRetained C a b).card)
  | loss
      (w : V)
      (hsw : source ≠ w)
      (hwLoss : w ∈ projectedLossVertices C exponent)

theorem exactSharedOutlet_to_recursive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {source : V}
    (hsourceExact : ExactProjectedBudget C exponent source)
    (hout : ExactSharedOutlet C exponent source) :
    ExactRecursiveOutlet C exponent source := by
  classical
  rcases hout with
    ⟨w,hwStrict,hpaid⟩ |
    ⟨w,hmixed⟩ |
    ⟨w,hsw,hwExact,word,hsWord,hwWord⟩ |
    ⟨w,hsw,hwLoss⟩
  · exact ExactRecursiveOutlet.strictPaid
      w hwStrict hpaid
  · exact ExactRecursiveOutlet.mixedUnpaid
      w hmixed
  · rcases lt_or_gt_of_ne hsw with hswlt | hwslt
    · rcases
        exact_overlap_activeSafe_or_noActiveSafe_reduced_classification
          C exponent hswlt hsWord hwWord
          hsourceExact hwExact
        with hactive | hno
      · exact ExactRecursiveOutlet.exactActiveSafe
          source w hswlt
          hsourceExact hwExact
          word hsWord hwWord hactive
      · obtain ⟨hNo,hred⟩ := hno
        rcases hred with hpos | haZero | hbZero
        · exact ExactRecursiveOutlet.exactPositiveReduced
            source w hswlt
            hsourceExact hwExact
            word hsWord hwWord hNo hpos.1 hpos.2
            (exact_overlap_noActiveSafe_positiveReduced_capacity
              C exponent hNo hsWord hwWord
              hsourceExact hwExact hpos.1 hpos.2)
        · exact ExactRecursiveOutlet.exactReducedZero
            source w hswlt
            hsourceExact hwExact
            word hsWord hwWord hNo (Or.inl haZero)
        · exact ExactRecursiveOutlet.exactReducedZero
            source w hswlt
            hsourceExact hwExact
            word hsWord hwWord hNo (Or.inr hbZero)
    · rcases
        exact_overlap_activeSafe_or_noActiveSafe_reduced_classification
          C exponent hwslt hwWord hsWord
          hwExact hsourceExact
        with hactive | hno
      · exact ExactRecursiveOutlet.exactActiveSafe
          w source hwslt
          hwExact hsourceExact
          word hwWord hsWord hactive
      · obtain ⟨hNo,hred⟩ := hno
        rcases hred with hpos | haZero | hbZero
        · exact ExactRecursiveOutlet.exactPositiveReduced
            w source hwslt
            hwExact hsourceExact
            word hwWord hsWord hNo hpos.1 hpos.2
            (exact_overlap_noActiveSafe_positiveReduced_capacity
              C exponent hNo hwWord hsWord
              hwExact hsourceExact hpos.1 hpos.2)
        · exact ExactRecursiveOutlet.exactReducedZero
            w source hwslt
            hwExact hsourceExact
            word hwWord hsWord hNo (Or.inl haZero)
        · exact ExactRecursiveOutlet.exactReducedZero
            w source hwslt
            hwExact hsourceExact
            word hwWord hsWord hNo (Or.inr hbZero)
  · exact ExactRecursiveOutlet.loss
      w hsw hwLoss

#print axioms exactSharedOutlet_to_recursive

end OrderedEdgeColoring
end JSP000404Research
