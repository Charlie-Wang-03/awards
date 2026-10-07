import JSP000404Research.ResidualSafeCommonInactiveTensor
import JSP000404Research.ResidualSafeCommonInactiveCapacity
import JSP000404Research.ResidualSafeDeterministicTransition
import Mathlib.Tactic

/-!
# Exact residual-pair state classification after a full transition

Let a<b be an exact--exact residual pair carrying one common completion word.

If NoActiveSafeCoordinate fails, some safe coordinate is active at at least one
endpoint. Since a safe overlap coordinate cannot be active at both endpoints,
this is exactly the deterministic active-safe regime.

If NoActiveSafeCoordinate holds, write

  d = card(commonInactiveRetained C a b).

The tensor formulas show

  exponent(a) = d + out-difference,
  exponent(b) = d + in-difference,

so d <= exponent at both endpoints. Hence either both reduced exponents are
positive, or at least one endpoint is reduced-zero.

The positive-reduced case is already closed by the existing tensor-capacity
theorem. Therefore the only exact--exact full-transition state which can remain
recursive is the reduced-zero nested state.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exact_overlap_activeSafe_or_noActiveSafe_reduced_classification
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {a b : V} {word : Fin n → Bool}
    (hab : a < b)
    (haWord : word ∈ retainedCompletionWords C a)
    (hbWord : word ∈ retainedCompletionWords C b)
    (haSat : ExactProjectedBudget C exponent a)
    (hbSat : ExactProjectedBudget C exponent b) :
    (
      ∃ c : Fin n,
        c ∉ residualForbidden C a b ∧
        ((c ∈ retainedActive C a ∧
            c ∉ retainedActive C b) ∨
         (c ∉ retainedActive C a ∧
            c ∈ retainedActive C b))
    )
    ∨
    (
      NoActiveSafeCoordinate C a b ∧
      (
        (
          (commonInactiveRetained C a b).card < exponent a ∧
          (commonInactiveRetained C a b).card < exponent b
        )
        ∨
        exponent a = (commonInactiveRetained C a b).card
        ∨
        exponent b = (commonInactiveRetained C a b).card
      )
    ) := by
  classical
  by_cases hno : NoActiveSafeCoordinate C a b
  · right
    refine ⟨hno,?_⟩
    have haExp :=
      exponent_eq_commonInactive_add_outDiff_of_noActiveSafe_saturated
        C exponent hno haWord hbWord haSat
    have hbExp :=
      exponent_eq_commonInactive_add_inDiff_of_noActiveSafe_saturated
        C exponent hno haWord hbWord hbSat
    by_cases haZero :
        exponent a = (commonInactiveRetained C a b).card
    · exact Or.inr (Or.inl haZero)
    · by_cases hbZero :
        exponent b = (commonInactiveRetained C a b).card
      · exact Or.inr (Or.inr hbZero)
      · left
        constructor <;> omega
  · left
    unfold NoActiveSafeCoordinate at hno
    push_neg at hno
    obtain ⟨c,hcSafe,hactive⟩ := hno
    by_cases hca : c ∈ retainedActive C a
    · have hcb : c ∉ retainedActive C b := by
        intro hcb
        exact safe_overlap_not_active_both
          C haWord hbWord hcSafe ⟨hca,hcb⟩
      exact ⟨c,hcSafe,Or.inl ⟨hca,hcb⟩⟩
    · rcases hactive with hca' | hcb
      · exact False.elim (hca hca')
      · exact ⟨c,hcSafe,Or.inr ⟨hca,hcb⟩⟩

theorem exact_overlap_noActiveSafe_positiveReduced_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {a b : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C a b)
    (haWord : word ∈ retainedCompletionWords C a)
    (hbWord : word ∈ retainedCompletionWords C b)
    (haSat : ExactProjectedBudget C exponent a)
    (hbSat : ExactProjectedBudget C exponent b)
    (haPos :
      (commonInactiveRetained C a b).card < exponent a)
    (hbPos :
      (commonInactiveRetained C a b).card < exponent b) :
    2 ^ exponent a + 2 ^ exponent b
      ≤
    2 ^
      (n -
        ((incomingRetained C b).card +
         (outgoingRetained C a).card)) :=
  noActiveSafe_saturated_positiveReduced_pair_dyadic_capacity
    C exponent hno haWord hbWord haSat hbSat haPos hbPos

#print axioms exact_overlap_activeSafe_or_noActiveSafe_reduced_classification
#print axioms exact_overlap_noActiveSafe_positiveReduced_capacity

end OrderedEdgeColoring
end JSP000404Research
