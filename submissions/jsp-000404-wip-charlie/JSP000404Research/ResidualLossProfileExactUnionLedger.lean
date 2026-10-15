import JSP000404Research.ResidualLossDuplicateDebtLedger
import JSP000404Research.ResidualLossWords
import Mathlib.Tactic

/-!
# The real projected profile-loss term equals used translated Boolean mass
# plus exact cross-coordinate duplicate debt

The original proof's loss term is not merely the target sum with an
arbitrary factor 2: `totalDyadicProfileLoss exponent (projectedFree C)`
is represented by the union of the **original** completion cubes
(`lossCompletionWords`), whose cubes are pairwise disjoint.

The translated slices may overlap across flip coordinates. We prove,
without any avoidance hypothesis, the exact conservation identity

  totalDyadicProfileLoss =
    |actual union of translated loss slices| + translatedLossDuplicateDebt.

Consequently a proposed payment that only counts the union must
separately pay or eliminate exactly the duplicate-debt correction.
Neither the union nor the debt is automatically a global Boolean hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem lossCompletionWords_card_eq_sum_translatedSlices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    (lossCompletionWords C exponent).card =
      ∑ c : Fin n, (translatedLossSliceWords C exponent choice c).card := by
  classical
  rw [lossCompletionWords,
    Finset.card_biUnion
      (projectedLoss_completion_pairwiseDisjoint
        C exponent hexp honeLoss)]
  calc
    (∑ v ∈ projectedLossVertices C exponent,
        (retainedCompletionWords C v).card) =
      ∑ c : Fin n, ∑ v ∈ lossCoordinateSlice C exponent choice c,
        (retainedCompletionWords C v).card := by
          simp only [lossCoordinateSlice, Finset.sum_filter]
          rw [Finset.sum_comm]
          simp
    _ = ∑ c : Fin n,
        (translatedLossSliceWords C exponent choice c).card := by
          apply Finset.sum_congr rfl
          intro c hc
          exact (translatedLossSliceWords_card
            C exponent hexp honeLoss choice c).symm

/-- Direct unconditional identity for the *original* loss-word mass. -/
theorem lossCompletionWords_card_eq_translated_union_plus_duplicate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    (lossCompletionWords C exponent).card =
      (translatedLossAllCoordinateWords C exponent choice).card +
        translatedLossDuplicateDebt C exponent choice := by
  classical
  have hsum :=
    lossCompletionWords_card_eq_sum_translatedSlices
      C exponent hexp honeLoss choice
  have hle :=
    translatedLossAllCoordinateWords_card_le_sum C exponent choice
  unfold translatedLossDuplicateDebt
  omega

/-- The actual dyadic-profile-loss term used in the global capacity
problem has an *exact* Boolean translation ledger, with all
cross-coordinate collisions isolated in one explicit defect. -/
theorem totalDyadicProfileLoss_eq_translated_union_plus_duplicate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    totalDyadicProfileLoss exponent (projectedFree C) =
      (translatedLossAllCoordinateWords C exponent choice).card +
        translatedLossDuplicateDebt C exponent choice := by
  rw [← lossCompletionWords_card_eq_totalDyadicProfileLoss
    C exponent hexp honeLoss]
  exact lossCompletionWords_card_eq_translated_union_plus_duplicate
    C exponent hexp honeLoss choice

/-- The pre-existing `badProjectionWords` ledger can now be stated
using the *actual* translated-loss union, while explicitly retaining the
cross-coordinate duplicate correction. This is a numerical equality:
we do NOT assert that the translated union is disjoint from overlap words. -/
theorem badProjectionWords_card_eq_overlap_union_plus_duplicate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    (lossCompletionWords C exponent ∪ overlapCompletionWords C).card =
      (overlapCompletionWords C).card +
        (translatedLossAllCoordinateWords C exponent choice).card +
        translatedLossDuplicateDebt C exponent choice := by
  rw [badProjectionWords_card C exponent hexp honeLoss]
  rw [totalDyadicProfileLoss_eq_translated_union_plus_duplicate
    C exponent hexp honeLoss choice]
  omega

#print axioms badProjectionWords_card_eq_overlap_union_plus_duplicate

#print axioms lossCompletionWords_card_eq_sum_translatedSlices
#print axioms lossCompletionWords_card_eq_translated_union_plus_duplicate
#print axioms totalDyadicProfileLoss_eq_translated_union_plus_duplicate

end OrderedEdgeColoring
end JSP000404Research
