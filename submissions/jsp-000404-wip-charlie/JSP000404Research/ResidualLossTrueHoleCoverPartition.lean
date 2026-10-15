import JSP000404Research.ResidualLossProfileExactUnionLedger
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Exact three-way projected profile-loss payment frontier

We split the **actual** union of translated projected-loss slices
into (i) globally uncovered true Boolean holes, and (ii) globally
covered blockers. We must ALSO retain the cross-coordinate duplicate debt
from the exact translation ledger.

This is a partition/counting identity. It does not assert that the
true-hole portion is available for non-reuse by other six-source
obligations, or that the covered blockers can be credited as holes.
No extra planar assumption or admitted axiom is introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedLossTrueHoleWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Finset (Fin n → Bool) :=
  translatedLossAllCoordinateWords C exponent choice \
    coveredCompletionWords C

noncomputable def translatedLossCoveredWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Finset (Fin n → Bool) :=
  translatedLossAllCoordinateWords C exponent choice ∩
    coveredCompletionWords C

/-- The two pieces of the actual translated union are disjoint and
exhaust the union (regardless of whether coordinate slices intersect). -/
theorem translatedLossAllCoordinateWords_card_eq_holes_plus_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) :
    (translatedLossAllCoordinateWords C exponent choice).card =
      (translatedLossTrueHoleWords C exponent choice).card +
      (translatedLossCoveredWords C exponent choice).card := by
  classical
  let U := translatedLossAllCoordinateWords C exponent choice
  let K := coveredCompletionWords C
  have hpartition : U = (U \ K) ∪ (U ∩ K) := by
    ext word
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : Disjoint (U \ K) (U ∩ K) := by
    apply Finset.disjoint_left.mpr
    intro word hminus hinter
    exact (Finset.mem_sdiff.mp hminus).2 (Finset.mem_inter.mp hinter).2
  change U.card = (U \ K).card + (U ∩ K).card
  calc
    U.card = ((U \ K) ∪ (U ∩ K)).card := congrArg Finset.card hpartition
    _ = (U \ K).card + (U ∩ K).card :=
      Finset.card_union_of_disjoint hdisj

/-- Exact non-overclaiming payment ledger for the original
totalDyadicProfileLoss: true holes + already covered blockers + the
remaining duplicate-overcount debt. -/
theorem totalDyadicProfileLoss_eq_trueHoles_plus_covered_plus_duplicate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    totalDyadicProfileLoss exponent (projectedFree C) =
      (translatedLossTrueHoleWords C exponent choice).card +
      (translatedLossCoveredWords C exponent choice).card +
      translatedLossDuplicateDebt C exponent choice := by
  rw [totalDyadicProfileLoss_eq_translated_union_plus_duplicate
    C exponent hexp honeLoss choice]
  rw [translatedLossAllCoordinateWords_card_eq_holes_plus_covered]

#print axioms translatedLossAllCoordinateWords_card_eq_holes_plus_covered
#print axioms totalDyadicProfileLoss_eq_trueHoles_plus_covered_plus_duplicate

end OrderedEdgeColoring
end JSP000404Research
