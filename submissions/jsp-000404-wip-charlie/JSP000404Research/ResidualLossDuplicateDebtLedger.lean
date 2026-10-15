import JSP000404Research.ResidualLossCrossCoordinateEdgeAvoidance
import Mathlib.Tactic

/-!
# Exact unconditional projected-loss collision debt

Per-coordinate translated loss slices are disjoint *inside* each slice, but
not necessarily across different flip coordinates. Hence the sum of their
sizes may count the same Boolean word more than once.

We isolate the exact global duplicate debt as a natural-number difference.
This is an unconditional identity, requiring only the original exponent
and active-palette bounds: no retained-edge avoidance or planar AngleCap
condition is added.

The identity DOES NOT manufacture true Boolean holes or unreserved surplus.
It makes the precise collision overcount that a future payment theorem must
address visible and available in the independent Lean proof chain.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The actual union of all translated projected-loss coordinate slices. -/
noncomputable def translatedLossAllCoordinateWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n)).biUnion
    (fun c => translatedLossSliceWords C exponent choice c)

/-- Exact multiplicity overcount caused by cross-coordinate word reuse.
It is **not** a true-hole credit. -/
noncomputable def translatedLossDuplicateDebt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : ℕ :=
  (∑ c : Fin n, (translatedLossSliceWords C exponent choice c).card) -
    (translatedLossAllCoordinateWords C exponent choice).card

theorem translatedLossAllCoordinateWords_card_le_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) :
    (translatedLossAllCoordinateWords C exponent choice).card ≤
      ∑ c : Fin n, (translatedLossSliceWords C exponent choice c).card := by
  classical
  unfold translatedLossAllCoordinateWords
  exact Finset.card_biUnion_le

/-- Unconditional exact loss payment ledger: the original projected-loss
dyadic mass equals twice the actually used union plus *twice* the duplicate
debt. The latter cannot be dropped without independent justification. -/
theorem two_mul_loss_union_add_duplicate_debt_eq_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    2 * (translatedLossAllCoordinateWords C exponent choice).card +
      2 * translatedLossDuplicateDebt C exponent choice =
        ∑ v ∈ projectedLossVertices C exponent, 2 ^ exponent v := by
  classical
  have hle :=
    translatedLossAllCoordinateWords_card_le_sum C exponent choice
  have hsum :=
    two_mul_total_translatedLossSliceWords_card
      C exponent hexp honeLoss choice
  unfold translatedLossDuplicateDebt
  omega

/-- Under the additional retained-edge avoidance condition, the exact
duplicate debt disappears, by the *verified* disjoint-union theorem. -/
theorem translatedLossDuplicateDebt_eq_zero_of_edge_avoidance
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (havoid : LossFlipAvoidsRetainedEdges C exponent choice) :
    translatedLossDuplicateDebt C exponent choice = 0 := by
  classical
  have hdisj :
      (((Finset.univ : Finset (Fin n)) : Set (Fin n))).PairwiseDisjoint
        (fun c => translatedLossSliceWords C exponent choice c) := by
    intro c hc d hd hcd
    exact translatedLossSliceWords_disjoint_of_edge_avoidance
      C exponent hexp honeLoss choice havoid hcd
  unfold translatedLossDuplicateDebt translatedLossAllCoordinateWords
  rw [Finset.card_biUnion hdisj]
  simp

#print axioms translatedLossAllCoordinateWords_card_le_sum
#print axioms two_mul_loss_union_add_duplicate_debt_eq_target
#print axioms translatedLossDuplicateDebt_eq_zero_of_edge_avoidance

end OrderedEdgeColoring
end JSP000404Research
