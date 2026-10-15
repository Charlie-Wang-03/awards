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

/-- A positive overcount must arise from two *distinct* coordinate slices
sharing an actual Boolean word. This is an unconditional converse to the
trivial implication from cross-slice disjointness to zero debt. -/
theorem positive_loss_duplicateDebt_has_slice_collision
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (hdup : 0 < translatedLossDuplicateDebt C exponent choice) :
    ∃ c d : Fin n, c ≠ d ∧
      ∃ word : Fin n → Bool,
        word ∈ translatedLossSliceWords C exponent choice c ∧
        word ∈ translatedLossSliceWords C exponent choice d := by
  classical
  by_contra hnone
  have hdisj :
      (((Finset.univ : Finset (Fin n)) : Set (Fin n))).PairwiseDisjoint
        (fun c => translatedLossSliceWords C exponent choice c) := by
    intro c hc d hd hcd
    rw [Finset.disjoint_left]
    intro word hcw hdw
    exact hnone ⟨c, d, hcd, word, hcw, hdw⟩
  unfold translatedLossDuplicateDebt translatedLossAllCoordinateWords at hdup
  rw [Finset.card_biUnion hdisj] at hdup
  simp at hdup

/-- Every *positive* projected-loss duplicate debt forces a concrete
retained edge between distinct loss vertices, with the edge colour equal
to one of their chosen flip coordinates. The converse is not claimed:
a problematic edge may fail to cause an actual Boolean collision. -/
theorem positive_loss_duplicateDebt_has_retained_edge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hdup : 0 < translatedLossDuplicateDebt C exponent choice) :
    ∃ v ∈ projectedLossVertices C exponent,
      ∃ w ∈ projectedLossVertices C exponent,
        v ≠ w ∧
          ((∃ hvw : v < w,
              ∃ hret : (C.color v w).val < n,
                retainedColor C v w hret = choice v ∨
                retainedColor C v w hret = choice w) ∨
           (∃ hwv : w < v,
              ∃ hret : (C.color w v).val < n,
                retainedColor C w v hret = choice v ∨
                retainedColor C w v hret = choice w)) := by
  obtain ⟨c, d, hcd, word, hc, hd⟩ :=
    positive_loss_duplicateDebt_has_slice_collision
      C exponent choice hdup
  obtain ⟨v, hv, w, hw, hvw, hedge⟩ :=
    translatedLossSliceWords_cross_collision_edge_colour
      C exponent hexp honeLoss choice hcd hc hd
  have hvData := (mem_lossCoordinateSlice C exponent choice c v).1 hv
  have hwData := (mem_lossCoordinateSlice C exponent choice d w).1 hw
  refine ⟨v, hvData.1, w, hwData.1, hvw, ?_⟩
  rcases hedge with ⟨hvwlt, hret, hcol⟩ | ⟨hwvlt, hret, hcol⟩
  · exact Or.inl ⟨hvwlt, hret,
      by simpa only [hvData.2, hwData.2] using hcol⟩
  · exact Or.inr ⟨hwvlt, hret,
      by simpa only [hvData.2, hwData.2] using hcol⟩

#print axioms positive_loss_duplicateDebt_has_slice_collision
#print axioms positive_loss_duplicateDebt_has_retained_edge

#print axioms translatedLossAllCoordinateWords_card_le_sum
#print axioms two_mul_loss_union_add_duplicate_debt_eq_target
#print axioms translatedLossDuplicateDebt_eq_zero_of_edge_avoidance

end OrderedEdgeColoring
end JSP000404Research
