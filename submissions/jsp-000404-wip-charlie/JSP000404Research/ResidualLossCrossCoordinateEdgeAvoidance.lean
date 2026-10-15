import JSP000404Research.ResidualLossCoordinateSlices
import Mathlib.Tactic

/-!
# A precise sufficient condition for collision-free projected-loss translations

The previous exact coordinate-slice accounting does not assert disjointness
between *different* chosen flip coordinates. Its overlap theorem supplies a
necessary retained-edge colour witness.

Here a transparent, explicit, checkable sufficient hypothesis forbids those
witnesses: for every ordered pair of projected-loss vertices, any retained
connecting edge must have a colour different from both chosen flip coordinates.

This yields genuine pairwise disjointness of the translated coordinate slices,
and hence upgrades the exact sum of slice sizes to the cardinality of their
actual Boolean union. No planar AngleCap theorem asserting this additional
hypothesis is claimed. The global six-source payment remains open.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The chosen flip coordinate at each loss vertex avoids both ends of
any *retained* edge whose two endpoints are projected-loss vertices. -/
def LossFlipAvoidsRetainedEdges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Prop :=
  ∀ v w : V,
    v ∈ projectedLossVertices C exponent →
    w ∈ projectedLossVertices C exponent →
    ∀ (_hvw : v < w) (hret : (C.color v w).val < n),
      retainedColor C v w hret ≠ choice v ∧
      retainedColor C v w hret ≠ choice w

theorem translatedLossSliceWords_disjoint_of_edge_avoidance
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (havoid : LossFlipAvoidsRetainedEdges C exponent choice)
    {c d : Fin n} (hcd : c ≠ d) :
    Disjoint (translatedLossSliceWords C exponent choice c)
      (translatedLossSliceWords C exponent choice d) := by
  classical
  rw [Finset.disjoint_left]
  intro word hc hd
  obtain ⟨v, hv, w, hw, hvw, witness⟩ :=
    translatedLossSliceWords_cross_collision_edge_colour
      C exponent hexp honeLoss choice hcd hc hd
  have hvData := (mem_lossCoordinateSlice C exponent choice c v).1 hv
  have hwData := (mem_lossCoordinateSlice C exponent choice d w).1 hw
  rcases witness with ⟨hvwlt, hret, heq⟩ | ⟨hwvlt, hret, heq⟩
  · have hblocked := havoid v w hvData.1 hwData.1 hvwlt hret
    rw [hvData.2, hwData.2] at hblocked
    rcases heq with heq | heq
    · exact hblocked.1 heq
    · exact hblocked.2 heq
  · have hblocked := havoid w v hwData.1 hvData.1 hwvlt hret
    rw [hwData.2, hvData.2] at hblocked
    rcases heq with heq | heq
    · exact hblocked.2 heq
    · exact hblocked.1 heq

/-- Exact Boolean union mass, assuming the explicit retained-edge
avoidance invariant. In particular, the sum of cross-slice intersections
requires no artificial credit under this hypothesis. -/
theorem two_mul_translatedLossSlice_union_card_of_edge_avoidance
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (havoid : LossFlipAvoidsRetainedEdges C exponent choice) :
    2 * ((Finset.univ : Finset (Fin n)).biUnion
      (fun c => translatedLossSliceWords C exponent choice c)).card =
      ∑ v ∈ projectedLossVertices C exponent,
        2 ^ exponent v := by
  classical
  have hdisj :
      (((Finset.univ : Finset (Fin n)) : Set (Fin n))).PairwiseDisjoint
        (fun c => translatedLossSliceWords C exponent choice c) := by
    intro c hc d hd hcd
    exact translatedLossSliceWords_disjoint_of_edge_avoidance
      C exponent hexp honeLoss choice havoid hcd
  calc
    2 * ((Finset.univ : Finset (Fin n)).biUnion
        (fun c => translatedLossSliceWords C exponent choice c)).card =
        2 * (∑ c : Fin n, (translatedLossSliceWords C exponent choice c).card) := by
          rw [Finset.card_biUnion hdisj]
    _ = ∑ v ∈ projectedLossVertices C exponent,
        2 ^ exponent v :=
      two_mul_total_translatedLossSliceWords_card
        C exponent hexp honeLoss choice

#print axioms translatedLossSliceWords_disjoint_of_edge_avoidance
#print axioms two_mul_translatedLossSlice_union_card_of_edge_avoidance

end OrderedEdgeColoring
end JSP000404Research
