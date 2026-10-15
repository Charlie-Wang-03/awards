import JSP000404Research.ResidualLossEarliestActualEdgeCarrier
import Mathlib.Tactic

/-!
# No double reuse of an earliest collision event across previous coordinates

For a FIXED later coordinate c, earliest prior coordinates d and e
produce disjoint Boolean-word carrier families, including after
refining to genuine source--blocker retained edges.

This is a strong local nonreuse statement for collision event ownership.
It does not imply that the same Boolean word is absent from other
later coordinates c'. Thus it cannot itself provide globally
non-reused outside Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual source--blocker edge carrier at coordinates (c,d) is a
subset of words whose earliest previous coordinate is d. -/
theorem lossEarliestActualEdgeCarrier_subset_earliestPair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d) :
    lossEarliestActualEdgeCarrier C exponent choice c d p ⊆
      lossEarliestPairWords (lossSliceAtNat C exponent choice)
        c.val d.val := by
  classical
  intro word hw
  rw [lossEarliestPairWords_eq_biUnion_actualEdge
    C exponent choice c d]
  exact Finset.mem_biUnion.mpr ⟨p, hp, hw⟩

/-- A duplicate event of later coordinate c cannot be attributed
simultaneously to an actual retained-edge source/blocker pair from
two distinct earlier coordinates d and e. -/
theorem lossEarliestActualEdgeCarrier_disjoint_of_distinct_prior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d e : Fin n}
    (hdc : d < c) (hec : e < c) (hde : d ≠ e)
    {p q : V × V}
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    (hq : q ∈ crossLossConflictPairs C exponent choice c e) :
    Disjoint
      (lossEarliestActualEdgeCarrier C exponent choice c d p)
      (lossEarliestActualEdgeCarrier C exponent choice c e q) := by
  classical
  have hd : d.val ∈ Finset.range c.val :=
    Finset.mem_range.mpr hdc
  have he : e.val ∈ Finset.range c.val :=
    Finset.mem_range.mpr hec
  have hne : d.val ≠ e.val := by
    intro hv
    exact hde (Fin.ext hv)
  have houter :=
    lossEarliestPairWords_pairwiseDisjoint
      (lossSliceAtNat C exponent choice) c.val hd he hne
  change Disjoint
    (lossEarliestPairWords (lossSliceAtNat C exponent choice)
      c.val d.val)
    (lossEarliestPairWords (lossSliceAtNat C exponent choice)
      c.val e.val) at houter
  rw [Finset.disjoint_left] at houter ⊢
  intro word hwD hwE
  exact houter
    (lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hwD)
    (lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c e q hq hwE)

#print axioms lossEarliestActualEdgeCarrier_subset_earliestPair
#print axioms lossEarliestActualEdgeCarrier_disjoint_of_distinct_prior

end OrderedEdgeColoring
end JSP000404Research
