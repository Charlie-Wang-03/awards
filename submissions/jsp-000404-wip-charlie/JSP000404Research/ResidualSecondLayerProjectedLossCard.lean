import JSP000404Research.ResidualProjectedLossCore
import Mathlib.Tactic

/-!
# Lightweight second-layer projected-loss cardinality

A projected-loss vertex satisfies
  exponent v = projectedFree C v + 1.
At the second layer exponent v = n - 2, so the retained-active palette has
exactly three coordinates.

This elementary fact is intentionally isolated from minimal-deficiency and
whole-cube augmenting machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem secondLayer_projectedLoss_retainedActive_card_eq_three_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (retainedActive C v).card = 3 := by
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  rw [hvSecond] at hloss
  have hcardLe :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  omega

theorem secondLayer_projectedLoss_retainedActive_card_eq_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (_hn3 : 3 ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (retainedActive C v).card = 3 :=
  secondLayer_projectedLoss_retainedActive_card_eq_three_core
    C exponent hvLoss hvSecond

#print axioms secondLayer_projectedLoss_retainedActive_card_eq_three_core
#print axioms secondLayer_projectedLoss_retainedActive_card_eq_three

end OrderedEdgeColoring
end JSP000404Research
