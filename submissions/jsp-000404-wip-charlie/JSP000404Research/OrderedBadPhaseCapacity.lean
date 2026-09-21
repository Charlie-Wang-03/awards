import JSP000404Research.WeightedBadPhaseCapacity
import JSP000404Research.OrderedEdgeColor
import Mathlib.Tactic

/-!
# Ordered-colouring specialization of weighted bad-phase tolerance

For an OrderedEdgeColoring by n+1 colours, take active(v) to be its actual
incident-colour count.  Weighted Hansel supplies the required global upper
bound automatically.

Hence any geometric construction which proves

  active(v) <= n - exponent(v) + 1

at every vertex, and whose over-budget vertices have total dyadic weight at
most one, already proves the sharp n-bit capacity.
-/

namespace JSP000404Research

open scoped BigOperators

namespace OrderedEdgeColoring

def activeBadWeight
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : ℕ :=
  badPhaseWeight n exponent (fun v => (active C v).card)

theorem dyadic_capacity_of_activeBadWeight_le_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hbad :
      activeBadWeight C exponent ≤ 1) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  apply dyadic_capacity_of_badPhaseWeight_le_one
    n exponent (fun v => (active C v).card)
    hexp honeLoss
  · simpa using C.weighted_capacity
  · exact hbad

/-- Structural version: it is enough that every over-budget vertex has
exponent zero and that at most one vertex is over budget. -/
theorem dyadic_capacity_of_atMostOne_zeroExponent_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hzero :
      ∀ v,
        n - exponent v < (active C v).card →
        exponent v = 0)
    (huniq :
      ∀ v w,
        n - exponent v < (active C v).card →
        n - exponent w < (active C w).card →
        v = w) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  apply dyadic_capacity_of_activeBadWeight_le_one
    C exponent hexp honeLoss
  exact badPhaseWeight_le_one_of_bad_zero_unique
    n exponent (fun v => (active C v).card)
    hzero huniq

#print axioms dyadic_capacity_of_activeBadWeight_le_one
#print axioms dyadic_capacity_of_atMostOne_zeroExponent_bad

end OrderedEdgeColoring

end JSP000404Research
