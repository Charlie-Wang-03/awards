import JSP000404Research.PlanarThreeIntegerCardinalityCap
import JSP000404Research.PlanarKnownSmallCentreCapacity
import JSP000404Research.ThreeFiveExactScaleFullCapacity
import JSP000404Research.PlanarThreeManyIntegerNextPacking
import Mathlib.Tactic

/-!
# ALL-CARDINALITY original AngleCap dyadic capacity at exact n=3, delta=0

The previous geometric proofs closed n=3, delta=0 for exactly five
and exactly six original centres. We now eliminate every possible
LARGER original configuration using the strict-support interval
packing theorem, which gives #centres <= 6 at the actual integer
scale t=3, lambda=pi/3. The existing unconditional small-centre
capacity (<=4) and genuine five-/six-centre capacities then exhaust
every original finite planar configuration.

This is a COMPLETE unconditional geometric lower-branch CAPACITY
statement at n=3, delta=0 with NO upper bound on input cardinality.
Every quantifier refers to the original AngleCap points and their
actual projective cycles. It does not imply the n=3 positive-delta
branch nor any arbitrary-n true-hole payment.

The root admitted theorem can now close its ENTIRE n=3,delta=0
disjunct before the sole remaining global admitted obligation.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open scoped BigOperators

/-- For the ENTIRE n=3 exact-integer strip (no cardinality bound),
original AngleCap alone proves sharp 3-bit dyadic capacity. -/
theorem planar_three_integer_all_centre_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 8 := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcapRe : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  have htThree : t = (3 : ℝ) := by
    rw [hdeltaExact] at ht
    simpa using ht
  have hcard6 : Fintype.card (ProjectionOrdered V) ≤ 6 :=
    planar_three_integer_card_le_six
      (reindexedPoint_injective hp) hcapRe
      htThree hlam cycles
  by_cases hcard4 : Fintype.card (ProjectionOrdered V) ≤ 4
  · have hsmall :
        Fintype.card (ProjectionOrdered V) ≤ 2 ∨
        (Fintype.card (ProjectionOrdered V) = 3 ∧ 2 ≤ (3 : ℕ)) ∨
        (Fintype.card (ProjectionOrdered V) = 4 ∧ 3 ≤ (3 : ℕ)) := by
      omega
    have hbound :=
      planar_lower_branch_known_small_centre_dyadic_capacity
        hp hcap (by decide : 1 ≤ (3 : ℕ))
        hdelta0 hdeltaHalf ht hlam cycles hsmall
    simpa using hbound
  · have hcard56 :
        Fintype.card (ProjectionOrdered V) = 5 ∨
          Fintype.card (ProjectionOrdered V) = 6 := by omega
    rcases hcard56 with hfive | hsix
    · exact planar_three_five_exact_three_scale_dyadic_capacity
        (reindexedPoint_injective hp) hcapRe hfive
        hdelta0 hdeltaHalf hdeltaExact ht hlam cycles
    · exact planar_three_six_exact_integer_dyadic_capacity
        (reindexedPoint_injective hp) hcapRe hsix
        hdelta0 hdeltaHalf hdeltaExact ht hlam cycles

#print axioms planar_three_integer_all_centre_dyadic_capacity

end ProjectionOrdered
end JSP000404Research
