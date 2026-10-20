import JSP000404Research.PlanarFirstBranchNoThree
import JSP000404Research.PlanarKnownSmallCentreCapacity
import Mathlib.Tactic

/-!
# True planar lower branch: n = 1 is completely closed

For t = 1 + delta and 0 <= delta < 1/2, the real planar AngleCap
forbids three different centres. The projectively reindexed point
configuration therefore has at most two vertices, and the exact
lower-branch dyadic capacity follows without any six-source payment.

This is a genuine unconditional geometric subcase of the original
projected goal, not a weakened debt-payment hypothesis.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_lower_branch_n_one_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (1 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ (2 : ℕ) ^ 1 := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcapRe : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  have hcard : Fintype.card (ProjectionOrdered V) ≤ 2 :=
    original_card_le_two_of_lower_one
      (reindexedPoint_injective hp) hcapRe
      hdelta0 hdeltaHalf ht hlam
  exact planar_lower_branch_known_small_centre_dyadic_capacity
    hp hcap (by omega : 1 ≤ 1)
    hdelta0 hdeltaHalf (by simpa only [Nat.cast_one] using ht)
    hlam cycles (Or.inl hcard)

#print axioms planar_lower_branch_n_one_dyadic_capacity

end ProjectionOrdered
end JSP000404Research
