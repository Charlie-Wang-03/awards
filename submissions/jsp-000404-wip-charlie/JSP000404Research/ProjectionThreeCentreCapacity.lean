import JSP000404Research.GenericThreeCentreCapacity
import JSP000404Research.GenericTopExponentMultiplicity
import Mathlib.Tactic

/-!
# Closed card=3 n>=2 branch of the exact projected global dyadic goal

This is proved on the original projection order and cycles, with no
six-source Boolean debt payment assumption and no executable sorry.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_lower_branch_card_three_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card (ProjectionOrdered V) = 3)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcapRe : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  exact three_centre_card_three_dyadic_capacity
    (reindexedPoint_injective hp)
    hcapRe hcard hn hdelta0 hdeltaHalf ht hlam cycles

#print axioms planar_lower_branch_card_three_dyadic_capacity

end ProjectionOrdered
end JSP000404Research
