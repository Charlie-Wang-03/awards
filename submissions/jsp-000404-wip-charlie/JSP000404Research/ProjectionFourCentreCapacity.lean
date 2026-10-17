import JSP000404Research.GenericFourCentreCapacity
import JSP000404Research.GenericTopExponentMultiplicity
import Mathlib.Tactic

/-!
# Projection-indexed four-original-centre branch of the GLOBAL dyadic goal

This theorem proves, without any hole/surplus premise, the exact statement
shape of the admitted root for the genuine |ProjectionOrdered V| = 4,
n >= 3 subcase. The original cycles are used unchanged, on the actual
projection order. This establishes a genuinely closed disjunct of the
global theorem, not merely a formal rephrasing of the six-source payment.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_lower_branch_card_four_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card (ProjectionOrdered V) = 4)
    (hn : 3 ≤ n)
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
  exact four_centre_card_four_dyadic_capacity
    (reindexedPoint_injective hp)
    hcapRe hcard hn hdelta0 hdeltaHalf ht hlam cycles

#print axioms planar_lower_branch_card_four_dyadic_capacity

end ProjectionOrdered
end JSP000404Research
