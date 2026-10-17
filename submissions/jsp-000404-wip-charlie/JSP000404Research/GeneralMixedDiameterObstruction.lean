import JSP000404Research.GeneralMixedOtherRaySeparation
import JSP000404Research.GeneralSupportTwoMultiplicity
import Mathlib.Tactic

/-!
# Exact reduction of a genuine mixed four-centre contradiction to pinned cluster diameter

The new AngleCap-derived strict separation angle(c,b,a) > delta*lambda
contradicts the non-sharp-ray diameter bound OuterSmallAwayFrom at the
support-two centre b. The diameter bound is NOT assumed unconditionally;
this theorem records precisely the remaining pinned-cycle geometric input.

No Boolean hole, credit assignment, or unrestricted six-source payment is
inferred from this local mixed obstruction.
-/

namespace JSP000404Research

theorem no_general_mixed_fourth_of_outerSmallAwayFrom
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2)
    (houter : OuterSmallAwayFrom p delta lam s b) :
    False := by
  have hlarge :=
    general_mixed_support_one_ray_delta_separated_from_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  have hsmall :
      EuclideanGeometry.angle (p c) (p b) (p a) ≤ delta * lam :=
    houter c a hbc.symm hab.symm hsc.symm hsa.symm hac.symm
  exact not_lt_of_ge hsmall hlarge

#print axioms no_general_mixed_fourth_of_outerSmallAwayFrom

end JSP000404Research
