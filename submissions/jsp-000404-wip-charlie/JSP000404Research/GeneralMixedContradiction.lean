import JSP000404Research.GeneralMixedDiameterObstruction
import JSP000404Research.SharpPinnedSupportTwoCluster
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Complete mixed four-centre obstruction in arbitrary finite configurations

The original geometric AngleCap and three-centre quotient profile (one sharp
source s, support-one a, support-two b) force both:

  * a non-sharp-ray diameter ≤ delta * lambda at b (pinned sharp ray,
    precisely two positive quotient gaps, and zero-gap angle mass);
  * the actual fourth ray c to support-one ray a has angle
    angle(c,b,a) > delta * lambda (base triangle angle diameter and exact
    sharp hidden-angle restriction).

Their contradiction proves the original no-top-mixed-with-fourth theorem
without restricting to Fin 4, without replacing actual Euclidean angles,
and without introducing any new unproved payment or axiom.

This is a geometric *subcase* theorem, not the original all-configuration
global dyadic capacity theorem.
-/

namespace JSP000404Research

theorem no_top_mixed_deficitTwo_with_fourth
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
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hsharp : SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      s Cs hS
  have hcluster : OuterSmallAwayFrom p delta lam s b :=
    supportTwo_outerSmallAwayFrom_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsharp Cb hB hsupB
  exact no_general_mixed_fourth_of_outerSmallAwayFrom
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc
    Cs Ca Cb hS hA hB hsupA hsupB hcluster

#print axioms no_top_mixed_deficitTwo_with_fourth

end JSP000404Research
