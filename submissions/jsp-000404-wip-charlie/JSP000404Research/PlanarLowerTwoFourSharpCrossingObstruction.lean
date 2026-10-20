import JSP000404Research.PlanarLowerTwoAllCentresExposed
import JSP000404Research.ConcreteSharpCentre
import JSP000404Research.StrictExposureConvexHull
import JSP000404Research.CrossingDiagonalsQuadrilateralAngleSum
import JSP000404Research.PlanarLowerTwoFourSharpAngleBudget
import Mathlib.Tactic

/-!
# Actual four-centre sharp obstruction whenever the opposite diagonals cross

Under genuine lower-branch n=2 AngleCap, all centres are strictly exposed.
An exponent-one centre is sharp, so the interior angle at that vertex is
<=delta*lambda. If the opposite segments of four distinct vertices intersect,
the existing crossing-diagonal quadrilateral theorem yields interior-angle
sum 2*pi, and the genuine AngleCap at each other vertex contradicts the
new sharp quadrilateral budget.

No fake boolean hole credits are involved. The geometric step not proved
by this module is that for any four strictly exposed planar vertices, at
least one pairing of opposite diagonals intersects.
-/

namespace JSP000404Research

theorem lower_two_no_sharp_of_crossing_diagonals
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s b c d : V}
    (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcross :
      (segment ℝ (p s) (p c) ∩ segment ℝ (p b) (p d)).Nonempty)
    (hsharpExp : centreExponent (C s) t = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hSharp : SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp hp hcap
      (by omega : 2 ≤ 2) hdelta0 hdelta1
      (by simpa only [Nat.cast_ofNat] using ht)
      hlam s (C s) (by simpa using hsharpExp)
  have hExpS : StrictlyExposedAt p s :=
    lower_two_all_centres_strictlyExposed
      hp hcap hdelta0 hdeltaHalf ht hlam C s
  have hExpC : StrictlyExposedAt p c :=
    lower_two_all_centres_strictlyExposed
      hp hcap hdelta0 hdeltaHalf ht hlam C c
  have hHullS :
      p s ∉ convexHull ℝ ({p b,p c,p d} : Set Plane) :=
    strictlyExposedAt_not_mem_convexHull_three
      hsb.symm hsc.symm hsd.symm hExpS
  have hHullC :
      p c ∉ convexHull ℝ ({p s,p b,p d} : Set Plane) :=
    strictlyExposedAt_not_mem_convexHull_three
      hsc hbc hcd.symm hExpC
  have hsum :=
    crossing_diagonals_four_angles_sum_two_pi
      (a := p s) (b := p b) (c := p c) (d := p d)
      (hp.ne hsb) (hp.ne hsc) (hp.ne hsd)
      (hp.ne hbc) (hp.ne hbd) (hp.ne hcd)
      hHullS hHullC hcross
  have hS :
      EuclideanGeometry.angle (p b) (p s) (p d) ≤ delta * lam :=
    hSharp b d hsb.symm hsd.symm hbd
  have hB :
      EuclideanGeometry.angle (p s) (p b) (p c) ≤ Real.pi - lam :=
    hcap s b c hsb hsc hbc
  have hC :
      EuclideanGeometry.angle (p b) (p c) (p d) ≤ Real.pi - lam :=
    hcap b c d hbc hbd hcd
  have hD :
      EuclideanGeometry.angle (p c) (p d) (p s) ≤ Real.pi - lam :=
    hcap c d s hcd hsc.symm hsd.symm
  exact four_sharp_quadrilateral_angle_budget_contradiction
    hdelta0 hdeltaHalf ht hlam hS hB hC hD hsum

#print axioms lower_two_no_sharp_of_crossing_diagonals

end JSP000404Research
