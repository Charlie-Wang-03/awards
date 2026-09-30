import JSP000404Research.MiddleHiddenOuterAmplification
import JSP000404Research.DeficitThreeSupportOneGeometry
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Support-one amplification of a middle-hidden outer transition

In the six-point mixed hard branch, let top have exponent n-1 and let a be an
n-3/support-one minimum.  The top centre is sharp, so the triangle
top-i-a gives

  ((n-2)-delta)*lambda <= angle(top,i,a)

for every third centre i.

If i also carries an enriched middle-hidden support-three pattern, the
zero-angle budget transfers this to one of the two outer transition edges:

  ((n-2)-2*delta)*lambda <= angle(top,i,r)

or

  ((n-2)-2*delta)*lambda <= angle(d,i,top).

This is the quantitative bridge from the support-one minimum to a specific
outer transition of every middle-hidden support-three centre.
-/

namespace JSP000404Research

open Real

theorem middle_hidden_outer_strengthened_by_support_one
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i a : V}
    (hit : i ≠ top)
    (haTop : a ≠ top)
    (haI : a ≠ i)
    (Ctop : CentreProjectiveCycle hp top)
    (Ca : CentreProjectiveCycle hp a)
    (hTop : centreExponent Ctop t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam) :
    (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p top) (p i) (p M.r.1)
      ∨
    (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p M.d.1) (p i) (p top) := by
  have hdelta1 : delta < 1 := by linarith
  have hsharp :
      SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      top Ctop hTop
  have hlarge :
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p top) (p i) (p a) :=
    sharp_and_deficit_three_support_one_force_large_outer_angle
      hp hcap hn hdelta0 ht hlam
      haTop.symm hit.symm haI
      hsharp Ca hA hsupA
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hout :=
    M.outer_large_of_large_to_other_vertex
      hcard hit haTop haI hdelta0 hlampos hlarge
  rcases hout with hleft | hright
  · left
    convert hleft using 1 <;> ring
  · right
    convert hright using 1 <;> ring

#print axioms middle_hidden_outer_strengthened_by_support_one

end JSP000404Research
