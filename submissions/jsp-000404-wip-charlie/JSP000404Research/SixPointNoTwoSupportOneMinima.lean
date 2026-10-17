import JSP000404Research.ThirdLayerTwoSupportOneExclusion
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Two deficit-three support-one minima cannot coexist with a sharp top

In the six-point third-layer profile, the top exponent n-1 is SharpAt.

If a minimum a has exponent n-3 and quotient support one, every genuine angle
at a is at most

  (2+delta) * lambda.

But the same support-one geometry, viewed in triangle top-a-b, forces the
angle at every third vertex b to be at least

  (n-2-delta) * lambda.

If b is itself another support-one n-3 minimum, its all-angle upper bound
applies to that same angle.  For n>=5 and delta<1/2,

  n-2-delta > 2+delta.

Contradiction.
-/

namespace JSP000404Research

theorem no_sharp_with_two_deficit_three_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a)
    (hsb : s ≠ b)
    (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hB : centreExponent Cb t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hSharp : SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n) hdelta0 hdelta1 ht hlam s Cs hS
  exact no_two_third_support_one_around_sharp_n_ge_five
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hab hSharp Ca Cb hA hB hsupA hsupB

#print axioms no_sharp_with_two_deficit_three_support_one

end JSP000404Research
