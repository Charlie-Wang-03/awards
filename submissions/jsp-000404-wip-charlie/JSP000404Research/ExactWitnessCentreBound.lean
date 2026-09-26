
import JSP000404Research.ExactWitnessUnitQuotient
import JSP000404Research.ConcreteSharpCentre
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# The centre of an exact maximum-angle witness is never top exponent

Let W=(a,b,c) attain the exact angle cap

  angle(a,b,c) = pi-lambda.

If b had exponent n-1 in the lower Sendov branch, ConcreteSharpCentre would
make b a SharpAt centre, so every angle at b would be at most delta*lambda.

But pi = t*lambda = (n+delta)*lambda, hence

  pi-lambda = (n+delta-1)*lambda > delta*lambda

for n>=3 and lambda>0.  Contradiction.

Together with the universal exponent<n bound this gives k_b<=n-2.
-/

namespace JSP000404Research

theorem exactWitness_centre_ne_topExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b) :
    centreExponent C t ≠ n - 1 := by
  intro hexp
  have hdelta1 : delta < 1 := by linarith
  have hsharp :
      SharpAt p delta lam W.b :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      W.b C hexp
  have hsharpWitness :
      EuclideanGeometry.angle
          (p W.a) (p W.b) (p W.c)
        ≤ delta * lam :=
    hsharp W.a W.c
      W.hab W.hbc.symm W.hac
  rw [W.exact] at hsharpWitness
  have htpos :
      0 < t :=
    sendov_scale_pos
      (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hpi :
      Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hpi, ht] at hsharpWitness
  nlinarith

theorem exactWitness_centreExponent_le_n_sub_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b) :
    centreExponent C t ≤ n - 2 := by
  have hdelta1 : delta < 1 := by linarith
  have hlt :
      centreExponent C t < n :=
    centreExponent_lt_n
      C n delta t
      (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hne :=
    exactWitness_centre_ne_topExponent
      hp hcap hn hdelta0 hdeltaHalf ht hlam W C
  omega

#print axioms exactWitness_centre_ne_topExponent
#print axioms exactWitness_centreExponent_le_n_sub_two

end JSP000404Research
