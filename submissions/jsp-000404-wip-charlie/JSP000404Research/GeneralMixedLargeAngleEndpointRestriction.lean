import JSP000404Research.GeneralMixedHiddenAngleFrontier
import Mathlib.Tactic

/-!
# Endpoint restriction for genuine large angles at the mixed support-two centre

The cardinality-free sharp/support-one/support-two pattern forces a
strict upper bound on angle(s,b,c) whenever c is a fourth distinct
centre.  Thus any actual large angle at b whose one endpoint is the
sharp centre s must have the OTHER endpoint equal to the distinguished
support-one centre a.

This precisely localizes one portion of the remaining large-quotient
witness geometry.  It does not assert that the large witness includes
s, nor exclude large angles between two unrelated endpoints.
-/

namespace JSP000404Research

theorem general_mixed_large_angle_sharp_endpoint_forces_support_one
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
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2)
    (x y : OtherVertex b)
    (hxy : x ≠ y)
    (hlarge :
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p b) (p y.1))
    (hx : x.1 = s) :
    y.1 = a := by
  by_contra hya
  have hsc : s ≠ y.1 := by
    intro hsy
    apply hxy
    exact Subtype.ext (hx.trans hsy)
  have hac : a ≠ y.1 := by
    intro hay
    exact hya hay.symm
  have hbc : b ≠ y.1 := y.2.symm
  have hupper :=
    general_mixed_hidden_angle_strict_upper
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  have hlarge' :
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p s) (p b) (p y.1) := by
    simpa [hx] using hlarge
  have htpos : 0 < t := by
    have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [ht]
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hnonneg : 0 ≤ delta * lam :=
    mul_nonneg hdelta0 hlampos.le
  nlinarith

#print axioms general_mixed_large_angle_sharp_endpoint_forces_support_one

end JSP000404Research
