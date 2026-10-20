import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Exact planar angle-budget obstruction for a four-centre sharp point at n=2

For t=2+delta, lambda=pi/t and 0<=delta<1/2, four *convex
quadrilateral* interior angles cannot have sum 2*pi if one is at most
delta*lambda (a sharp centre) and each other angle is at most pi-lambda.

This module proves the quantitative inconsistency, unconditionally and
without any admitted theorem. To apply it to four ORIGINAL planar vertices,
one still must formalize the genuine geometric dichotomy and its angle-sum:
  (i) an AngleCap configuration at this lambda has no point inside the
      triangle of its other three vertices;
  (ii) therefore all four vertices are in convex position;
  (iii) its four appropriate interior angles add to 2*pi.

These are NOT assumed to follow from AngleCap in this theorem.
In particular, this is not yet a proof of the n=2 four-centre branch.
-/

namespace JSP000404Research

open Real

theorem four_sharp_quadrilateral_angle_budget_contradiction
    {t delta lam a b c d : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = 2 + delta)
    (hlam : lam = Real.pi / t)
    (hsharp : a ≤ delta * lam)
    (hb : b ≤ Real.pi - lam)
    (hc : c ≤ Real.pi - lam)
    (hd : d ≤ Real.pi - lam)
    (hsum : a + b + c + d = 2 * Real.pi) :
    False := by
  have htpos : 0 < t := by rw [ht]; linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [ht] at hpi
  have hgap : 0 < (1 - 2 * delta) * lam :=
    mul_pos (by linarith) hlampos
  nlinarith

#print axioms four_sharp_quadrilateral_angle_budget_contradiction

end JSP000404Research
