import JSP000404Research.ExactTwoCrossedSmallPairMatching
import Mathlib.Tactic

/-!
# Crossed exact-two cycle contradicts a convex quadrilateral angle sum

For either crossed small-pair matching, the corresponding four-cycle has two
support-one vertex angles bounded by (1+delta)*lambda and two support-two
vertex angles bounded by delta*lambda.

If that four-cycle is the convex-hull boundary, its four interior angles sum to
2*pi.  But their total upper bound is

  (2 + 4*delta) * lambda

which is strictly below 2*pi = 2*(n+delta)*lambda for n>=3 and delta<1/2.

Thus the only remaining geometric issue is to identify the convex-hull cycle.
-/

namespace JSP000404Research

theorem crossed_cycle_coeff_lt_two_t
    {n : ℕ} {delta t : ℝ}
    (hn3 : 3 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta) :
    2 * (1 + delta) + 2 * delta < 2 * t := by
  rw [ht]
  push_cast
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  linarith

theorem impossible_crossed_cycle_of_four_angle_sum_two_pi
    {V : Type*} {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o₁ s₁ s₂ o₂ : V}
    (ho1 :
      EuclideanGeometry.angle (p s₁) (p o₁) (p o₂)
        ≤ (1 + delta) * lam)
    (hs1 :
      EuclideanGeometry.angle (p o₁) (p s₁) (p s₂)
        ≤ delta * lam)
    (hs2 :
      EuclideanGeometry.angle (p s₁) (p s₂) (p o₂)
        ≤ delta * lam)
    (ho2 :
      EuclideanGeometry.angle (p s₂) (p o₂) (p o₁)
        ≤ (1 + delta) * lam)
    (hsum :
      EuclideanGeometry.angle (p s₁) (p o₁) (p o₂) +
      EuclideanGeometry.angle (p o₁) (p s₁) (p s₂) +
      EuclideanGeometry.angle (p s₁) (p s₂) (p o₂) +
      EuclideanGeometry.angle (p s₂) (p o₂) (p o₁)
        = 2 * Real.pi) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcoeff :=
    crossed_cycle_coeff_lt_two_t hn3 hdeltaHalf ht
  have hpiEq : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hbound :
      (2 * (1 + delta) + 2 * delta) * lam
        < 2 * Real.pi := by
    have hmul := mul_lt_mul_of_pos_right hcoeff hlampos
    rw [mul_assoc, hpiEq] at hmul
    simpa [mul_add, add_mul] using hmul
  nlinarith

/-- First crossed matching: s1 pairs s2 with o1, while s2 pairs s1 with o2.
If cycle o1-s1-s2-o2 is a convex boundary cycle, contradiction. -/
theorem impossible_first_crossed_matching_of_boundary_angle_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o₁ o₂ s₁ s₂ : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (Co1 : CentreProjectiveCycle hp o₁)
    (Co2 : CentreProjectiveCycle hp o₂)
    (ho1Exp : centreExponent Co1 t = n - 2)
    (ho2Exp : centreExponent Co2 t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient Co1 t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co2 t) = 1)
    (Ho1 : HighExponentTransitionIntervalCertificate hp t o₁ Co1)
    (Ho2 : HighExponentTransitionIntervalCertificate hp t o₂ Co2)
    (hs1 :
      EuclideanGeometry.angle (p s₂) (p s₁) (p o₁)
        ≤ delta * lam)
    (hs2 :
      EuclideanGeometry.angle (p o₂) (p s₂) (p s₁)
        ≤ delta * lam)
    (hsum :
      EuclideanGeometry.angle (p s₁) (p o₁) (p o₂) +
      EuclideanGeometry.angle (p o₁) (p s₁) (p s₂) +
      EuclideanGeometry.angle (p s₁) (p s₂) (p o₂) +
      EuclideanGeometry.angle (p s₂) (p o₂) (p o₁)
        = 2 * Real.pi) :
    False := by
  have ho1Angle :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp hn3 hdelta0 ht hlam
      Co1 ho1Exp ho1Support Ho1
      ho1s1.symm ho12.symm
  have ho2Angle :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp hn3 hdelta0 ht hlam
      Co2 ho2Exp ho2Support Ho2
      ho2s2.symm ho12
  exact impossible_crossed_cycle_of_four_angle_sum_two_pi
    hn3 hdelta0 hdeltaHalf ht hlam
    ho1Angle
    (by simpa [EuclideanGeometry.angle_comm] using hs1)
    (by simpa [EuclideanGeometry.angle_comm] using hs2)
    ho2Angle hsum

#print axioms crossed_cycle_coeff_lt_two_t
#print axioms impossible_crossed_cycle_of_four_angle_sum_two_pi
#print axioms impossible_first_crossed_matching_of_boundary_angle_sum

end JSP000404Research
