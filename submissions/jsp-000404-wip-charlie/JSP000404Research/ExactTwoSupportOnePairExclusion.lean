import JSP000404Research.SupportOneNarrowCone
import JSP000404Research.SupportTwoThreeMarkedSmallPair
import Mathlib.Tactic

/-!
# Exact-two mixed triangle exclusion

Two second-layer support-one centres are globally narrow: every angle between
two rays from either centre is at most (1+delta)*lambda.

If a support-two centre sees those two support-one centres under a
delta*lambda-small angle, then the triangle formed by the three centres has
all three angles bounded by

  (1+delta)*lambda, (1+delta)*lambda, delta*lambda.

For n>=3 and delta<1/2 their sum is strictly below
(n+delta)*lambda = pi, contradiction.
-/

namespace JSP000404Research

theorem coeff_two_supportOne_plus_delta_lt_t
    {n : ℕ} {delta t : ℝ}
    (hn3 : 3 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta) :
    2 * (1 + delta) + delta < t := by
  rw [ht]
  push_cast
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  linarith

theorem impossible_two_supportOne_bounds_and_delta_third
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c)
        ≤ (1 + delta) * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c)
        ≤ (1 + delta) * lam)
    (hc :
      EuclideanGeometry.angle (p a) (p c) (p b)
        ≤ delta * lam) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcoeff :=
    coeff_two_supportOne_plus_delta_lt_t
      hn3 hdeltaHalf ht
  have hpiEq : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hsumLt :
      (2 * (1 + delta) + delta) * lam < Real.pi := by
    have hmul :=
      mul_lt_mul_of_pos_right hcoeff hlampos
    rw [hpiEq] at hmul
    exact hmul
  have htri :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p a) (p c)
      (hp.ne hab.symm)
  have hcommA :
      EuclideanGeometry.angle (p c) (p a) (p b) =
        EuclideanGeometry.angle (p b) (p a) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommC :
      EuclideanGeometry.angle (p b) (p c) (p a) =
        EuclideanGeometry.angle (p a) (p c) (p b) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommA,hcommC] at htri
  nlinarith

theorem supportTwo_small_pair_not_two_supportOne_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o₁ o₂ s : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s : o₁ ≠ s)
    (ho2s : o₂ ≠ s)
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
    (hsmall :
      EuclideanGeometry.angle (p o₁) (p s) (p o₂)
        ≤ delta * lam) :
    False := by
  have ha :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp hn3 hdelta0 ht hlam
      Co1 ho1Exp ho1Support Ho1
      ho12.symm ho1s.symm
  have hb :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp hn3 hdelta0 ht hlam
      Co2 ho2Exp ho2Support Ho2
      ho12 ho2s.symm
  exact impossible_two_supportOne_bounds_and_delta_third
    hp hn3 hdelta0 hdeltaHalf ht hlam
    ho12 ho1s ho2s
    ha hb
    (by simpa [EuclideanGeometry.angle_comm] using hsmall)

#print axioms coeff_two_supportOne_plus_delta_lt_t
#print axioms impossible_two_supportOne_bounds_and_delta_third
#print axioms supportTwo_small_pair_not_two_supportOne_centres

end JSP000404Research
