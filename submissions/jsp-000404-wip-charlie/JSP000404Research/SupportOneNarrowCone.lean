import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.CutBandSmallAngle
import Mathlib.Tactic

/-!
# Quantitative narrow cone from a support-one transition certificate

A HighExponentTransitionIntervalCertificate represents every displacement from
the centre by a positive scalar times one common signed ray family with angle
parameter in [a,a+width].  Hence every angle between two neighbours is at most
width.

At a second-layer support-one centre, the transition quotient is n-1.  Since
qe <= t*ge and width = pi*(1-ge), with t=n+delta and lambda=pi/t, this sharpens
to

  width <= (1+delta)*lambda.

Thus every pair of rays seen from such a centre has actual angle at most
(1+delta)*lambda.
-/

namespace JSP000404Research

theorem transitionCertificate_actual_angle_le_width
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} {i : V}
    (C : CentreProjectiveCycle hp i)
    (H : HighExponentTransitionIntervalCertificate hp t i C)
    {j k : V}
    (hji : j ≠ i)
    (hki : k ≠ i) :
    EuclideanGeometry.angle (p j) (p i) (p k) ≤ H.width := by
  obtain ⟨rhoj,thetaj,hrhoj,hjlo,hjhi,hjrepr⟩ :=
    H.repr j hji
  obtain ⟨rhok,thetak,hrhok,hklo,hkhi,hkrepr⟩ :=
    H.repr k hki
  have hdiff :
      |thetaj - thetak| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [H.width_nonneg, H.width_lt_pi]
  have hwidth :
      |thetaj - thetak| ≤ H.width := by
    rw [abs_le]
    constructor <;> linarith
  change
    InnerProductGeometry.angle
      (p j - p i) (p k - p i) ≤ H.width
  rw [hjrepr,hkrepr,
      angle_positive_smul_signedRay hrhoj hrhok,
      angle_signedRayDirection_eq_of_sign_eq rfl hdiff]
  exact hwidth

theorem secondLayer_supportOne_transition_width_le_one_add_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1)
    (H : HighExponentTransitionIntervalCertificate hp t i C) :
    H.width ≤ (1 + delta) * lam := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hqe :
      H.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        C H hsupport
    rw [hexp] at h
    omega
  have hqeLe :
      ((n - 1 : ℕ) : ℝ) ≤ t * H.ge := by
    rw [← hqe]
    exact H.qe_le
  have hcore :
      t * (1 - H.ge) ≤ 1 + delta := by
    rw [ht] at hqeLe ⊢
    push_cast at hqeLe ⊢
    nlinarith
  have hpiMul :
      Real.pi * (t * (1 - H.ge))
        ≤ Real.pi * (1 + delta) :=
    mul_le_mul_of_nonneg_left hcore Real.pi_pos.le
  have hscaled :
      H.width * t ≤ (1 + delta) * Real.pi := by
    rw [H.width_eq]
    nlinarith [hpiMul]
  rw [hlam]
  have hdiv :
      H.width ≤ ((1 + delta) * Real.pi) / t :=
    (le_div_iff₀ htpos).2 (by
      simpa [mul_comm] using hscaled)
  convert hdiv using 1 <;> ring

theorem secondLayer_supportOne_all_angles_le_one_add_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1)
    (H : HighExponentTransitionIntervalCertificate hp t i C)
    {j k : V}
    (hji : j ≠ i)
    (hki : k ≠ i) :
    EuclideanGeometry.angle (p j) (p i) (p k)
      ≤ (1 + delta) * lam := by
  exact
    (transitionCertificate_actual_angle_le_width
      hp C H hji hki).trans
      (secondLayer_supportOne_transition_width_le_one_add_delta_lam
        hn3 hdelta0 ht hlam C hexp hsupport H)

#print axioms transitionCertificate_actual_angle_le_width
#print axioms secondLayer_supportOne_transition_width_le_one_add_delta_lam
#print axioms secondLayer_supportOne_all_angles_le_one_add_delta_lam

end JSP000404Research
