import JSP000404Research.SupportOneNarrowCone
import Mathlib.Tactic

/-!
# Narrow cone from a transition quotient n-1

The quantitative part of SupportOneNarrowCone does not actually require
positiveSupport=1.  It only uses the distinguished transition quotient
qe=n-1.

For any high-exponent transition certificate with qe=n-1,

  qe <= t*ge,
  width = pi*(1-ge),

hence in the lower Sendov branch t=n+delta,

  width <= (1+delta)*lambda.

Therefore every pair of rays seen from the centre has angle at most
(1+delta)*lambda.
-/

namespace JSP000404Research

theorem transition_n_sub_one_width_le_one_add_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : CentreProjectiveCycle hp i)
    (H : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : H.qe = n - 1) :
    H.width ≤ (1 + delta) * lam := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
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

theorem transition_n_sub_one_all_angles_le_one_add_delta_lam
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
    (H : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : H.qe = n - 1)
    {j k : V}
    (hji : j ≠ i)
    (hki : k ≠ i) :
    EuclideanGeometry.angle (p j) (p i) (p k)
      ≤ (1 + delta) * lam := by
  exact
    (transitionCertificate_actual_angle_le_width
      hp C H hji hki).trans
      (transition_n_sub_one_width_le_one_add_delta_lam
        hn3 hdelta0 ht hlam C H hqe)

#print axioms transition_n_sub_one_width_le_one_add_delta_lam
#print axioms transition_n_sub_one_all_angles_le_one_add_delta_lam

end JSP000404Research
