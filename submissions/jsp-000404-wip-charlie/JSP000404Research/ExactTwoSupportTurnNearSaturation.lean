import JSP000404Research.SupportIntervalCertificate
import JSP000404Research.SupportLeTwoTransitionInterval
import Mathlib.Tactic

/-!
# Near-saturation of the support-turn circle in the exact-two terminal

For two second-layer support-one centres and two unit-transition support-two
centres, the distinguished transition quotients are

  n-1, n-1, 1, 1.

Each quotient q contributes at least q*lambda to the corresponding dual
support-turn interval.  Four support intervals pack into total length at most
2*pi.  Hence the exact-two terminal satisfies

  2*n*lambda <= total turn <= 2*pi.

Since pi=(n+delta)*lambda, the unused support-turn slack is at most
2*delta*lambda, strictly below one lambda unit in the lower branch.
-/

namespace JSP000404Research

open SupportIntervalCertificate

theorem exactTwo_four_transition_turns_near_saturate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
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
    (Cs1 : CentreProjectiveCycle hp s₁)
    (Cs2 : CentreProjectiveCycle hp s₂)
    (ho1Exp : centreExponent Co1 t = n - 2)
    (ho2Exp : centreExponent Co2 t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient Co1 t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co2 t) = 1)
    (Ho1 : HighExponentTransitionIntervalCertificate hp t o₁ Co1)
    (Ho2 : HighExponentTransitionIntervalCertificate hp t o₂ Co2)
    (Hs1 : HighExponentTransitionIntervalCertificate hp t s₁ Cs1)
    (Hs2 : HighExponentTransitionIntervalCertificate hp t s₂ Cs2)
    (hqe1 : Hs1.qe = 1)
    (hqe2 : Hs2.qe = 1) :
    let To1 := (ofHighExponent Ho1).turnLength
    let To2 := (ofHighExponent Ho2).turnLength
    let Ts1 := (ofHighExponent Hs1).turnLength
    let Ts2 := (ofHighExponent Hs2).turnLength
    2 * (n : ℝ) * lam ≤ To1 + To2 + Ts1 + Ts2
    ∧
    To1 + To2 + Ts1 + Ts2 ≤ 2 * Real.pi
    ∧
    2 * Real.pi - (To1 + To2 + Ts1 + Ts2)
      ≤ 2 * delta * lam
    ∧
    2 * delta * lam < lam := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  have hqo1 :
      Ho1.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Co1 Ho1 ho1Support
    rw [ho1Exp] at h
    omega
  have hqo2 :
      Ho2.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Co2 Ho2 ho2Support
    rw [ho2Exp] at h
    omega

  have hlo1 :=
    qe_mul_lam_le_turnLength_ofHighExponent Ho1 htpos hlam
  have hlo2 :=
    qe_mul_lam_le_turnLength_ofHighExponent Ho2 htpos hlam
  have hls1 :=
    qe_mul_lam_le_turnLength_ofHighExponent Hs1 htpos hlam
  have hls2 :=
    qe_mul_lam_le_turnLength_ofHighExponent Hs2 htpos hlam
  rw [hqo1] at hlo1
  rw [hqo2] at hlo2
  rw [hqe1] at hls1
  rw [hqe2] at hls2

  have hlower :
      2 * (n : ℝ) * lam ≤
        (ofHighExponent Ho1).turnLength +
        (ofHighExponent Ho2).turnLength +
        (ofHighExponent Hs1).turnLength +
        (ofHighExponent Hs2).turnLength := by
    push_cast at hlo1 hlo2 hls1 hls2
    nlinarith

  have hupper :=
    four_turnLength_sum_le_two_pi
      ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
      (ofHighExponent Ho1)
      (ofHighExponent Ho2)
      (ofHighExponent Hs1)
      (ofHighExponent Hs2)

  have hpiEq : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hslack :
      2 * Real.pi -
        ((ofHighExponent Ho1).turnLength +
         (ofHighExponent Ho2).turnLength +
         (ofHighExponent Hs1).turnLength +
         (ofHighExponent Hs2).turnLength)
      ≤ 2 * delta * lam := by
    rw [hpiEq, ht]
    push_cast
    nlinarith [hlower]

  have hsmallSlack :
      2 * delta * lam < lam := by
    have h2d : 2 * delta < 1 := by linarith
    exact (mul_lt_mul_right hlampos).2 h2d

  exact ⟨hlower,hupper,hslack,hsmallSlack⟩

#print axioms exactTwo_four_transition_turns_near_saturate

end JSP000404Research
