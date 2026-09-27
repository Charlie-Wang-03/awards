import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.SixPointNoTwoSupportOneMinima
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Transition ceiling beside a sharp top and one support-one minimum

In the six-point third-layer profile, the sharp top contributes a transition
certificate of quotient n.  A support-one n-3 minimum contributes a transition
certificate of quotient n-2.

For any third distinct centre carrying a transition certificate H, global
transition packing gives

  n + (n-2) + H.qe <= 2n,

hence

  H.qe <= 2.

This is the key mixed-support ceiling: every quotient >=3 at the second bad
minimum is necessarily a same-sign quotient, not a transition.
-/

namespace JSP000404Research

open scoped BigOperators

theorem transition_qe_le_two_beside_top_and_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (Ctop : CentreProjectiveCycle hp top)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hTop : centreExponent Ctop t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hSupportA :
      positiveSupport (centreQuotient Ca t) = 1)
    (H : HighExponentTransitionIntervalCertificate hp t b Cb) :
    H.qe ≤ 2 := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  let HTop :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        top Ctop (by rw [hTop]; omega))

  obtain ⟨HA, _hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca
      (by rw [hSupportA]; omega)

  have hqTop : HTop.qe = n :=
    unit_deficit_transition_qe_eq_n
      Ctop HTop (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hTop

  have hqA : HA.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hSupportA
    rw [hA] at h
    omega

  let centre : Fin 3 → V := ![top,a,b]
  let Cfam : ∀ r : Fin 3,
      CentreProjectiveCycle hp (centre r) :=
    ![Ctop,Ca,Cb]
  let cert : ∀ r : Fin 3,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) :=
    ![HTop,HA,H]

  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
      try { exact False.elim (hta hxy) } <;>
      try { exact False.elim (htb hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hta hxy.symm) } <;>
      try { exact False.elim (htb hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) }

  have hpack :
      (∑ r : Fin 3, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      centre hcentre Cfam cert

  have hpack' :
      HTop.qe + HA.qe + H.qe ≤ 2 * n := by
    simpa [cert,Cfam,centre,Fin.sum_univ_succ] using hpack

  rw [hqTop,hqA] at hpack'
  omega

#print axioms transition_qe_le_two_beside_top_and_support_one

end JSP000404Research
