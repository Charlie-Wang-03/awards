import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.ExposedSupportIntervalGeneral
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Exposure budget after one third-layer support-one centre

A top n-1 centre contributes at least n*lambda of strict-support turn.
An exact n-3 support-one centre contributes at least (n-2)*lambda.
Every additional strictly exposed centre contributes at least lambda.

Therefore three further exposed centres would force total turn at least

  (2*n+1)*lambda,

which is strictly greater than

  2*pi = 2*(n+delta)*lambda

in the lower branch delta<1/2.

This cardinality-free packing lemma is the global distribution constraint
needed around the remaining two-bad-minimum equality terminal.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

theorem no_three_additional_exposed_after_top_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a b c d : V}
    (hta : top ≠ a) (htb : top ≠ b)
    (htc : top ≠ c) (htd : top ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Ctop : CentreProjectiveCycle hp top)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (hTop : centreExponent Ctop t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hExposeB : StrictlyExposedAt p b)
    (hExposeC : StrictlyExposedAt p c)
    (hExposeD : StrictlyExposedAt p d) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  let HTop :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        top Ctop (by rw [hTop]; omega))
  obtain ⟨HA, _hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca
      (by rw [hsupA]; omega)

  obtain ⟨SB, hturnB⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp hcap htpos htone hlam Cb hExposeB
  obtain ⟨SC, hturnC⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp hcap htpos htone hlam Cc hExposeC
  obtain ⟨SD, hturnD⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp hcap htpos htone hlam Cd hExposeD

  let STop : SupportIntervalCertificate (p := p) top :=
    SupportIntervalCertificate.ofHighExponent HTop
  let SA : SupportIntervalCertificate (p := p) a :=
    SupportIntervalCertificate.ofHighExponent HA

  have hqTop : HTop.qe = n :=
    unit_deficit_transition_qe_eq_n
      Ctop HTop (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hTop

  have hqA : HA.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hsupA
    rw [hA] at h
    omega

  have hturnTop :
      (n : ℝ) * lam ≤ STop.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HTop htpos hlam
    rw [hqTop] at h
    exact h

  have hturnA :
      ((n - 2 : ℕ) : ℝ) * lam ≤ SA.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HA htpos hlam
    rw [hqA] at h
    exact h

  let centre : Fin 5 → V := ![top,a,b,c,d]
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
      try { exact False.elim (hta hxy) } <;>
      try { exact False.elim (htb hxy) } <;>
      try { exact False.elim (htc hxy) } <;>
      try { exact False.elim (htd hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hac hxy) } <;>
      try { exact False.elim (had hxy) } <;>
      try { exact False.elim (hbc hxy) } <;>
      try { exact False.elim (hbd hxy) } <;>
      try { exact False.elim (hcd hxy) } <;>
      try { exact False.elim (hta hxy.symm) } <;>
      try { exact False.elim (htb hxy.symm) } <;>
      try { exact False.elim (htc hxy.symm) } <;>
      try { exact False.elim (htd hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) } <;>
      try { exact False.elim (hac hxy.symm) } <;>
      try { exact False.elim (had hxy.symm) } <;>
      try { exact False.elim (hbc hxy.symm) } <;>
      try { exact False.elim (hbd hxy.symm) } <;>
      try { exact False.elim (hcd hxy.symm) }

  let cert : ∀ r : Fin 5,
      SupportIntervalCertificate (p := p) (centre r) :=
    ![STop,SA,SB,SC,SD]

  have hpack :
      (∑ r : Fin 5, (cert r).turnLength) ≤
        2 * Real.pi :=
    SupportIntervalCertificate.turnLength_sum_le_two_pi
      centre hcentre cert

  have hlower :
      (n : ℝ) * lam +
        ((n - 2 : ℕ) : ℝ) * lam +
        lam + lam + lam
        ≤
      ∑ r : Fin 5, (cert r).turnLength := by
    simpa [cert, centre, Fin.sum_univ_succ] using
      add_le_add
        (add_le_add
          (add_le_add hturnTop hturnA)
          hturnB)
        (add_le_add hturnC hturnD)

  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 2 ≤ n))
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]

  rw [hncast, hpi, ht] at hpack hlower
  nlinarith

#print axioms no_three_additional_exposed_after_top_support_one

end JSP000404Research
