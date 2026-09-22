import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.ConcreteDeficitThree
import JSP000404Research.ExposedSupportIntervalGeneral
import JSP000404Research.SupportIntervalCertificate
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# No fifth strictly exposed point in the 1+2+2 third-layer extremal shape

Assume a top centre s and three exact n-3 companions a,b,c with support types

  support(a)=1,
  support(b)=support(c)=2.

All four centres have one-transition support interval certificates.  Their
turn lengths are bounded below by

  n*lambda, (n-2)*lambda, lambda, lambda.

Any fifth globally strictly exposed point d owns another support interval of
turn at least lambda.  The five disjoint strict-support arcs would therefore
have total turn at least

  (2n+1)*lambda,

which exceeds 2*pi = 2(n+delta)*lambda because delta<1/2.

Thus every fifth point in this extremal shape must fail global strict exposure.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

theorem no_fifth_strictlyExposed_of_top_supportOne_two_supportTwo_deficitThree
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
    {s a b c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hB : centreExponent Cb t = n - 3)
    (hC : centreExponent Cc t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 2)
    (hsupC :
      positiveSupport (centreQuotient Cc t) = 2)
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

  let HS :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        s Cs (by rw [hS]; omega))
  obtain ⟨HA, hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca (by rw [hsupA]; omega)
  obtain ⟨HB, hHBpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam b Cb (by rw [hsupB]; omega)
  obtain ⟨HC, hHCpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam c Cc (by rw [hsupC]; omega)
  obtain ⟨SD, hturnD⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp hcap htpos htone hlam
      (Classical.choice
        (exists_centreProjectiveCycle hp d
          ⟨⟨s, hsd⟩⟩))
      hExposeD

  let SS : SupportIntervalCertificate (p := p) s :=
    SupportIntervalCertificate.ofHighExponent HS
  let SA : SupportIntervalCertificate (p := p) a :=
    SupportIntervalCertificate.ofHighExponent HA
  let SB : SupportIntervalCertificate (p := p) b :=
    SupportIntervalCertificate.ofHighExponent HB
  let SC : SupportIntervalCertificate (p := p) c :=
    SupportIntervalCertificate.ofHighExponent HC

  have hqS : HS.qe = n :=
    unit_deficit_transition_qe_eq_n
      Cs HS (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hS
  have hqA : HA.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hsupA
    rw [hA] at h
    omega

  have hturnS : (n : ℝ) * lam ≤ SS.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HS htpos hlam
    rw [hqS] at h
    exact h
  have hturnA :
      ((n - 2 : ℕ) : ℝ) * lam ≤ SA.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HA htpos hlam
    rw [hqA] at h
    exact h
  have hturnB : lam ≤ SB.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HB htpos hlam
    have hq : 1 ≤ HB.qe :=
      Nat.one_le_iff_ne_zero.mpr hHBpos
    have hmul : lam ≤ (HB.qe : ℝ) * lam := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hq) hlampos.le
    exact hmul.trans h
  have hturnC : lam ≤ SC.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HC htpos hlam
    have hq : 1 ≤ HC.qe :=
      Nat.one_le_iff_ne_zero.mpr hHCpos
    have hmul : lam ≤ (HC.qe : ℝ) * lam := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hq) hlampos.le
    exact hmul.trans h

  let centre : Fin 5 → V := ![s,a,b,c,d]
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
      try { exact False.elim (hsa hxy) } <;>
      try { exact False.elim (hsb hxy) } <;>
      try { exact False.elim (hsc hxy) } <;>
      try { exact False.elim (hsd hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hac hxy) } <;>
      try { exact False.elim (had hxy) } <;>
      try { exact False.elim (hbc hxy) } <;>
      try { exact False.elim (hbd hxy) } <;>
      try { exact False.elim (hcd hxy) } <;>
      try { exact False.elim (hsa hxy.symm) } <;>
      try { exact False.elim (hsb hxy.symm) } <;>
      try { exact False.elim (hsc hxy.symm) } <;>
      try { exact False.elim (hsd hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) } <;>
      try { exact False.elim (hac hxy.symm) } <;>
      try { exact False.elim (had hxy.symm) } <;>
      try { exact False.elim (hbc hxy.symm) } <;>
      try { exact False.elim (hbd hxy.symm) } <;>
      try { exact False.elim (hcd hxy.symm) }

  let cert : ∀ r : Fin 5,
      SupportIntervalCertificate (p := p) (centre r) :=
    ![SS,SA,SB,SC,SD]

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
          (add_le_add hturnS hturnA)
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

#print axioms no_fifth_strictlyExposed_of_top_supportOne_two_supportTwo_deficitThree

end JSP000404Research
