import JSP000404Research.ThirdLayerNoFifthExposed
import JSP000404Research.FiveCentreTransitionCapacity
import Mathlib.Tactic

/-!
# Fifth-centre strict-exposure obstruction with arbitrary companion exponents

A top (n-1) centre and an (n-3)/support-one centre contribute
disjoint strict-support-arc turn at least n*lambda and (n-2)*lambda.
Two further centres, independently of their exponents, each have one
transition whenever their positive quotient supports are at most two.

A fifth strictly exposed centre would force a total of at least
(2n+1)*lambda > 2*pi as delta<1/2. Thus under this
four-centre saturation no fifth centre can be strictly exposed.

Unlike the original ThirdLayerNoFifthExposed theorem, the two
additional companions are NOT assumed to be in exponent layer n-3
or to have support exactly two. This is not a proof of the
unconditional JSP-000404 dyadic inequality.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

theorem no_fifth_strictlyExposed_of_top_third_one_two_low_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
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
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC :
      positiveSupport (centreQuotient Cc t) ≤ 2)
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
      hp hcap htpos htone hlam b Cb hsupB
  obtain ⟨HC, hHCpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam c Cc hsupC
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
    top_exponent_transition_qe_eq_n
      Cs (by omega : 2 ≤ n) hdelta0 hdelta1 ht hS HS
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
      have hqReal : (1 : ℝ) ≤ (HB.qe : ℝ) := by exact_mod_cast hq
      nlinarith
    exact hmul.trans h
  have hturnC : lam ≤ SC.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HC htpos hlam
    have hq : 1 ≤ HC.qe :=
      Nat.one_le_iff_ne_zero.mpr hHCpos
    have hmul : lam ≤ (HC.qe : ℝ) * lam := by
      have hqReal : (1 : ℝ) ≤ (HC.qe : ℝ) := by exact_mod_cast hq
      nlinarith
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
      SupportIntervalCertificate (p := p) (centre r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre] using SS
    · simpa [centre] using SA
    · simpa [centre] using SB
    · simpa [centre] using SC
    · simpa [centre] using SD

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
    have hc0 : cert (0 : Fin 5) = SS := rfl
    have hc1 : cert (1 : Fin 5) = SA := rfl
    have hc2 : cert (2 : Fin 5) = SB := rfl
    have hc3 : cert (3 : Fin 5) = SC := rfl
    have hc4 : cert (4 : Fin 5) = SD := rfl
    have hsum :
        (∑ r : Fin 5, (cert r).turnLength) =
          SS.turnLength + SA.turnLength + SB.turnLength +
            SC.turnLength + SD.turnLength := by
      simp [Fin.sum_univ_succ, hc0, hc1, hc2, hc3, hc4, add_assoc] <;> rfl
    rw [hsum]
    linarith

  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hncast] at hlower
  rw [hpi, ht] at hpack
  have hgap : 0 < (1 - 2 * delta) * lam :=
    mul_pos (by linarith) hlampos
  nlinarith

#print axioms no_fifth_strictlyExposed_of_top_third_one_two_low_support

end JSP000404Research
