import JSP000404Research.TopNextSupportOneFourCentrePacking
import JSP000404Research.SecondLayerNoTopReduction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# No-top four-centre packing: at most two support-one second-layer centres

If n>=3 and four distinct genuine AngleCap centres are given, three
next-layer exponent (n-2) centres of support one would each cost n-1.
One more centre of quotient support <=2 costs at least one.
Their sum 3(n-1)+1 > 2n violates the actual transition packing theorem.

For n=3 this strengthens the previously unresolved *no-top* five-centre
motif: among four n=3 exponent-one centres, no triple can have support one.
This is not a geometric exclusion of all exponent-one profiles.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_three_next_support_one_with_fourth_low_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = n - 2)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupS : positiveSupport (centreQuotient Cs t) = 1)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 1)
    (hsupC :
      positiveSupport (centreQuotient Cc t) ≤ 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  let HS :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        s Cs (by rw [hS]; omega))
  obtain ⟨HA, hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca (by omega)
  obtain ⟨HB, hHBpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam b Cb (by rw [hsupB]; omega)
  obtain ⟨HC, hHCpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam c Cc hsupC

  have hqS : HS.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Cs HS hsupS
    rw [hS] at h
    omega
  have hqA : HA.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hsupA
    rw [hA] at h
    omega
  have hqB : HB.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Cb HB hsupB
    rw [hB] at h
    omega

  let centre : Fin 4 → V := ![s,a,b,c]
  let Cfam : ∀ r : Fin 4,
      CentreProjectiveCycle hp (centre r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre] using Cs
    · simpa [centre] using Ca
    · simpa [centre] using Cb
    · simpa [centre] using Cc
  let cert : ∀ r : Fin 4,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre, Cfam] using HS
    · simpa [centre, Cfam] using HA
    · simpa [centre, Cfam] using HB
    · simpa [centre, Cfam] using HC

  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
      try { exact False.elim (hsa hxy) } <;>
      try { exact False.elim (hsb hxy) } <;>
      try { exact False.elim (hsc hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hac hxy) } <;>
      try { exact False.elim (hbc hxy) } <;>
      try { exact False.elim (hsa hxy.symm) } <;>
      try { exact False.elim (hsb hxy.symm) } <;>
      try { exact False.elim (hsc hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) } <;>
      try { exact False.elim (hac hxy.symm) } <;>
      try { exact False.elim (hbc hxy.symm) }

  have hpack :
      (∑ r : Fin 4, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      centre hcentre Cfam cert

  have hcert0 : (cert (0 : Fin 4)).qe = HS.qe := by
    rfl
  have hcert1 : (cert (1 : Fin 4)).qe = HA.qe := by
    rfl
  have hcert2 : (cert (2 : Fin 4)).qe = HB.qe := by
    rfl
  have hcert3 : (cert (3 : Fin 4)).qe = HC.qe := by
    rfl
  have hpack' :
      HS.qe + HA.qe + HB.qe + HC.qe ≤ 2 * n := by
    simpa [Fin.sum_univ_succ, hcert0, hcert1, hcert2, hcert3,
      add_assoc] using hpack
  rw [hqS, hqA, hqB] at hpack'
  have hCpos : 1 ≤ HC.qe :=
    Nat.one_le_iff_ne_zero.mpr hHCpos
  omega


#print axioms no_three_next_support_one_with_fourth_low_support

end JSP000404Research
