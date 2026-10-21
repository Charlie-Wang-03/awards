import JSP000404Research.ThirdLayerTransitionPacking
import JSP000404Research.SupportLeTwoTransitionInterval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Four actual centre transition packing: top, next support-one and two low-support

In the genuine AngleCap geometry with t=n+delta, 0<=delta<1/2, n>=3,
the real top exponent (n-1) consumes n transition units. A genuine
next exponent (n-2) with quotient support 1 consumes n-1 units.
Every additional centre with positive support at most 2 consumes at
least 1 transition unit. Thus four distinct centres of these types
would pay n+(n-1)+1+1 > 2*n, contradicting the globally proved
highTransition_quotient_sum_le_two_n bound.

This is a strengthened geometry-derived restriction on the actual
n=3, card=5 overweight top+next motif, not its full exclusion.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_top_next_support_one_with_two_low_support_companions
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
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) ≤ 2)
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
      hp hcap htpos htone hlam b Cb hsupB
  obtain ⟨HC, hHCpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam c Cc hsupC

  have hqS : HS.qe = n :=
    top_exponent_transition_qe_eq_n
      Cs (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hS HS
  have hqA : HA.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hsupA
    rw [hA] at h
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
  rw [hqS, hqA] at hpack'
  have hBpos : 1 ≤ HB.qe :=
    Nat.one_le_iff_ne_zero.mpr hHBpos
  have hCpos : 1 ≤ HC.qe :=
    Nat.one_le_iff_ne_zero.mpr hHCpos
  omega

/-- In any actual planar lower-branch configuration with a top exponent
and a support-one next-layer centre, there can be AT MOST ONE
other centre whose full quotient list has support at most two.
This is a direct genuine four-source transition-packing obstruction,
not a fictional dyadic slot-uniqueness condition. -/
theorem top_next_support_one_low_support_card_le_one
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
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a : V}
    (hsa : s ≠ a)
    (hS : centreExponent (C s) t = n - 1)
    (hA : centreExponent (C a) t = n - 2)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1) :
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧ i ≠ a ∧
        positiveSupport (centreQuotient (C i) t) ≤ 2)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro b hb c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hc
  by_contra hbc
  exact no_top_next_support_one_with_two_low_support_companions
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hb.1.symm hc.1.symm hb.2.1.symm hc.2.1.symm hbc
    (C s) (C a) (C b) (C c)
    hS hA hsupA hb.2.2 hc.2.2

#print axioms no_top_next_support_one_with_two_low_support_companions
#print axioms top_next_support_one_low_support_card_le_one

end JSP000404Research
