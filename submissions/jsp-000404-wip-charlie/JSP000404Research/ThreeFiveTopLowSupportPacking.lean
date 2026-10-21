import JSP000404Research.NoTopNextLayerFourCentrePacking
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Five-centre transition obstruction at scale n=3

At t=3+delta, one actual exponent-two top centre consumes three
units of the six available projective transition-quotient units.
Every other centre whose full quotient positive support is at most two
has a genuine positive transition certificate, costing at least one.
Four such other centres would cost at least 3+4=7>6.

For a genuine exponent-one centre, support is automatically one or
two by the proved deficit-two classification. Consequently the n=3
top-plus-next exceptional five-centre configuration necessarily has
at least one of its three exponent-zero companions with support >=3.
This is a further necessary condition, not a proof of impossibility.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_top_three_with_four_low_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (hs : centreExponent Cs t = 2)
    (ha : positiveSupport (centreQuotient Ca t) ≤ 2)
    (hb : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hc : positiveSupport (centreQuotient Cc t) ≤ 2)
    (hd : positiveSupport (centreQuotient Cd t) ≤ 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos := sendov_scale_pos (by omega : 1 ≤ (3 : ℕ)) hdelta0 ht
  have htone := sendov_scale_one_le (by omega : 1 ≤ (3 : ℕ)) hdelta0 ht
  let HS := Classical.choice
    (exists_highExponentTransitionIntervalCertificate
      hp hcap (by omega : 1 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht hlam s Cs (by rw [hs]; omega))
  obtain ⟨HA, hApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca ha
  obtain ⟨HB, hBpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam b Cb hb
  obtain ⟨HC, hCpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam c Cc hc
  obtain ⟨HD, hDpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam d Cd hd
  have htop : HS.qe = 3 :=
    top_exponent_transition_qe_eq_n
      Cs (by omega : 2 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht hs HS
  let centre : Fin 5 → V := ![s,a,b,c,d]
  let Cfam : ∀ r : Fin 5,
      CentreProjectiveCycle hp (centre r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre] using Cs
    · simpa [centre] using Ca
    · simpa [centre] using Cb
    · simpa [centre] using Cc
    · simpa [centre] using Cd
  let cert : ∀ r : Fin 5,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre, Cfam] using HS
    · simpa [centre, Cfam] using HA
    · simpa [centre, Cfam] using HB
    · simpa [centre, Cfam] using HC
    · simpa [centre, Cfam] using HD
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [centre]
  have hpack : (∑ r : Fin 5, (cert r).qe) ≤ 2 * 3 :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ (3 : ℕ))
      hdelta0 hdeltaHalf ht centre hcentre Cfam cert
  have hcert0 : (cert (0 : Fin 5)).qe = HS.qe := by rfl
  have hcert1 : (cert (1 : Fin 5)).qe = HA.qe := by rfl
  have hcert2 : (cert (2 : Fin 5)).qe = HB.qe := by rfl
  have hcert3 : (cert (3 : Fin 5)).qe = HC.qe := by rfl
  have hcert4 : (cert (4 : Fin 5)).qe = HD.qe := by rfl
  have hpack' : HS.qe + HA.qe + HB.qe + HC.qe + HD.qe ≤ 6 := by
    simpa [Fin.sum_univ_succ, hcert0, hcert1, hcert2,
      hcert3, hcert4, add_assoc] using hpack
  have hA : 1 ≤ HA.qe := Nat.one_le_iff_ne_zero.mpr hApos
  have hB : 1 ≤ HB.qe := Nat.one_le_iff_ne_zero.mpr hBpos
  have hC : 1 ≤ HC.qe := Nat.one_le_iff_ne_zero.mpr hCpos
  have hD : 1 ≤ HD.qe := Nat.one_le_iff_ne_zero.mpr hDpos
  omega

/-- In the n=3 top-plus-next five-centre profile, the other three
centres cannot all have support at most two: some has support >=3.
This conclusion uses only actual planar AngleCap and concrete exponent
data, without introducing any unproved payment assumption. -/
theorem top_next_three_companions_one_support_ge_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (hs : centreExponent Cs t = 2)
    (ha : centreExponent Ca t = 1) :
    3 ≤ positiveSupport (centreQuotient Cb t) ∨
    3 ≤ positiveSupport (centreQuotient Cc t) ∨
    3 ≤ positiveSupport (centreQuotient Cd t) := by
  have haClass := actual_deficit_two_support_one_or_two Ca
    (by omega : 3 ≤ (3 : ℕ)) hdelta0 hdeltaHalf ht ha
  have haLow : positiveSupport (centreQuotient Ca t) ≤ 2 := by
    rcases haClass with haOne | haTwo <;> omega
  by_contra h
  push_neg at h
  rcases h with ⟨hb, hc, hd⟩
  have hbLow : positiveSupport (centreQuotient Cb t) ≤ 2 := by omega
  have hcLow : positiveSupport (centreQuotient Cc t) ≤ 2 := by omega
  have hdLow : positiveSupport (centreQuotient Cd t) ≤ 2 := by omega
  exact no_top_three_with_four_low_support
    hp hcap hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hsd hab hac had hbc hbd hcd
    Cs Ca Cb Cc Cd hs haLow hbLow hcLow hdLow

#print axioms no_top_three_with_four_low_support
#print axioms top_next_three_companions_one_support_ge_three

end JSP000404Research
