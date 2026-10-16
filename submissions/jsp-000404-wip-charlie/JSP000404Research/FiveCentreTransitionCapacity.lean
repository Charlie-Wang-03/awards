import JSP000404Research.ThirdLayerTransitionPacking
import JSP000404Research.LowDeficitSupport
import JSP000404Research.CentreExponentBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Five-centre transition capacity at a saturated top/third-layer pair

A top exponent n-1 centre contributes a transition quotient n.
An exponent n-3 centre with quotient support one contributes n-2.
Any three further distinct centres of quotient support at most two
would each contribute at least one positive transition quotient.

The total n+(n-2)+1+1+1 = 2n+1 violates the geometric packing
bound 2n. Crucially, the three additional centres may have
ARBITRARY exponents; no n-3 or support-two equalities are assumed.

Consequently if two such additional centres exist, every fifth
centre has support at least three and exponent at most n-3.
These are conditional geometric restrictions, not a solution of
the JSP-000404 global non-reusing dyadic payment problem.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_five_low_support_of_top_and_third_support_one
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
    (Cd : CentreProjectiveCycle hp d)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC : positiveSupport (centreQuotient Cc t) ≤ 2)
    (hsupD : positiveSupport (centreQuotient Cd t) ≤ 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos := sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone := sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

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
  obtain ⟨HD, hHDpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam d Cd hsupD

  have hqS : HS.qe = n :=
    top_exponent_transition_qe_eq_n
      Cs (by omega : 2 ≤ n) hdelta0 hdelta1 ht hS HS
  have hqA : HA.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hsupA
    rw [hA] at h
    omega

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

  have hpack :
      (∑ r : Fin 5, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      centre hcentre Cfam cert
  have hc0 : (cert (0 : Fin 5)).qe = HS.qe := rfl
  have hc1 : (cert (1 : Fin 5)).qe = HA.qe := rfl
  have hc2 : (cert (2 : Fin 5)).qe = HB.qe := rfl
  have hc3 : (cert (3 : Fin 5)).qe = HC.qe := rfl
  have hc4 : (cert (4 : Fin 5)).qe = HD.qe := rfl
  have hpack' :
      HS.qe + HA.qe + HB.qe + HC.qe + HD.qe ≤ 2 * n := by
    simpa [Fin.sum_univ_succ, hc0, hc1, hc2, hc3, hc4,
      add_assoc] using hpack
  have hBpos : 1 ≤ HB.qe := Nat.one_le_iff_ne_zero.mpr hHBpos
  have hCpos : 1 ≤ HC.qe := Nat.one_le_iff_ne_zero.mpr hHCpos
  have hDpos : 1 ≤ HD.qe := Nat.one_le_iff_ne_zero.mpr hHDpos
  rw [hqS, hqA] at hpack'
  omega

/-- After two arbitrary support<=2 companions have consumed the last two
transition slots, every additional centre necessarily has support>=3. -/
theorem fifth_support_ge_three_of_top_third_saturation
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
    (Cd : CentreProjectiveCycle hp d)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC : positiveSupport (centreQuotient Cc t) ≤ 2) :
    3 ≤ positiveSupport (centreQuotient Cd t) := by
  by_contra h
  have hd : positiveSupport (centreQuotient Cd t) ≤ 2 := by omega
  exact no_five_low_support_of_top_and_third_support_one
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hsd hab hac had hbc hbd hcd
    Cs Ca Cb Cc Cd hS hA hsupA hsupB hsupC hd

/-- All other centres, regardless of their individual exponents, lie
at least three dyadic layers below the top upper bound. -/
theorem fifth_exponent_le_n_sub_three_of_top_third_saturation
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
    (Cd : CentreProjectiveCycle hp d)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC : positiveSupport (centreQuotient Cc t) ≤ 2) :
    centreExponent Cd t ≤ n - 3 := by
  have hdelta1 : delta < 1 := by linarith
  have hsupD : 3 ≤ positiveSupport (centreQuotient Cd t) :=
    fifth_support_ge_three_of_top_third_saturation
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hsd hab hac had hbc hbd hcd
      Cs Ca Cb Cc Cd hS hA hsupA hsupB hsupC
  let q := centreQuotient Cd t
  have hsum : (∑ r, q r) ≤ n :=
    centreQuotient_function_sum_le_n
      Cd n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hid := floorExcess_add_positiveSupport q
  have hbudget : floorExcess q + positiveSupport q ≤ n := by
    rw [hid]
    exact hsum
  have hk : centreExponent Cd t = floorExcess q := rfl
  rw [hk]
  omega

#print axioms no_five_low_support_of_top_and_third_support_one
#print axioms fifth_support_ge_three_of_top_third_saturation
#print axioms fifth_exponent_le_n_sub_three_of_top_third_saturation

end JSP000404Research
