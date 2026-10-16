import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.ConcreteDeficitThree
import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.TopExponentSupportOneTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Transition packing in the third exponent layer

Let s be a top n-1 centre and a an exact n-3 support-one centre.  The
distinguished transition quotients are

  q_s = n,
  q_a = n-2.

If b and c are any two further distinct centres with quotient support at most
two, each has one positive transition quotient.  Packing the four transition
support arcs gives

  n + (n-2) + q_b + q_c <= 2n.

Thus q_b=q_c=1.

Consequently, if b or c is itself exact n-3/support-one, its transition
quotient would also equal n-2>=2, a contradiction.  Hence among three exact
third-layer companions with support<=2, the presence of one support-one centre
forces the other two to be support-two with unit transitions.
-/

namespace JSP000404Research

open scoped BigOperators

theorem third_layer_packing_forces_two_unit_transitions
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
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
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
      positiveSupport (centreQuotient Cc t) ≤ 2) :
    ∃ HB : HighExponentTransitionIntervalCertificate hp t b Cb,
      ∃ HC : HighExponentTransitionIntervalCertificate hp t c Cc,
        HB.qe = 1 ∧ HC.qe = 1 := by
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
  have hqA : HA.qe = n - 2 := by
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
  have hB1 : HB.qe = 1 := by
    have hBpos : 1 ≤ HB.qe := Nat.one_le_iff_ne_zero.mpr hHBpos
    have hCpos : 1 ≤ HC.qe := Nat.one_le_iff_ne_zero.mpr hHCpos
    omega
  have hC1 : HC.qe = 1 := by
    have hBpos : 1 ≤ HB.qe := Nat.one_le_iff_ne_zero.mpr hHBpos
    have hCpos : 1 ≤ HC.qe := Nat.one_le_iff_ne_zero.mpr hHCpos
    omega
  exact ⟨HB, HC, hB1, hC1⟩

/-- A top centre cannot have three exact n-3 companions of support at most two
if at least two of those companions are support one. -/
theorem no_top_three_deficit_three_support_le_two_with_two_support_one
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
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hB : centreExponent Cb t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 1)
    (hsupC :
      positiveSupport (centreQuotient Cc t) ≤ 2) :
    False := by
  obtain ⟨HB, HC, hB1, hC1⟩ :=
    third_layer_packing_forces_two_unit_transitions
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb Cc hS hA hsupA
      (by rw [hsupB]; omega) hsupC
  have hBqe :
      HB.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Cb HB hsupB
    rw [hB] at h
    omega
  rw [hB1] at hBqe
  omega

#print axioms third_layer_packing_forces_two_unit_transitions
#print axioms no_top_three_deficit_three_support_le_two_with_two_support_one

end JSP000404Research
