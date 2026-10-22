import JSP000404Research.ThirdLayerTransitionPacking
import JSP000404Research.SupportOneExposureBudget
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Transition-budget rigidity in the mixed support-one/support-two branch

Once the six-point third layer contains one support-one minimum a, the sharp
top and a already consume

  n + (n-2) = 2n-2

units of the global transition-support packing budget.

Therefore every additional support-at-most-two centre must fit into the final
two units.  In particular:

* three further support<=2 centres are impossible;
* one support-two centre has transition quotient at most two;
* two support-two centres both have transition quotient exactly one.

This packages the exact numerical rigidity of the remaining mixed (1,2)
hard-support branch.
-/

namespace JSP000404Research

open scoped BigOperators

theorem mixed_support_one_one_support_two_transition_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
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
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2) :
    ∃ HB : HighExponentTransitionIntervalCertificate hp t b Cb,
      HB.qe ≤ 2 := by
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
      (by rw [hsupA]; omega)
  obtain ⟨HB, hHBpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam b Cb hsupB

  have hsumTop :=
    centreQuotient_function_sum_le_n
      Ctop n delta t (by omega : 1 ≤ n) hdelta0 hdelta1 ht
  have hdefTop :
      n - floorExcess (centreQuotient Ctop t) = 1 := by
    change n - centreExponent Ctop t = 1
    rw [hTop]
    omega
  have hsupportTop :
      positiveSupport (centreQuotient Ctop t) = 1 :=
    (unit_deficit_structure
      (centreQuotient Ctop t) n
      (by omega : 2 ≤ n) hsumTop hdefTop).1
  have hqTop : HTop.qe = n := by
    have h :=
      highTransition_qe_eq_exponent_add_one_of_support_one
        Ctop HTop hsupportTop
    rw [hTop] at h
    omega
  have hqA : HA.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Ca HA hsupA
    rw [hA] at h
    omega

  let centre : Fin 3 → V := ![top,a,b]
  let Cfam : ∀ r : Fin 3,
      CentreProjectiveCycle hp (centre r) := by
    intro r
    rcases r with ⟨k, hk⟩
    interval_cases k
    · simpa [centre] using Ctop
    · simpa [centre] using Ca
    · simpa [centre] using Cb
  let cert : ∀ r : Fin 3,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) := by
    intro r
    rcases r with ⟨k, hk⟩
    interval_cases k
    · simpa [Cfam, centre] using HTop
    · simpa [Cfam, centre] using HA
    · simpa [Cfam, centre] using HB

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
  have hcert0 : (cert (0 : Fin 3)).qe = HTop.qe := by
    rfl
  have hcert1 : (cert (1 : Fin 3)).qe = HA.qe := by
    rfl
  have hcert2 : (cert (2 : Fin 3)).qe = HB.qe := by
    rfl
  have hpack' :
      HTop.qe + HA.qe + HB.qe ≤ 2 * n := by
    simpa [Fin.sum_univ_succ, hcert0, hcert1, hcert2,
      add_assoc] using hpack

  rw [hqTop, hqA] at hpack'
  exact ⟨HB, by omega⟩

theorem mixed_support_one_two_support_two_transitions_eq_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a b c : V}
    (hta : top ≠ a) (htb : top ≠ b) (htc : top ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ctop : CentreProjectiveCycle hp top)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hTop : centreExponent Ctop t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2)
    (hsupC : positiveSupport (centreQuotient Cc t) = 2) :
    ∃ HB : HighExponentTransitionIntervalCertificate hp t b Cb,
      ∃ HC : HighExponentTransitionIntervalCertificate hp t c Cc,
        HB.qe = 1 ∧ HC.qe = 1 := by
  exact third_layer_packing_forces_two_unit_transitions
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hta htb htc hab hac hbc
    Ctop Ca Cb Cc hTop hA hsupA
    (by simpa [hsupB])
    (by simpa [hsupC])

#print axioms mixed_support_one_one_support_two_transition_le_two
#print axioms mixed_support_one_two_support_two_transitions_eq_one

end JSP000404Research
