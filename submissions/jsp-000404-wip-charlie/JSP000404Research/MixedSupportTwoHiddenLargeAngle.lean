import JSP000404Research.SixPointMixedSupportTransitionBudget
import JSP000404Research.DeficitThreeSupportTwoHidden
import JSP000404Research.GeneralNontransitionPayment
import Mathlib.Tactic

/-!
# Hidden large angle in the mixed support-one/support-two branch

Let top be the n-1 sharp centre, a an n-3 support-one minimum, and b an
n-3 support-two minimum.

Choose the actual unique-transition decomposition at b.  Packing its
transition certificate together with the top and support-one certificates
forces the transition quotient qe at b to satisfy qe <= 2.

The support-two quotient sum is n-1, so the unique other positive quotient is

  (n-1)-qe >= n-3.

That other quotient lies on a same-sign step, hence pays a genuine Euclidean
angle of at least (n-3)*lambda at b.
-/

namespace JSP000404Research

open scoped BigOperators

theorem mixed_support_one_support_two_hidden_large_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn : 5 ≤ n)
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
    (hB : centreExponent Cb t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    ∃ x y : OtherVertex b,
      x ≠ y ∧
      (((n - 3 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p b) (p y.1) := by
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hdelta1 : delta < 1 := by linarith

  obtain ⟨firstB, restB, preB, postB, qeB,
      hraysB, hqeB0, hqB, hsignB⟩ :=
    exists_transition_decomposition_of_support_le_two
      hp hcap htpos htone hlam b Cb
      (by rw [hsupB])

  obtain ⟨HB, hHBqe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos b Cb firstB restB preB postB qeB
      hraysB hqeB0 hqB hsignB

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

  let centre : Fin 3 → V := ![top,a,b]
  let Cfam : (r : Fin 3) →
      CentreProjectiveCycle hp (centre r) := by
    intro r
    induction r using Fin.cases with
    | zero => exact Ctop
    | succ r =>
      induction r using Fin.cases with
      | zero => exact Ca
      | succ r =>
        induction r using Fin.cases with
        | zero => exact Cb
        | succ r => exact Fin.elim0 r
  let cert : (r : Fin 3) →
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) := by
    intro r
    induction r using Fin.cases with
    | zero => exact HTop
    | succ r =>
      induction r using Fin.cases with
      | zero => exact HA
      | succ r =>
        induction r using Fin.cases with
        | zero => exact HB
        | succ r => exact Fin.elim0 r

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
      HTop.qe + HA.qe + HB.qe ≤ 2 * n := by
    have h :=
      highTransition_quotient_sum_le_two_n
        hp (by omega : 1 ≤ n)
        hdelta0 hdeltaHalf ht
        centre hcentre Cfam cert
    have he0 : (cert (0 : Fin 3)).qe = HTop.qe := by rfl
    have he1 : (cert (1 : Fin 3)).qe = HA.qe := by rfl
    have he2 : (cert (2 : Fin 3)).qe = HB.qe := by rfl
    have hsum :
        (∑ r : Fin 3, (cert r).qe) =
          HTop.qe + HA.qe + HB.qe := by
      simpa [Fin.sum_univ_succ, he0, he1, he2, add_assoc]
    exact hsum ▸ h

  have hqeBle : qeB ≤ 2 := by
    rw [hqTop, hqA, hHBqe] at hpack
    omega

  have hsumFn :=
    deficit_three_support_two_sum
      Cb (by omega : 4 ≤ n)
      hdelta0 hdelta1 ht hB hsupB
  have hsumList :
      (preB ++ qeB :: postB).sum = n - 1 := by
    rw [← hqB, ← centreQuotient_sum_eq_list_sum Cb t]
    exact hsumFn
  have hsupportList :
      listPositiveCount (preB ++ qeB :: postB) = 2 := by
    rw [← hqB, ← centreQuotient_ofFn Cb t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupB

  obtain ⟨hhiddenPos, hocc0⟩ :=
    support_two_transition_hidden_sameSign
      (raySignAt hp b firstB)
      (liftedCentreSignPath hp b firstB restB)
      preB postB qeB (n - 1)
      hqeB0 hsignB hsupportList hsumList

  let qHidden : ℕ := (n - 1) - qeB
  have hqHiddenLower : n - 3 ≤ qHidden := by
    dsimp [qHidden]
    omega

  have hocc :
      SameSignQuotientOccurs qHidden
        (raySignAt hp b firstB)
        (liftedCentreSignPath hp b firstB restB)
        (quotientList t Cb.gaps) := by
    dsimp [qHidden]
    rw [hqB]
    exact hocc0

  obtain ⟨x,y,hxy,hangle⟩ :=
    sameSignQuotient_pays_angle
      hp htpos hlam b Cb firstB restB hraysB
      qHidden hocc

  refine ⟨x,y,hxy,?_⟩
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hmul :
      (((n - 3 : ℕ) : ℝ) * lam)
        ≤ (qHidden : ℝ) * lam := by
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hqHiddenLower) hlampos.le
  exact hmul.trans hangle

#print axioms mixed_support_one_support_two_hidden_large_angle

end JSP000404Research
