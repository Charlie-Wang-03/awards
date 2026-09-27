import JSP000404Research.ThirdLayerTransitionPacking
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Two support-one third-layer minima cannot coexist with the sharp top

For n>=5, let s be the top n-1 centre and let a,b be two distinct n-3
support-one centres.  Their distinguished transition quotients are

  n, n-2, n-2.

The corresponding strict-support arcs are pairwise disjoint, so the global
transition packing bound gives

  n + (n-2) + (n-2) <= 2n,

which is impossible for n>=5.

This removes the (1,1) support pair from the remaining two-bad-minimum
terminal without using any cut-specific information.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_top_two_deficit_three_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a)
    (hsb : s ≠ b)
    (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hB : centreExponent Cb t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 1) :
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

  obtain ⟨HA, _hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca
      (by rw [hsupA]; omega)

  obtain ⟨HB, _hHBpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam b Cb
      (by rw [hsupB]; omega)

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

  have hqB : HB.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        Cb HB hsupB
    rw [hB] at h
    omega

  let centre : Fin 3 → V := ![s,a,b]
  let Cfam : ∀ r : Fin 3,
      CentreProjectiveCycle hp (centre r) :=
    ![Cs,Ca,Cb]
  let cert : ∀ r : Fin 3,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) :=
    ![HS,HA,HB]

  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
      try { exact False.elim (hsa hxy) } <;>
      try { exact False.elim (hsb hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hsa hxy.symm) } <;>
      try { exact False.elim (hsb hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) }

  have hpack :
      (∑ r : Fin 3, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      centre hcentre Cfam cert

  have hpack' :
      HS.qe + HA.qe + HB.qe ≤ 2 * n := by
    simpa [cert, Cfam, centre, Fin.sum_univ_succ] using hpack

  rw [hqS, hqA, hqB] at hpack'
  omega

#print axioms no_top_two_deficit_three_support_one

end JSP000404Research
