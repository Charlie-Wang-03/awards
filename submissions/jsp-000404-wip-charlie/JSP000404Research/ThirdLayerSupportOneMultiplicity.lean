import JSP000404Research.OneSupportGlobalBound
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# At most one support-one minimum in the six-point third layer

Let s have exponent n-1 and let a,b be distinct n-3 centres, each with
quotient support one.

For support-one centres the unique positive quotient equals exponent+1.
Thus the three strict support arcs at s,a,b have quotient costs

  n, n-2, n-2.

Their projective support gaps are pairwise packable on the direction circle,
so the total quotient cost is at most 2n.  But

  n + (n-2) + (n-2) = 3n-4 > 2n

for n>=5.

Hence the six-point third layer contains at most one support-one minimum.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_top_with_two_support_one_deficit_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hB : centreExponent (C b) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hsumTop :=
    centreQuotient_function_sum_le_n
      (C top) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hdefTop :
      n - floorExcess (centreQuotient (C top) t) = 1 := by
    change n - centreExponent (C top) t = 1
    rw [hTop]
    omega
  have hsupTop :
      positiveSupport (centreQuotient (C top) t) = 1 :=
    (unit_deficit_structure
      (centreQuotient (C top) t) n
      (by omega : 2 ≤ n)
      hsumTop hdefTop).1

  let certTop : OneSupportIntervalCertificate hp t top (C top) :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 ht hlam top (C top) hsupTop)
  let certA : OneSupportIntervalCertificate hp t a (C a) :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 ht hlam a (C a) hsupA)
  let certB : OneSupportIntervalCertificate hp t b (C b) :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 ht hlam b (C b) hsupB)

  let centre : Fin 3 → V := ![top,a,b]
  have hcentre : Function.Injective centre := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp [centre] at huv ⊢ <;>
      try { exact False.elim (hta huv) } <;>
      try { exact False.elim (htb huv) } <;>
      try { exact False.elim (hab huv) } <;>
      try { exact False.elim (hta huv.symm) } <;>
      try { exact False.elim (htb huv.symm) } <;>
      try { exact False.elim (hab huv.symm) }

  let Cfam : ∀ r : Fin 3, CentreProjectiveCycle hp (centre r) :=
    ![C top,C a,C b]
  let cert : ∀ r : Fin 3,
      OneSupportIntervalCertificate hp t (centre r) (Cfam r) :=
    ![certTop,certA,certB]

  have hgap :
      (∑ r : Fin 3, (cert r).ge) ≤ 2 :=
    oneSupport_gap_sum_le_two
      hp centre hcentre t Cfam cert
  have hqsum :
      (∑ r : Fin 3, (cert r).qe) ≤ 2 * n :=
    sum_quotient_le_two_n_of_transition_gap_packing
      (fun r => (cert r).qe)
      (fun r => (cert r).ge)
      n delta t
      (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      (fun r => (cert r).qe_le)
      hgap

  have hqTop : certTop.qe = n := by
    rw [certTop.qe_eq, hTop]
    omega
  have hqA : certA.qe = n - 2 := by
    rw [certA.qe_eq, hA]
    omega
  have hqB : certB.qe = n - 2 := by
    rw [certB.qe_eq, hB]
    omega

  have hqsum' :
      certTop.qe + certA.qe + certB.qe ≤ 2 * n := by
    simpa [cert, Cfam, centre, Fin.sum_univ_succ] using hqsum
  rw [hqTop, hqA, hqB] at hqsum'
  omega

#print axioms no_top_with_two_support_one_deficit_three

end JSP000404Research
