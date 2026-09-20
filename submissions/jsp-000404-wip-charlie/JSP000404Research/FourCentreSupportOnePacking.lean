import JSP000404Research.OneSupportGlobalBound
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# A sharp centre cannot coexist with two support-one deficit-two centres

In the lower branch, a sharp centre has exponent n-1 and hence one-support
transition quotient n.  A support-one deficit-two centre has exponent n-2 and
transition quotient n-1.

For three distinct such centres the strict-support transition gaps are
pairwise disjoint on the direction circle.  Their quotient costs must therefore
sum to at most 2n.  But

  n + (n-1) + (n-1) = 3n-2 > 2n

for n>=3.

This closes the support-one/support-one branch of the four-centre sharp case.
-/

namespace JSP000404Research

open scoped BigOperators

theorem no_sharp_with_two_support_one_deficit_two
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s a b : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hexpS : centreExponent Cs t = n - 1)
    (hexpA : centreExponent Ca t = n - 2)
    (hexpB : centreExponent Cb t = n - 2)
    (hsuppA : positiveSupport (centreQuotient Ca t) = 1)
    (hsuppB : positiveSupport (centreQuotient Cb t) = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hsumS :=
    centreQuotient_function_sum_le_n
      Cs n delta t (by omega) hdelta0 hdelta1 ht
  have hdefS :
      n - floorExcess (centreQuotient Cs t) = 1 := by
    change n - centreExponent Cs t = 1
    rw [hexpS]
    omega
  have hsuppS :
      positiveSupport (centreQuotient Cs t) = 1 :=
    (unit_deficit_structure
      (centreQuotient Cs t) n (by omega)
      hsumS hdefS).1

  let certS : OneSupportIntervalCertificate hp t s Cs :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0 ht hlam
        s Cs hsuppS)
  let certA : OneSupportIntervalCertificate hp t a Ca :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0 ht hlam
        a Ca hsuppA)
  let certB : OneSupportIntervalCertificate hp t b Cb :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0 ht hlam
        b Cb hsuppB)

  let centre : Fin 3 → Fin 4 :=
    Fin.cases s (fun r : Fin 2 =>
      Fin.cases a (fun _ : Fin 1 => b) r)

  let Cfam : ∀ r : Fin 3, CentreProjectiveCycle hp (centre r) :=
    Fin.cases Cs (fun r : Fin 2 =>
      Fin.cases Ca (fun _ : Fin 1 => Cb) r)

  let cert : ∀ r : Fin 3,
      OneSupportIntervalCertificate hp t (centre r) (Cfam r) :=
    Fin.cases certS (fun r : Fin 2 =>
      Fin.cases certA (fun _ : Fin 1 => certB) r)

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

  have hqeS : certS.qe = n := by
    rw [certS.qe_eq, hexpS]
    omega
  have hqeA : certA.qe = n - 1 := by
    rw [certA.qe_eq, hexpA]
    omega
  have hqeB : certB.qe = n - 1 := by
    rw [certB.qe_eq, hexpB]
    omega

  have hqsum' :
      certS.qe + certA.qe + certB.qe ≤ 2 * n := by
    simpa [cert, Cfam, centre, Fin.sum_univ_succ] using hqsum
  rw [hqeS, hqeA, hqeB] at hqsum'
  omega

#print axioms no_sharp_with_two_support_one_deficit_two

end JSP000404Research
