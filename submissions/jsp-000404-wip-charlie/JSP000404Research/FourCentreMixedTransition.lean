import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# The mixed four-centre top-layer case is forced to transition quotient one

Assume three distinct centres in the lower branch:

* a sharp centre s with exponent n-1;
* a support-one deficit-two centre a with exponent n-2;
* a support-two deficit-two centre b with exponent n-2.

The first two transition quotients are n and n-1.  Global transition-arc
packing bounds the sum of all three transition quotients by 2n.  Since b's
transition quotient is positive, it is forced to be exactly one.

Thus the mixed case, if it exists at all, has the extremal support-two split

  transition quotient = 1,
  hidden positive quotient = n-1.

This is the discrete reduction needed before attacking the remaining geometry.
-/

namespace JSP000404Research

open scoped BigOperators

theorem mixed_support_two_transition_qe_eq_one
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
    (hsuppB : positiveSupport (centreQuotient Cb t) = 2) :
    let certB :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0
          (by linarith : delta < 1) ht hlam
          b Cb (by rw [hexpB]; omega))
    certB.qe = 1 := by
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

  let certS :
      HighExponentTransitionIntervalCertificate hp t s Cs :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        s Cs (by rw [hexpS]; omega))
  let certA :
      HighExponentTransitionIntervalCertificate hp t a Ca :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        a Ca (by rw [hexpA]))
  let certB :
      HighExponentTransitionIntervalCertificate hp t b Cb :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        b Cb (by rw [hexpB]))

  have hqeS : certS.qe = n := by
    have h :=
      highTransition_qe_eq_exponent_add_one_of_support_one
        Cs certS hsuppS
    rw [h, hexpS]
    omega
  have hqeA : certA.qe = n - 1 := by
    have h :=
      highTransition_qe_eq_exponent_add_one_of_support_one
        Ca certA hsuppA
    rw [h, hexpA]
    omega

  let centre : Fin 3 → Fin 4 :=
    Fin.cases s (fun r : Fin 2 =>
      Fin.cases a (fun _ : Fin 1 => b) r)
  let Cfam : ∀ r : Fin 3, CentreProjectiveCycle hp (centre r) :=
    Fin.cases Cs (fun r : Fin 2 =>
      Fin.cases Ca (fun _ : Fin 1 => Cb) r)
  let cert : ∀ r : Fin 3,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) :=
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

  have hqsum :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n) hdelta0 hdeltaHalf ht
      centre hcentre Cfam cert
  have hqsum' :
      certS.qe + certA.qe + certB.qe ≤ 2 * n := by
    simpa [cert, Cfam, centre, Fin.sum_univ_succ] using hqsum
  have hqeBpos : 1 ≤ certB.qe :=
    Nat.one_le_iff_ne_zero.mpr certB.qe_ne
  rw [hqeS, hqeA] at hqsum'
  have hqeB : certB.qe = 1 := by omega
  simpa [certB] using hqeB

#print axioms mixed_support_two_transition_qe_eq_one

end JSP000404Research
