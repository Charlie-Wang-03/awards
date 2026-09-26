
import JSP000404Research.ExactWitnessCentreBound
import JSP000404Research.DeficitTwo
import JSP000404Research.SingleSupportDeficit
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Exact witness centres in the deficit-two layer are support two

The exact witness centre quotient list contains quotient 1.

If its exponent is n-2, DeficitTwo gives only two arithmetic possibilities:

* support one and quotient sum n-1;
* support two and quotient sum n.

The first case is impossible for n>=3.  With support one, the quotient equal
to 1 is the unique nonzero coordinate, so the full quotient sum is exactly
one, contradicting sum=n-1.

Hence an exact maximum-angle witness centre in the second exponent layer has

  positiveSupport = 2,
  quotient sum = n.
-/

namespace JSP000404Research

open scoped BigOperators

theorem centreQuotient_exists_eq_one_of_exactWitness
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b) :
    ∃ e, centreQuotient C t e = 1 := by
  have hone :
      1 ∈ quotientList t C.gaps :=
    one_mem_witnessCentre_quotientList
      hp hcap hn hdelta0 ht hlam W C
  rw [← centreQuotient_ofFn C t] at hone
  simpa using hone

/-- If a finite quotient function has support one and takes the value one,
its total sum is one. -/
theorem sum_eq_one_of_positiveSupport_one_of_exists_eq_one
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hsupport : positiveSupport q = 1)
    (hone : ∃ e, q e = 1) :
    (∑ i, q i) = 1 := by
  classical
  obtain ⟨e, he⟩ := hone
  obtain ⟨u, hu, huniq⟩ :=
    existsUnique_positive_of_one_support q hsupport
  have hePos : q e ≠ 0 := by
    rw [he]
    norm_num
  have heu : e = u := huniq e hePos
  have huOne : q u = 1 := by
    rw [← heu]
    exact he
  have hrest :
      (∑ i ∈ (Finset.univ : Finset I).erase u, q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hne
    have hiu : i = u := huniq i hne
    have hiNe : i ≠ u :=
      (Finset.mem_erase.mp hi).1
    exact hiNe hiu
  have hsplit :=
    Finset.add_sum_erase
      (Finset.univ : Finset I) q (Finset.mem_univ u)
  rw [hrest, huOne] at hsplit
  simpa using hsplit.symm

theorem exactWitness_deficitTwo_support_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 2) :
    positiveSupport (centreQuotient C t) = 2 ∧
      (∑ r, centreQuotient C t r) = n := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :
      (∑ r, centreQuotient C t r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hell :
      n - floorExcess (centreQuotient C t) = 2 := by
    change n - centreExponent C t = 2
    rw [hexp]
    omega
  rcases deficit_two_structure
      (centreQuotient C t) n hn hQ hell with h1 | h2
  · have hone :=
      centreQuotient_exists_eq_one_of_exactWitness
        hp hcap hn hdelta0 ht hlam W C
    have hsumOne :=
      sum_eq_one_of_positiveSupport_one_of_exists_eq_one
        (centreQuotient C t) h1.1 hone
    rw [h1.2] at hsumOne
    omega
  · exact h2

#print axioms centreQuotient_exists_eq_one_of_exactWitness
#print axioms sum_eq_one_of_positiveSupport_one_of_exists_eq_one
#print axioms exactWitness_deficitTwo_support_two

end JSP000404Research
