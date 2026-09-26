import JSP000404Research.SixPointThirdLayerTerminal
import JSP000404Research.ExactWitnessDeficitTwo
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Exact-witness centre in the six-point third-layer terminal

In the six-point terminal there is one top n-1 centre, no n-2 centre, and all
five remaining vertices have exponent n-3.

The centre W.b of any exact maximum-angle witness cannot be top.  Since there
is no second layer, it is therefore one of the n-3 minima.

The exact witness short arc forces a quotient equal to one at W.b.  In the
deficit-three classification this immediately excludes support one: support
one would make the whole quotient sum equal to one, whereas an n-3/support-one
centre has quotient sum n-2 >= 2.

Hence W.b has support two or three.  In the support-two branch the two positive
quotients are exactly 1 and n-2.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A three-layer profile with no second layer forces the exact-witness centre
into the minimum n-3 layer. -/
theorem exactWitness_centre_eq_n_sub_three_of_no_second_layer
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hlower : n - 3 ≤ centreExponent C t)
    (hnoSecond : centreExponent C t ≠ n - 2) :
    centreExponent C t = n - 3 := by
  have hupper :=
    exactWitness_centreExponent_le_n_sub_two
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam W C
  omega

/-- An exact-witness centre in the n-3 layer cannot have quotient support one. -/
theorem exactWitness_deficitThree_not_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3) :
    positiveSupport (centreQuotient C t) ≠ 1 := by
  intro hsup
  have hdelta1 : delta < 1 := by linarith
  have hsum :=
    deficit_three_support_one_sum
      C hn hdelta0 hdelta1 ht hexp hsup
  have hone :=
    centreQuotient_exists_eq_one_of_exactWitness
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
  have hsumOne :=
    sum_eq_one_of_positiveSupport_one_of_exists_eq_one
      (centreQuotient C t) hsup hone
  rw [hsum] at hsumOne
  omega

/-- The exact-witness n-3 centre has support two or support three. -/
theorem exactWitness_deficitThree_support_two_or_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3) :
    positiveSupport (centreQuotient C t) = 2 ∨
      positiveSupport (centreQuotient C t) = 3 := by
  have hdelta1 : delta < 1 := by linarith
  rcases concrete_deficit_three_structure
      C hn hdelta0 hdelta1 ht hexp with h1 | h2 | h3
  · exact False.elim
      ((exactWitness_deficitThree_not_support_one
        hp hcap hn hdelta0 hdeltaHalf ht hlam W C hexp) h1.1)
  · exact Or.inl h2.1
  · exact Or.inr h3.1

/-- Support-two exact-witness third-layer shape: one positive quotient is the
witness unit quotient and the other is exactly n-2. -/
theorem exactWitness_deficitThree_support_two_exact_quotient_pair
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ e f : Fin C.gaps.length,
      e ≠ f ∧
      centreQuotient C t e = 1 ∧
      centreQuotient C t f = n - 2 ∧
      ∀ i, i ≠ e → i ≠ f →
        centreQuotient C t i = 0 := by
  have hdelta1 : delta < 1 := by linarith
  have hsum :=
    deficit_three_support_two_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  obtain ⟨e, he⟩ :=
    centreQuotient_exists_eq_one_of_exactWitness
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
  obtain ⟨f, hfe, hf, hzero⟩ :=
    support_two_with_one_exact_shape
      (centreQuotient C t) (n - 1)
      hsupport hsum he
  have hf' : centreQuotient C t f = n - 2 := by
    rw [hf]
    omega
  exact ⟨e, f, hfe.symm, he, hf', hzero⟩

#print axioms exactWitness_centre_eq_n_sub_three_of_no_second_layer
#print axioms exactWitness_deficitThree_not_support_one
#print axioms exactWitness_deficitThree_support_two_or_three
#print axioms exactWitness_deficitThree_support_two_exact_quotient_pair

end JSP000404Research
