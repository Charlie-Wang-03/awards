import JSP000404Research.FourCentreTransitionCases
import JSP000404Research.FourCentreSupportTwoContradiction
import Mathlib.Tactic

/-!
# Four-centre sharp case reduces uniquely to mixed support 1/2

Assume one centre s has exponent n-1 and two other centres a,b both have
exponent n-2 in a four-point lower-branch configuration.

DeficitTwo forces each of a,b to have quotient support either one or two.

* support 1 / support 1 is impossible by global transition-quotient packing;
* support 2 / support 2 is impossible by the small-angle triangle contradiction.

Therefore the only surviving possibility is mixed support:

  (support(a), support(b)) = (1,2) or (2,1).

This file packages that exact reduction so the remaining four-centre geometry
can focus exclusively on the mixed branch.
-/

namespace JSP000404Research

open scoped BigOperators

theorem deficit_two_support_one_or_two_concrete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 2) :
    positiveSupport (centreQuotient C t) = 1 ∨
      positiveSupport (centreQuotient C t) = 2 := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  rcases deficit_two_structure
      (centreQuotient C t) n hn hQ hdef with h1 | h2
  · exact Or.inl h1.1
  · exact Or.inr h2.1

theorem sharp_two_deficit_two_force_mixed_support_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2) :
    (
      positiveSupport (centreQuotient Ca t) = 1 ∧
      positiveSupport (centreQuotient Cb t) = 2
    ) ∨
    (
      positiveSupport (centreQuotient Ca t) = 2 ∧
      positiveSupport (centreQuotient Cb t) = 1
    ) := by
  have hdelta1 : delta < 1 := by linarith
  have hsupA :=
    deficit_two_support_one_or_two_concrete
      Ca hn hdelta0 hdeltaHalf ht hA
  have hsupB :=
    deficit_two_support_one_or_two_concrete
      Cb hn hdelta0 hdeltaHalf ht hB
  rcases hsupA with hA1 | hA2 <;>
    rcases hsupB with hB1 | hB2
  · have HS :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
          s Cs (by rw [hS]; omega))
    have HA :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
          a Ca (by rw [hA]; omega))
    have HB :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
          b Cb (by rw [hB]; omega))
    exact False.elim
      (no_sharp_with_two_support_one_deficit_two
        hp hn hdelta0 hdeltaHalf ht
        hsa hsb hab
        Cs Ca Cb HS HA HB hS hA hB hA1 hB1)
  · exact Or.inl ⟨hA1, hB2⟩
  · exact Or.inr ⟨hA2, hB1⟩
  · exact False.elim
      (no_sharp_with_two_support_two_deficit_two_fin_four
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        hsa hsb hsc hab hac hbc
        Cs Ca Cb hS hA hB hA2 hB2)

#print axioms deficit_two_support_one_or_two_concrete
#print axioms sharp_two_deficit_two_force_mixed_support_fin_four

end JSP000404Research
