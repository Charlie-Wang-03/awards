import JSP000404Research.GeneralMixedContradiction
import JSP000404Research.SharpSupportTwoMultiplicity
import JSP000404Research.FourCentreTransitionCases
import Mathlib.Tactic

/-!
# A top exponent and two next-layer exponents cannot coexist with a fourth point

For arbitrary finite injective planar AngleCap data in the lower branch
n >= 3, three distinct actual centres with exponents n-1, n-2, n-2
cannot coexist with any fourth distinct centre. The deficit-two
quotient classification gives exactly four cases:
  1/1: verified transition-quotient packing,
  1/2 and 2/1: actual cardinality-free mixed fourth-centre exclusion,
  2/2: pinned sharp-centre two-cluster triangle obstruction.

This is a genuine structural exclusion at the very top of the dyadic
profile, without an auxiliary payment condition or any new sorry.
It is NOT the full JSP-000404 global six-source inequality.
-/

namespace JSP000404Research

open scoped BigOperators

theorem actual_deficit_two_support_one_or_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} (C : CentreProjectiveCycle hp i)
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

/-- The actual planar top+two-next-layer profile is geometrically
impossible as soon as there is a fourth distinct centre. -/
theorem no_top_and_two_next_with_fourth
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
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
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hsupA :=
    actual_deficit_two_support_one_or_two
      Ca hn hdelta0 hdeltaHalf ht hA
  have hsupB :=
    actual_deficit_two_support_one_or_two
      Cb hn hdelta0 hdeltaHalf ht hB
  rcases hsupA with hA1 | hA2 <;>
    rcases hsupB with hB1 | hB2
  · have htpos : 0 < t := by
      rw [ht]
      have hnReal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let HS :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
          s Cs (by rw [hS]; omega))
    let HA :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
          a Ca (by rw [hA]))
    let HB :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
          b Cb (by rw [hB]))
    exact no_sharp_with_two_support_one_deficit_two
      hp hn hdelta0 hdeltaHalf ht
      hsa hsb hab Cs Ca Cb HS HA HB hS hA hB hA1 hB1
  · exact no_top_mixed_deficitTwo_with_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hA1 hB2
  · exact no_top_mixed_deficitTwo_with_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsa hsc hab.symm hbc hac
      Cs Cb Ca hS hB hA hB1 hA2
  · have hs : SharpAt p delta lam s :=
      concrete_unit_deficit_is_sharp
        hp hcap (by omega : 2 ≤ n) hdelta0 hdelta1 ht hlam
        s Cs hS
    exact no_two_supportTwo_deficitTwo_around_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      hs Ca Cb hA hB hA2 hB2

#print axioms actual_deficit_two_support_one_or_two
#print axioms no_top_and_two_next_with_fourth

end JSP000404Research
