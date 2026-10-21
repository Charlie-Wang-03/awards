import JSP000404Research.NoTopNextLayerFourCentrePacking
import Mathlib.Tactic

/-!
# Two support-two centres forced among four second-layer centres

For four pairwise distinct genuine planar centres with exponent n-2,
the actual deficit-two support classification restricts positive
quotient support to {1,2}. The certified four-centre transition
packing forbids any three of the four having support one.

Therefore at least two of the four must have support two.  This is
a genuine geometric necessary condition in the n=3 five-centre
no-top overweight motif, NOT a proof that the motif is impossible.
-/

namespace JSP000404Research

/-- For four distinct actual next-layer centres, there is a pair whose
positive quotient support is two.  The proof uses real AngleCap packing
to exclude each of the four possible triples of support-one centres. -/
theorem two_support_two_among_four_second_layer_centres
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
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = n - 2)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hC : centreExponent Cc t = n - 2) :
    (positiveSupport (centreQuotient Cs t) = 2 ∧
     positiveSupport (centreQuotient Ca t) = 2) ∨
    (positiveSupport (centreQuotient Cs t) = 2 ∧
     positiveSupport (centreQuotient Cb t) = 2) ∨
    (positiveSupport (centreQuotient Cs t) = 2 ∧
     positiveSupport (centreQuotient Cc t) = 2) ∨
    (positiveSupport (centreQuotient Ca t) = 2 ∧
     positiveSupport (centreQuotient Cb t) = 2) ∨
    (positiveSupport (centreQuotient Ca t) = 2 ∧
     positiveSupport (centreQuotient Cc t) = 2) ∨
    (positiveSupport (centreQuotient Cb t) = 2 ∧
     positiveSupport (centreQuotient Cc t) = 2) := by
  have hclassS :=
    actual_deficit_two_support_one_or_two Cs hn hdelta0 hdeltaHalf ht hS
  have hclassA :=
    actual_deficit_two_support_one_or_two Ca hn hdelta0 hdeltaHalf ht hA
  have hclassB :=
    actual_deficit_two_support_one_or_two Cb hn hdelta0 hdeltaHalf ht hB
  have hclassC :=
    actual_deficit_two_support_one_or_two Cc hn hdelta0 hdeltaHalf ht hC
  have hnoSAB :
      ¬ (positiveSupport (centreQuotient Cs t) = 1 ∧
         positiveSupport (centreQuotient Ca t) = 1 ∧
         positiveSupport (centreQuotient Cb t) = 1) := by
    rintro ⟨hs, ha, hb⟩
    exact no_three_support_one_among_four_second_layer_centres
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc Cs Ca Cb Cc
      hS hA hB hC hs ha hb
  have hnoSAC :
      ¬ (positiveSupport (centreQuotient Cs t) = 1 ∧
         positiveSupport (centreQuotient Ca t) = 1 ∧
         positiveSupport (centreQuotient Cc t) = 1) := by
    rintro ⟨hs, ha, hc⟩
    exact no_three_support_one_among_four_second_layer_centres
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsc hsb hac hab hbc.symm Cs Ca Cc Cb
      hS hA hC hB hs ha hc
  have hnoSBC :
      ¬ (positiveSupport (centreQuotient Cs t) = 1 ∧
         positiveSupport (centreQuotient Cb t) = 1 ∧
         positiveSupport (centreQuotient Cc t) = 1) := by
    rintro ⟨hs, hb, hc⟩
    exact no_three_support_one_among_four_second_layer_centres
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsc hsa hbc hab.symm hac.symm Cs Cb Cc Ca
      hS hB hC hA hs hb hc
  have hnoABC :
      ¬ (positiveSupport (centreQuotient Ca t) = 1 ∧
         positiveSupport (centreQuotient Cb t) = 1 ∧
         positiveSupport (centreQuotient Cc t) = 1) := by
    rintro ⟨ha, hb, hc⟩
    exact no_three_support_one_among_four_second_layer_centres
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hab hac hsa.symm hbc hsb.symm hsc.symm Ca Cb Cc Cs
      hA hB hC hS ha hb hc
  rcases hclassS with hsupS | hsupS <;>
    rcases hclassA with hsupA | hsupA <;>
    rcases hclassB with hsupB | hsupB <;>
    rcases hclassC with hsupC | hsupC <;>
    omega

#print axioms two_support_two_among_four_second_layer_centres

end JSP000404Research
