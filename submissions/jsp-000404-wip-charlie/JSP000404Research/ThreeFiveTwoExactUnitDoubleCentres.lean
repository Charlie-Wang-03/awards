import JSP000404Research.ThreeFiveNextSupportTwoRigidity
import JSP000404Research.ThreeFiveTwoOneQuotientShape
import Mathlib.Tactic

/-!
# Genuine four-next-centre n=3: two different 2+1 quotient profiles

The previously kernel-checked geometric packing theorem forces at least
two support-two centres among four genuine exponent-one centres.
The saturated-quotient theorem upgrades each such centre to exactly
one unit and exactly one double quotient, with all other gaps zero.

This preserves the actual planar AngleCap hypotheses and disjunction
of genuine original centres. It does not claim a contradiction.
-/

namespace JSP000404Research

def ExactUnitDoubleCentre
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) (t : ℝ) : Prop :=
  unitSupport (centreQuotient C t) = 1 ∧
    nonUnitPositiveSupport (centreQuotient C t) = 1

theorem two_exact_unit_double_centres_among_four_n3
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = 1)
    (hA : centreExponent Ca t = 1)
    (hB : centreExponent Cb t = 1)
    (hC : centreExponent Cc t = 1) :
    (ExactUnitDoubleCentre Cs t ∧ ExactUnitDoubleCentre Ca t) ∨
    (ExactUnitDoubleCentre Cs t ∧ ExactUnitDoubleCentre Cb t) ∨
    (ExactUnitDoubleCentre Cs t ∧ ExactUnitDoubleCentre Cc t) ∨
    (ExactUnitDoubleCentre Ca t ∧ ExactUnitDoubleCentre Cb t) ∨
    (ExactUnitDoubleCentre Ca t ∧ ExactUnitDoubleCentre Cc t) ∨
    (ExactUnitDoubleCentre Cb t ∧ ExactUnitDoubleCentre Cc t) := by
  have hpair :=
    two_saturated_next_among_four_n3 hp hcap
      hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb Cc hS hA hB hC
  have hcS : nextSaturatedSupportTwo Cs t → ExactUnitDoubleCentre Cs t :=
    next_saturated_support_two_has_exact_two_one_units Cs
  have hcA : nextSaturatedSupportTwo Ca t → ExactUnitDoubleCentre Ca t :=
    next_saturated_support_two_has_exact_two_one_units Ca
  have hcB : nextSaturatedSupportTwo Cb t → ExactUnitDoubleCentre Cb t :=
    next_saturated_support_two_has_exact_two_one_units Cb
  have hcC : nextSaturatedSupportTwo Cc t → ExactUnitDoubleCentre Cc t :=
    next_saturated_support_two_has_exact_two_one_units Cc
  rcases hpair with hSA | hSB | hSC | hAB | hAC | hBC
  · exact Or.inl ⟨hcS hSA.1, hcA hSA.2⟩
  · exact Or.inr (Or.inl ⟨hcS hSB.1, hcB hSB.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hcS hSC.1, hcC hSC.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcA hAB.1, hcB hAB.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcA hAC.1, hcC hAC.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcB hBC.1, hcC hBC.2⟩))))

#print axioms two_exact_unit_double_centres_among_four_n3

end JSP000404Research
