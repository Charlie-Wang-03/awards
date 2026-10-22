import JSP000404Research.ThreeFiveSupportThreeRigidity
import JSP000404Research.SixPointUnitGapBudget
import Mathlib.Tactic

/-!
# Saturated n=3 five-centre companion: all nonzero quotients are units

The known actual AngleCap top+next five-centre obstruction requires one
exponent-zero, support-three companion, with quotient sum exactly three.
This file extracts the stronger per-coordinate unit shape: no quotient
can exceed one, and there are exactly three unit quotient positions.

This is an actual geometric NECESSARY condition; no planar exclusion
of the remaining sharp motif is asserted.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Equality of quotient mass with positive support forces each positive
quotient to be one. The proof uses the exact floor-excess identity. -/
theorem quotient_le_one_of_sum_eq_positiveSupport
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hsum : (∑ i : I, q i) = positiveSupport q) :
    ∀ i : I, q i ≤ 1 := by
  classical
  have hexcess : floorExcess q = 0 := by
    have h := floorExcess_add_positiveSupport q
    omega
  intro i
  have hsingle :
      q i - 1 ≤ ∑ j : I, (q j - 1) := by
    exact Finset.single_le_sum
      (f := fun j : I => q j - 1)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  change q i - 1 ≤ floorExcess q at hsingle
  omega

/-- Genuine n=3 saturated support-three centre has precisely three
unit-quotient coordinates, all other coordinates zero. -/
theorem three_scale_support_three_all_unit_quotients
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {delta t : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hsupport : 3 ≤ positiveSupport (centreQuotient C t)) :
    (∀ r, centreQuotient C t r ≤ 1) ∧
      unitSupport (centreQuotient C t) = 3 := by
  let q := centreQuotient C t
  obtain ⟨_hexp, hthree, hfull⟩ :=
    three_scale_high_support_exact_rigidity C
      hdelta0 hdeltaHalf ht hsupport
  have hsum : (∑ r, q r) = positiveSupport q := by
    dsimp [q]
    rw [hfull, hthree]
  have hle : ∀ r, q r ≤ 1 :=
    quotient_le_one_of_sum_eq_positiveSupport q hsum
  have hnonunit : nonUnitPositiveSupport q = 0 := by
    classical
    unfold nonUnitPositiveSupport
    apply Finset.sum_eq_zero
    intro r _
    have hr := hle r
    simp [show ¬(2 ≤ q r) by omega]
  have hpart := positiveSupport_eq_unit_add_nonUnit q
  rw [hnonunit] at hpart
  constructor
  · exact hle
  · dsimp [q] at hpart ⊢
    omega

/-- In the genuine five-centre top+next obstruction, at least one of
the three lower companions has exactly three unit quotient gaps. -/
theorem top_next_five_has_saturated_unit_companion
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (hs : centreExponent Cs t = 2)
    (ha : centreExponent Ca t = 1) :
    ((∀ r, centreQuotient Cb t r ≤ 1) ∧
      unitSupport (centreQuotient Cb t) = 3) ∨
    ((∀ r, centreQuotient Cc t r ≤ 1) ∧
      unitSupport (centreQuotient Cc t) = 3) ∨
    ((∀ r, centreQuotient Cd t r ≤ 1) ∧
      unitSupport (centreQuotient Cd t) = 3) := by
  rcases top_next_three_exact_support_three_companion
      hp hcap hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hsd hab hac had hbc hbd hcd
      Cs Ca Cb Cc Cd hs ha with hb | hc | hd
  · exact Or.inl
      (three_scale_support_three_all_unit_quotients Cb
        hdelta0 hdeltaHalf ht (by omega))
  · exact Or.inr (Or.inl
      (three_scale_support_three_all_unit_quotients Cc
        hdelta0 hdeltaHalf ht (by omega)))
  · exact Or.inr (Or.inr
      (three_scale_support_three_all_unit_quotients Cd
        hdelta0 hdeltaHalf ht (by omega)))

#print axioms quotient_le_one_of_sum_eq_positiveSupport
#print axioms three_scale_support_three_all_unit_quotients
#print axioms top_next_five_has_saturated_unit_companion

end JSP000404Research
