import JSP000404Research.ThreeFiveNextSupportTwoRigidity
import JSP000404Research.ThreeScaleZeroGapSlack
import Mathlib.Tactic

/-!
# Genuine no-top five-centre necessary angular condition at n = 3

The four-next AngleCap packing theorem forces two actual centres with
exponent one, quotient support two and quotient sum three.  Combining
this with the exact continuous remainder budget t - sum(floors) = delta
shows that *every* zero quotient gap at each such centre has scaled
angular width at most delta.

This is an unconditional local NECESSARY constraint of the still-open
no-top five-centre motif A, not a geometric exclusion of that motif.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exact three-unit quotient mass and all zero-gap angular widths
at a saturated support-two planar centre. -/
def nextNarrowSupportTwo
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) (t delta : ℝ) : Prop :=
  nextSaturatedSupportTwo C t ∧
  ∀ r, centreQuotient C t r = 0 →
    t * C.gaps.get r ≤ delta

theorem next_narrow_of_saturated_support_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hsat : nextSaturatedSupportTwo C t) :
    nextNarrowSupportTwo C t delta := by
  have ht0 : 0 ≤ t := by linarith
  have hg0 : ∀ j : Fin C.gaps.length, 0 ≤ t * C.gaps.get j := by
    intro j
    exact mul_nonneg ht0
      (C.gaps_nonneg (C.gaps.get j) (List.get_mem _ _))
  have hgsum : (∑ j : Fin C.gaps.length, C.gaps.get j) = 1 := by
    rw [← List.sum_ofFn]
    simpa using C.gaps_sum
  have hqsum :
      (∑ j : Fin C.gaps.length, Nat.floor (t * C.gaps.get j)) = 3 := by
    simpa [centreQuotient] using hsat.2.1
  refine ⟨hsat, ?_⟩
  intro j hz
  exact scaled_zero_floor_gap_le_three_slack
    (fun k => C.gaps.get k) t delta ht hg0 hgsum hqsum
    j (by simpa [centreQuotient] using hz)

/-- The genuine four-next n=3 no-top motif has TWO distinct
centres whose quotient mass and zero-gap angular widths are both
exactly constrained by the same delta remainder budget. -/
theorem two_narrow_next_among_four_n3
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
    (nextNarrowSupportTwo Cs t delta ∧ nextNarrowSupportTwo Ca t delta) ∨
    (nextNarrowSupportTwo Cs t delta ∧ nextNarrowSupportTwo Cb t delta) ∨
    (nextNarrowSupportTwo Cs t delta ∧ nextNarrowSupportTwo Cc t delta) ∨
    (nextNarrowSupportTwo Ca t delta ∧ nextNarrowSupportTwo Cb t delta) ∨
    (nextNarrowSupportTwo Ca t delta ∧ nextNarrowSupportTwo Cc t delta) ∨
    (nextNarrowSupportTwo Cb t delta ∧ nextNarrowSupportTwo Cc t delta) := by
  have hpair := two_saturated_next_among_four_n3
    hp hcap hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc Cs Ca Cb Cc hS hA hB hC
  have hs : nextSaturatedSupportTwo Cs t →
      nextNarrowSupportTwo Cs t delta :=
    next_narrow_of_saturated_support_two Cs hdelta0 ht
  have ha : nextSaturatedSupportTwo Ca t →
      nextNarrowSupportTwo Ca t delta :=
    next_narrow_of_saturated_support_two Ca hdelta0 ht
  have hb : nextSaturatedSupportTwo Cb t →
      nextNarrowSupportTwo Cb t delta :=
    next_narrow_of_saturated_support_two Cb hdelta0 ht
  have hc : nextSaturatedSupportTwo Cc t →
      nextNarrowSupportTwo Cc t delta :=
    next_narrow_of_saturated_support_two Cc hdelta0 ht
  rcases hpair with h | h | h | h | h | h
  · exact Or.inl ⟨hs h.1, ha h.2⟩
  · exact Or.inr (Or.inl ⟨hs h.1, hb h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hs h.1, hc h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha h.1, hb h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha h.1, hc h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb h.1, hc h.2⟩))))

#print axioms next_narrow_of_saturated_support_two
#print axioms two_narrow_next_among_four_n3

end JSP000404Research
