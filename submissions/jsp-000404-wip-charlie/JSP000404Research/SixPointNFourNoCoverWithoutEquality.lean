import JSP000404Research.SixPointNFourDirectNoCover
import JSP000404Research.SixPointUnitGapSlots
import Mathlib.Tactic

/-!
# Six-centre n=4 conditional phase-cover exclusion WITHOUT ten-slot equality

Under one original top centre with exponent 3, and five original minimum
centres with exponent 1, the actual dependent unit-gap slot count is at most 10.

* If at most nine slots exist, the n=4 lower bound for a phase cover is
  already inconsistent with 0 <= delta < 1/2.
* If exactly ten slots exist, the previously kernel-verified unconditional
  same-sign unit gap is unavailable for any transition-only cover.

This removes the total-unitSupport-equality premise of the local cover
obstruction. Both the phase-cover lower bound and the property that a
same-sign original-centre gap is unusable remain EXPLICIT assumptions.
This is not the global six-source Boolean-hole payment.
-/

namespace JSP000404Research

open scoped BigOperators

theorem six_point_n_four_no_transition_only_phase_cover_without_equality
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hSameUnusable :
      ∀ u : GlobalUnitGapSlot C t,
        GlobalUnitGapSameSign C t u →
        ∀ x : ℝ, ¬ A u x)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  have hslotTen :
      Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
    six_point_globalUnitGapSlot_card_le_ten
      C (by norm_num : 4 ≤ 4)
      hdelta0 (by linarith : delta < 1)
      ht hcard top hTop hMin
  by_cases hsmall : Fintype.card (GlobalUnitGapSlot C t) ≤ 9
  · intro hcover
    have hcardS : S.card ≤ 9 :=
      (Finset.card_le_univ S).trans hsmall
    have hlower :
        (4 : ℝ) + delta ≤ (S.card : ℝ) * delta :=
      hcoverLower S (Finset.Subset.rfl) hcover
    have hcardReal : (S.card : ℝ) ≤ 9 := by
      exact_mod_cast hcardS
    have hmul :
        (S.card : ℝ) * delta ≤ 9 * delta :=
      mul_le_mul_of_nonneg_right hcardReal hdelta0
    linarith
  · have hten : Fintype.card (GlobalUnitGapSlot C t) = 10 := by
      omega
    have htotal :
        (∑ i : V, unitSupport (centreQuotient (C i) t)) = 10 :=
      (globalUnitGapSlot_card_eq_sum_unitSupport C t).symm.trans hten
    exact
      six_point_n_four_equality_no_transition_only_phase_cover_direct
        hp hcap hdelta0 hdeltaHalf ht hlam
        C hcard top hTop hMin htotal
        A S hSameUnusable hcoverLower

#print axioms six_point_n_four_no_transition_only_phase_cover_without_equality

end JSP000404Research
