import JSP000404Research.SixPointUnitPhaseCover
import JSP000404Research.SixPointNFourNoCover
import Mathlib.Tactic

/-!
# Unified six-point unit-slot phase-cover terminal for every n >= 4

The six-point top + five n-3 profile has at most ten q=1 slots.

For n>=5, ten slots are already fewer than the lower-branch phase-cover
minimum 2n+2, so SixPointUnitPhaseCover closes immediately.

For n=4, any hypothetical cover needs at least ten selected slots.  Since at
most ten global unit-gap slots exist, coverage forces equality:

  card(GlobalUnitGapSlot) = 10
  and
  sum_i unitSupport(q_i) = 10.

The n=4 equality terminal then applies.  If critical obstructions are genuinely
transition-only, so that same-sign unit slots are unusable, the farthest-point
strict-exposure contradiction from SixPointNFourNoCover rules out the cover.

Thus one theorem now handles the entire six-point terminal n>=4.
-/

namespace JSP000404Research

theorem no_six_point_transition_only_globalUnitGapSlot_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hSameUnusable :
      ∀ u : GlobalUnitGapSlot C t,
        GlobalUnitGapSameSign C t u →
        ∀ x : ℝ, ¬ A u x)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  by_cases hn5 : 5 ≤ n
  · exact
      no_six_point_globalUnitGapSlot_cover
        C hn hn5 hdelta0 hdeltaHalf ht
        hcard top hTop hMin A S hcoverLower
  · have hn4eq : n = 4 := by omega
    subst n
    intro hcover
    have hslot10 :
        Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
      six_point_globalUnitGapSlot_card_le_ten
        C (by norm_num : 4 ≤ 4)
        hdelta0 (by linarith) ht
        hcard top
        (by simpa using hTop)
        (by
          intro i hi
          simpa using hMin i hi)
    have hSle :
        S.card ≤ Fintype.card (GlobalUnitGapSlot C t) := by
      simpa using Finset.card_le_univ S
    have hcoverReal :
        (4 : ℝ) + delta ≤ (S.card : ℝ) * delta :=
      hcoverLower S (by intro x hx; exact hx) hcover
    have hneed :
        10 ≤ S.card := by
      have h :=
        phase_cover_count_lower
          (n := 4) (m := S.card)
          (by norm_num : 1 ≤ 4)
          hdelta0 hdeltaHalf hcoverReal
      norm_num at h
      exact h
    have hslotEq :
        Fintype.card (GlobalUnitGapSlot C t) = 10 := by
      omega
    have hunitTotal :
        (∑ i : V,
          unitSupport (centreQuotient (C i) t)) = 10 := by
      rw [← globalUnitGapSlot_card_eq_sum_unitSupport C t]
      exact hslotEq
    have hno :=
      no_six_point_n_four_transition_only_unit_slot_cover
        hp hcap hdelta0 hdeltaHalf
        (by simpa using ht) hlam
        C hcard top
        (by simpa using hTop)
        (by
          intro i hi
          simpa using hMin i hi)
        hunitTotal A S hSameUnusable
        (by
          intro T hTS hTCover
          simpa using hcoverLower T hTS hTCover)
    exact hno hcover

#print axioms no_six_point_transition_only_globalUnitGapSlot_cover

end JSP000404Research
