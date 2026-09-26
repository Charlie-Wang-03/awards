import JSP000404Research.SixPointUnitPhaseCover
import Mathlib.Tactic

/-!
# n=4 phase-cover closure from one unusable slot

For n=4 the generic lower-branch cover count is ten:

  2*n + 2 = 10.

Therefore a ten-slot universe can cover only if every available slot is
potentially usable.  If one distinguished slot carries no obstruction at any
phase, deleting it preserves coverage while leaving at most nine slots, a
contradiction.

This is the exact phase-cover outlet needed for the exposed exact-witness
branch of the six-point n=4 equality terminal: there the second unit quotient
is same-sign rather than transitional, so it cannot generate a terminal
critical transition obstruction.
-/

namespace JSP000404Research

/-- Abstract ten-slot terminal at n=4: one globally unusable slot already
prevents a delta-width cover. -/
theorem no_n_four_cover_of_ten_slots_with_unusable
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (A : Slot → ℝ → Prop)
    (S : Finset Slot)
    (unusable : Slot)
    {delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hslotCard : Fintype.card Slot ≤ 10)
    (hunusable : ∀ x : ℝ, ¬ A unusable x)
    (hcoverLower :
      ∀ T : Finset Slot, T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  intro hcover
  let T := S.erase unusable
  have hTCover : PredicateCovers A T := by
    intro x
    obtain ⟨i, hiS, hiA⟩ := hcover x
    have hiNe : i ≠ unusable := by
      intro h
      subst i
      exact hunusable x hiA
    exact ⟨i, Finset.mem_erase.mpr ⟨hiNe, hiS⟩, hiA⟩
  have hTsub : T ⊆ S :=
    Finset.erase_subset _ _
  have hcoverReal :
      (4 : ℝ) + delta ≤ (T.card : ℝ) * delta :=
    hcoverLower T hTsub hTCover
  have hneed : 10 ≤ T.card := by
    have h :=
      phase_cover_count_lower
        (n := 4) (m := T.card)
        (by norm_num : 1 ≤ 4)
        hdelta0 hdeltaHalf hcoverReal
    norm_num at h
    exact h
  have hTcard : T.card ≤ 9 := by
    have hTuniv :
        T ⊆ (Finset.univ.erase unusable : Finset Slot) := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      exact Finset.mem_erase.mpr ⟨hi'.1, Finset.mem_univ i⟩
    have hle :
        T.card ≤ (Finset.univ.erase unusable : Finset Slot).card :=
      Finset.card_le_card hTuniv
    have hcardErase :
        (Finset.univ.erase unusable : Finset Slot).card =
          Fintype.card Slot - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ unusable)]
      simp
    rw [hcardErase] at hle
    omega
  omega

/-- Concrete global-unit-gap specialization. -/
theorem no_six_point_n_four_globalUnitGapSlot_cover_of_unusable
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (unusable : GlobalUnitGapSlot C t)
    (hunusable : ∀ x : ℝ, ¬ A unusable x)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  have hslot10 :
      Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
    six_point_globalUnitGapSlot_card_le_ten
      C (by norm_num : 4 ≤ 4)
      hdelta0 (by linarith) ht
      hcard top hTop hMin
  exact no_n_four_cover_of_ten_slots_with_unusable
    A S unusable hdelta0 hdeltaHalf
    hslot10 hunusable hcoverLower

#print axioms no_n_four_cover_of_ten_slots_with_unusable
#print axioms no_six_point_n_four_globalUnitGapSlot_cover_of_unusable

end JSP000404Research
