import JSP000404Research.RestrictedCriticalPhaseCover
import JSP000404Research.GlobalTurnSlots
import Mathlib.Tactic

/-!
# Nonvacuous common-dominator phase-cover compression

Legacy MinimumDominatingPhaseCover treats a finite family of bounded
real intervals as a cover of all Real. This hypothesis cannot hold.

On an explicitly restricted phase-domain, assume each geometric slot
has one terminal obstruction that dominates every obstruction assigned
to that slot, at each phase IN the domain.

Instead of selecting a minimum-cardinality subcover, replace EVERY
obstruction by its terminal dominator simultaneously: the resulting
finite cover has at most one member per slot. This avoids unnecessary
minimality and interval-fibre nesting assumptions.

No claim is made that the actual planar AngleCap setting provides
the geometric terminal-dominator certificate.
-/

namespace JSP000404Research

structure RestrictedCommonDominatorSlots
    {I Phase Slot : Type*} [DecidableEq I]
    (Domain : Phase → Prop)
    (A : I → Phase → Prop)
    (S : Finset I)
    (slot : I → Slot) where
  top : Slot → I
  top_mem : ∀ sl, top sl ∈ S
  dominates : ∀ i, i ∈ S → ∀ x, Domain x →
    A i x → A (top (slot i)) x

/-- Directly replace all obstructions in a finite restricted-domain
cover with their terminal dominators. Minimal-cardinality selection
and pairwise interval nesting are both unnecessary. -/
theorem restricted_cover_compress_via_common_dominator
    {I Phase Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (Domain : Phase → Prop) (A : I → Phase → Prop)
    (S : Finset I) (slot : I → Slot)
    (D : RestrictedCommonDominatorSlots Domain A S slot)
    (hcover : PredicateCoversOn Domain A S) :
    ∃ T : Finset I, T ⊆ S ∧
      PredicateCoversOn Domain A T ∧
      T.card ≤ Fintype.card Slot := by
  classical
  let T : Finset I := Finset.univ.image D.top
  have hTsub : T ⊆ S := by
    intro k hk
    obtain ⟨sl, _, hsl⟩ := Finset.mem_image.mp hk
    rw [← hsl]
    exact D.top_mem sl
  have hTCover : PredicateCoversOn Domain A T := by
    intro x hx
    obtain ⟨i, hi, hA⟩ := hcover x hx
    refine ⟨D.top (slot i), ?_, D.dominates i hi x hx hA⟩
    exact Finset.mem_image.mpr
      ⟨slot i, Finset.mem_univ _, rfl⟩
  have hcard : T.card ≤ Fintype.card Slot := by
    have hImage := Finset.card_image_le
      (s := (Finset.univ : Finset Slot)) (f := D.top)
    simpa [T] using hImage
  exact ⟨T, hTsub, hTCover, hcard⟩

/-- A correct restricted-domain version of the common-dominator
turn-slot phase contradiction: a domain-specific cover LOWER bound
and a terminal-dominator slot UPPER bound are inconsistent for
0 <= delta < 1/2. Unlike the legacy form, the cover antecedent
can hold for an actual bounded phase domain. -/
theorem no_restricted_phase_cover_of_common_dominator_turn_slots
    {I Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (Domain : ℝ → Prop)
    (L R : I → ℝ)
    (slot : I → Slot)
    (S : Finset I)
    (D : RestrictedCommonDominatorSlots Domain
      (InClosedInterval L R) S slot)
    (n : ℕ) (delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hslotBudget :
      (Fintype.card Slot : ℝ) ≤
        2 * ((n : ℝ) + delta))
    (hcoverLower :
      ∀ T : Finset I, T ⊆ S →
        PredicateCoversOn Domain (InClosedInterval L R) T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCoversOn Domain (InClosedInterval L R) S := by
  intro hcover
  obtain ⟨T, hTS, hTCover, hcardSlot⟩ :=
    restricted_cover_compress_via_common_dominator
      Domain (InClosedInterval L R) S slot D hcover
  have hslotNat : Fintype.card Slot ≤ 2 * n :=
    hull_count_upper hdeltaHalf hslotBudget
  have hcardUpper : T.card ≤ 2 * n :=
    hcardSlot.trans hslotNat
  have hcoverReal := hcoverLower T hTS hTCover
  have hcardLower :=
    phase_cover_count_lower hn hdelta0 hdeltaHalf hcoverReal
  omega

#print axioms restricted_cover_compress_via_common_dominator
#print axioms no_restricted_phase_cover_of_common_dominator_turn_slots

end JSP000404Research
