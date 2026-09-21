import JSP000404Research.MinimalPhaseCover
import JSP000404Research.GlobalTurnSlots
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Minimum-cardinality phase covers with common dominators

Two ancestor bad intervals attached to the same terminal transition need not be
nested with each other.  The correct compression principle is therefore not
pairwise nesting but common domination.

Assume every obstruction i is assigned to a slot, and the slot has a
distinguished terminal obstruction top(slot i) whose bad set contains the bad
set of i.  In a minimum-cardinality cover, two selected obstructions cannot
share one slot:

* if the terminal dominator is already selected, one ancestor is redundant;
* otherwise replace the two selected ancestors by the one terminal dominator.

Thus the slot map is injective on a minimum-cardinality cover.

Combined with the global lower-branch turn-slot budget, this yields the same
phase-cover contradiction as the older nested-fibre route, under a strictly
weaker geometric hypothesis.
-/

namespace JSP000404Research

/-- A subcover of minimum cardinality among all subcovers of S. -/
def MinimumCardCover
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop) (S T : Finset I) : Prop :=
  T ⊆ S ∧
  PredicateCovers A T ∧
  ∀ U : Finset I, U ⊆ S → PredicateCovers A U →
    T.card ≤ U.card

theorem exists_minimum_card_subcover
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop) (S : Finset I)
    (hcover : PredicateCovers A S) :
    ∃ T : Finset I, MinimumCardCover A S T := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ T : Finset I,
      T ⊆ S ∧ PredicateCovers A T ∧ T.card = m
  have hP : ∃ m, P m :=
    ⟨S.card, S, fun _ h => h, hcover, rfl⟩
  let m := Nat.find hP
  obtain ⟨T, hTS, hTCover, hTcard⟩ := Nat.find_spec hP
  refine ⟨T, hTS, hTCover, ?_⟩
  intro U hUS hUCover
  have hPU : P U.card := ⟨U, hUS, hUCover, rfl⟩
  have hmin : m ≤ U.card := Nat.find_min' hP hPU
  rw [← hTcard]
  exact hmin

/-- One distinguished obstruction dominates every obstruction in its slot. -/
structure CommonDominatorSlots
    {I Phase Slot : Type*}
    [DecidableEq I]
    (A : I → Phase → Prop)
    (S : Finset I)
    (slot : I → Slot) where
  top : Slot → I
  top_mem : ∀ s, top s ∈ S
  top_slot : ∀ s, slot (top s) = s
  dominates :
    ∀ i, i ∈ S → ∀ x, A i x → A (top (slot i)) x

/-- Minimum covers are injective on common-dominator slots. -/
theorem slot_injective_on_minimum_cover_of_common_dominator
    {I Phase Slot : Type*}
    [DecidableEq I]
    (A : I → Phase → Prop)
    (S T : Finset I)
    (slot : I → Slot)
    (hmin : MinimumCardCover A S T)
    (D : CommonDominatorSlots A S slot) :
    ∀ {i j : I}, i ∈ T → j ∈ T →
      slot i = slot j → i = j := by
  classical
  intro i j hi hj hslot
  by_contra hij
  let k := D.top (slot i)
  have hkS : k ∈ S := D.top_mem (slot i)
  have hdomI : ∀ x, A i x → A k x := by
    intro x hx
    exact D.dominates i (hmin.1 hi) x hx
  have hdomJ : ∀ x, A j x → A k x := by
    intro x hx
    have h := D.dominates j (hmin.1 hj) x hx
    simpa [k, hslot] using h
  by_cases hkT : k ∈ T
  · by_cases hki : k = i
    · have hkj : k ≠ j := by
        intro h
        apply hij
        rw [← hki, h]
      let U := T.erase j
      have hUS : U ⊆ S :=
        (Finset.erase_subset j T).trans hmin.1
      have hUCover : PredicateCovers A U := by
        intro x
        obtain ⟨r, hrT, hrA⟩ := hmin.2.1 x
        by_cases hrj : r = j
        · subst r
          exact ⟨k, Finset.mem_erase.mpr ⟨hkj, hkT⟩,
            hdomJ x hrA⟩
        · exact ⟨r, Finset.mem_erase.mpr ⟨hrj, hrT⟩, hrA⟩
      have hc := hmin.2.2 U hUS hUCover
      have he := Finset.card_erase_of_mem hj
      dsimp [U] at hc
      rw [he] at hc
      omega
    · let U := T.erase i
      have hUS : U ⊆ S :=
        (Finset.erase_subset i T).trans hmin.1
      have hUCover : PredicateCovers A U := by
        intro x
        obtain ⟨r, hrT, hrA⟩ := hmin.2.1 x
        by_cases hri : r = i
        · subst r
          exact ⟨k, Finset.mem_erase.mpr ⟨hki, hkT⟩,
            hdomI x hrA⟩
        · exact ⟨r, Finset.mem_erase.mpr ⟨hri, hrT⟩, hrA⟩
      have hc := hmin.2.2 U hUS hUCover
      have he := Finset.card_erase_of_mem hi
      dsimp [U] at hc
      rw [he] at hc
      omega
  · let U := insert k ((T.erase i).erase j)
    have hUS : U ⊆ S := by
      intro r hr
      simp only [U, Finset.mem_insert, Finset.mem_erase] at hr
      rcases hr with rfl | hr
      · exact hkS
      · exact hmin.1 hr.2.2
    have hUCover : PredicateCovers A U := by
      intro x
      obtain ⟨r, hrT, hrA⟩ := hmin.2.1 x
      by_cases hri : r = i
      · subst r
        exact ⟨k, by simp [U], hdomI x hrA⟩
      · by_cases hrj : r = j
        · subst r
          exact ⟨k, by simp [U], hdomJ x hrA⟩
        · exact ⟨r, by simp [U, hri, hrj, hrT], hrA⟩
    have hjErase : j ∈ T.erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    have hkNot : k ∉ (T.erase i).erase j := by
      intro hk
      exact hkT (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hk))
    have hcardU : U.card = T.card - 1 := by
      dsimp [U]
      rw [Finset.card_insert_of_notMem hkNot,
          Finset.card_erase_of_mem hjErase,
          Finset.card_erase_of_mem hi]
      omega
    have hc := hmin.2.2 U hUS hUCover
    rw [hcardU] at hc
    omega

theorem minimum_cover_card_le_slots_of_common_dominator
    {I Phase Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (A : I → Phase → Prop)
    (S T : Finset I)
    (slot : I → Slot)
    (hmin : MinimumCardCover A S T)
    (D : CommonDominatorSlots A S slot) :
    T.card ≤ Fintype.card Slot := by
  classical
  let f : {i : I // i ∈ T} → Slot := fun i => slot i.1
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact slot_injective_on_minimum_cover_of_common_dominator
      A S T slot hmin D i.2 j.2 hij
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f] using hcard

/-- Final phase contradiction under a common-dominator slot certificate. -/
theorem no_phase_cover_of_common_dominator_turn_slots
    {I Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (L R : I → ℝ)
    (slot : I → Slot)
    (S : Finset I)
    (D : CommonDominatorSlots
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
        PredicateCovers (InClosedInterval L R) T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers (InClosedInterval L R) S := by
  intro hcover
  obtain ⟨T, hmin⟩ :=
    exists_minimum_card_subcover
      (InClosedInterval L R) S hcover
  have hcardSlot :
      T.card ≤ Fintype.card Slot :=
    minimum_cover_card_le_slots_of_common_dominator
      (InClosedInterval L R) S T slot hmin D
  have hslotNat :
      Fintype.card Slot ≤ 2 * n :=
    hull_count_upper hdeltaHalf hslotBudget
  have hcardUpper : T.card ≤ 2 * n :=
    hcardSlot.trans hslotNat
  have hcoverReal :=
    hcoverLower T hmin.1 hmin.2.1
  have hcardLower :=
    phase_cover_count_lower
      hn hdelta0 hdeltaHalf hcoverReal
  omega

#print axioms exists_minimum_card_subcover
#print axioms slot_injective_on_minimum_cover_of_common_dominator
#print axioms minimum_cover_card_le_slots_of_common_dominator
#print axioms no_phase_cover_of_common_dominator_turn_slots

end JSP000404Research
