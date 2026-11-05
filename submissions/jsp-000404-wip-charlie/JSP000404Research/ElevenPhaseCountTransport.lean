import JSP000404Research.ElevenPhaseCounting

/-! Transport the four finite group counts to the CNF's prefix-count representation. -/

namespace JSP000404Research.ElevenPhase

open scoped BigOperators

theorem prefixCount_fin_card (input : ℕ → Bool) (n : ℕ) :
    prefixCount input n = ((Finset.univ : Finset (Fin n)).filter fun i ↦ input i.val).card := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range]
  rfl

theorem missingBit_iff (selected : Fin 198 → Bool) (i : ℕ) :
    missingBit selected i = true ↔ slotIndex (missingSlot i) ∉ coveredSet selected := by
  classical
  simp [missingBit, coveredSet, selectedSet, support, Finset.mem_biUnion]

theorem long_prefix_eq (selected : Fin 198 → Bool) :
    prefixCount (chosenLong selected) 22 = ((selectedSet selected) ∩ longGroup).card := by
  classical
  rw [prefixCount_fin_card]
  have hfilter : selectedSet selected ∩ longGroup =
      longGroup.filter (fun row ↦ selected row = true) := by
    ext row
    simp [selectedSet, and_comm]
  rw [hfilter, longGroup, Finset.filter_image,
    Finset.card_image_of_injective _ coordinates_injective.2.2.2]
  congr 1
  ext i
  simp [chosenLong, longIndex, Nat.mod_eq_of_lt i.isLt]

theorem medium_prefix_eq (selected : Fin 198 → Bool) :
    prefixCount (missingBit selected) 66 = (missingGroup selected mediumGroup).card := by
  classical
  rw [prefixCount_fin_card]
  have hfilter : missingGroup selected mediumGroup =
      mediumGroup.filter (fun slot ↦ slot ∉ coveredSet selected) := by
    ext slot
    simp [missingGroup]
  rw [hfilter, mediumGroup_image, Finset.filter_image,
    Finset.card_image_of_injective _ coordinates_injective.1]
  congr 1
  ext i
  simp [missingBit_iff, missingSlot, mediumSlot, Nat.mod_eq_of_lt i.isLt]

theorem high_prefix_eq (selected : Fin 198 → Bool) :
    prefixCount (fun i ↦ missingBit selected (66 + i)) 22 =
      (missingGroup selected highGroup).card := by
  classical
  rw [prefixCount_fin_card]
  have hfilter : missingGroup selected highGroup =
      highGroup.filter (fun slot ↦ slot ∉ coveredSet selected) := by
    ext slot
    simp [missingGroup]
  rw [hfilter, highGroup, Finset.filter_image,
    Finset.card_image_of_injective _ coordinates_injective.2.1]
  congr 1
  ext i
  have hnot : ¬66 + i.val < 66 := by omega
  simp [missingBit_iff, missingSlot, highSlot, hnot, Nat.mod_eq_of_lt i.isLt]

theorem high341_covered (selected : Fin 198 → Bool)
    (hzero : (missingGroup selected specialGroup).card = 0) :
    ∀ i, i < 22 → ∃ n ∈ coverers (high341Slot i), selected (rowIndex n) = true := by
  classical
  intro i hi
  let slot := slotIndex (high341Slot i)
  have hgroup : slot ∈ specialGroup := by
    unfold specialGroup
    apply Finset.mem_image.mpr
    refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    simp [slot, high341Slot, Nat.mod_eq_of_lt hi]
  have hcovered : slot ∈ coveredSet selected := by
    by_contra hn
    have hm : slot ∈ missingGroup selected specialGroup := Finset.mem_sdiff.mpr ⟨hgroup, hn⟩
    have hempty := Finset.card_eq_zero.mp hzero
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm
  obtain ⟨row, hselected, hs⟩ := Finset.mem_biUnion.mp hcovered
  refine ⟨row.val, ?_, ?_⟩
  · unfold coverers
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_range.mpr row.isLt
    · have hcover := (Finset.mem_filter.mp hs).2
      simpa [rowIndex, Nat.mod_eq_of_lt row.isLt, slot] using hcover
  · have hchosen := (Finset.mem_filter.mp hselected).2
    simpa [rowIndex, Nat.mod_eq_of_lt row.isLt] using hchosen

theorem missing_cross_exclusion (selected : Fin 198 → Bool)
    (hzero : (missingGroup selected highGroup).card = 0 ∨
      (missingGroup selected mediumGroup).card = 0)
    {h m : ℕ} (hh : h < 22) (hm : m < 66)
    (hhigh : missingBit selected (66 + h) = true)
    (hmedium : missingBit selected m = true) : False := by
  have hhighPos : 0 < prefixCount (fun i ↦ missingBit selected (66 + i)) 22 := by
    rw [prefixCount_fin_card]
    apply Finset.card_pos.mpr
    exact ⟨⟨h, hh⟩, by simp [hhigh]⟩
  have hmedPos : 0 < prefixCount (missingBit selected) 66 := by
    rw [prefixCount_fin_card]
    apply Finset.card_pos.mpr
    exact ⟨⟨m, hm⟩, by simp [hmedium]⟩
  rw [high_prefix_eq] at hhighPos
  rw [medium_prefix_eq] at hmedPos
  omega

#print axioms long_prefix_eq
#print axioms medium_prefix_eq
#print axioms high_prefix_eq
#print axioms missing_cross_exclusion

end JSP000404Research.ElevenPhase
