import JSP000404Research.ElevenPhaseCoverData
import JSP000404Research.ElevenPhasePackingLogic

/-!
# Counting a separated family against the weighted eleven-phase cover

The integer inequalities here are derived from disjoint supports and the verified finite
cover data. They do not assume a bound on the row family.
-/

namespace JSP000404Research.ElevenPhase

open scoped BigOperators

def selectedSet (selected : Fin 198 → Bool) : Finset (Fin 198) :=
  Finset.univ.filter fun i ↦ selected i = true

def coveredSet (selected : Fin 198 → Bool) : Finset (Fin 132) :=
  (selectedSet selected).biUnion support

def missingGroup (selected : Fin 198 → Bool) (group : Finset (Fin 132)) : Finset (Fin 132) :=
  group \ coveredSet selected

def specialSelected (selected : Fin 198 → Bool) : Finset (Fin 198) :=
  (selectedSet selected).filter fun i ↦ (support i ∩ specialGroup).Nonempty

theorem biUnion_inter_group {α β : Type*} [DecidableEq β] (s : Finset α)
    (supports : α → Finset β) (group : Finset β) :
    (s.biUnion supports) ∩ group = s.biUnion (fun i ↦ supports i ∩ group) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, hg⟩
    exact ⟨i, hi, hx, hg⟩
  · rintro ⟨i, hi, hx, hg⟩
    exact ⟨⟨i, hi, hx⟩, hg⟩

theorem pairwise_disjoint_inter_group {α β : Type*} [DecidableEq β]
    (s : Finset α) (supports : α → Finset β) (group : Finset β)
    (h : (↑s : Set α).PairwiseDisjoint supports) :
    (↑s : Set α).PairwiseDisjoint (fun i ↦ supports i ∩ group) := by
  intro i hi j hj hij
  exact (h hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left

theorem covered_group_card (selected : Fin 198 → Bool) (group : Finset (Fin 132))
    (hdisjoint : (↑(selectedSet selected) : Set (Fin 198)).PairwiseDisjoint support) :
    ((coveredSet selected) ∩ group).card =
      ∑ i ∈ selectedSet selected, (support i ∩ group).card := by
  unfold coveredSet
  rw [biUnion_inter_group, Finset.card_biUnion]
  exact pairwise_disjoint_inter_group _ _ _ hdisjoint

theorem covered_low_card (selected : Fin 198 → Bool)
    (hdisjoint : (↑(selectedSet selected) : Set (Fin 198)).PairwiseDisjoint support) :
    ((coveredSet selected) ∩ lowGroup).card =
      6 * ((selectedSet selected) ∩ longGroup).card := by
  rw [covered_group_card selected lowGroup hdisjoint]
  simp_rw [support_low_count]
  rw [← Finset.sum_filter]
  have hfilter : (selectedSet selected).filter (fun i ↦ i ∈ longGroup) =
      selectedSet selected ∩ longGroup := by ext i; simp
  rw [hfilter]
  simp [Nat.mul_comm]

theorem covered_special_card (selected : Fin 198 → Bool)
    (hdisjoint : (↑(selectedSet selected) : Set (Fin 198)).PairwiseDisjoint support) :
    ((coveredSet selected) ∩ specialGroup).card = 2 * (specialSelected selected).card := by
  rw [covered_group_card selected specialGroup hdisjoint]
  simp_rw [support_special_count]
  rw [← Finset.sum_filter]
  simp [specialSelected, Nat.mul_comm]

theorem missing_weight_bound (selected : Fin 198 → Bool)
    (hdisjoint : (↑(selectedSet selected) : Set (Fin 198)).PairwiseDisjoint support)
    (hsize : 41 ≤ (selectedSet selected).card) :
    (∑ slot ∈ missingGroup selected Finset.univ, slotWeight slot) ≤ 14 := by
  have hsum : (∑ slot ∈ coveredSet selected, slotWeight slot) =
      12 * (selectedSet selected).card := by
    unfold coveredSet
    rw [Finset.sum_biUnion hdisjoint]
    simp_rw [support_weight]
    simp [Nat.mul_comm]
  have hdiff := Finset.sum_sdiff (Finset.subset_univ (coveredSet selected)) (f := slotWeight)
  rw [total_weight, hsum] at hdiff
  change (∑ slot ∈ missingGroup selected Finset.univ, slotWeight slot) ≤ 14
  unfold missingGroup
  omega

theorem sum_group_constant (group : Finset (Fin 132)) (weight : ℕ)
    (hweight : ∀ slot ∈ group, slotWeight slot = weight) :
    (∑ slot ∈ group, slotWeight slot) = weight * group.card := by
  calc
    _ = ∑ _slot ∈ group, weight := Finset.sum_congr rfl hweight
    _ = weight * group.card := by simp [Nat.mul_comm]

theorem missing_weight_decomposition (selected : Fin 198 → Bool) :
    (∑ slot ∈ missingGroup selected Finset.univ, slotWeight slot) =
      2 * (missingGroup selected lowGroup).card +
      3 * (missingGroup selected mediumGroup).card +
      6 * (missingGroup selected highGroup).card +
      6 * (missingGroup selected specialGroup).card := by
  let l := missingGroup selected lowGroup
  let m := missingGroup selected mediumGroup
  let h := missingGroup selected highGroup
  let s := missingGroup selected specialGroup
  obtain ⟨hpart, hlm, hlh, hls, hmh, hms, hhs⟩ := group_partition
  have hlm' : Disjoint l m := hlm.mono Finset.sdiff_subset Finset.sdiff_subset
  have hlh' : Disjoint l h := hlh.mono Finset.sdiff_subset Finset.sdiff_subset
  have hls' : Disjoint l s := hls.mono Finset.sdiff_subset Finset.sdiff_subset
  have hmh' : Disjoint m h := hmh.mono Finset.sdiff_subset Finset.sdiff_subset
  have hms' : Disjoint m s := hms.mono Finset.sdiff_subset Finset.sdiff_subset
  have hhs' : Disjoint h s := hhs.mono Finset.sdiff_subset Finset.sdiff_subset
  have htotal : l ∪ m ∪ h ∪ s = missingGroup selected Finset.univ := by
    dsimp [l, m, h, s, missingGroup]
    rw [← Finset.union_sdiff_distrib, ← Finset.union_sdiff_distrib,
      ← Finset.union_sdiff_distrib, hpart]
  rw [← htotal, Finset.sum_union (Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hls', hms'⟩, hhs'⟩)]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hlh', hmh'⟩),
    Finset.sum_union hlm']
  have hwlow := sum_group_constant l 2 (fun slot hs ↦ group_weights.1 slot (Finset.mem_sdiff.mp hs).1)
  have hwmed := sum_group_constant m 3 (fun slot hs ↦ group_weights.2.1 slot (Finset.mem_sdiff.mp hs).1)
  have hwhigh := sum_group_constant h 6 (fun slot hs ↦ group_weights.2.2.1 slot (Finset.mem_sdiff.mp hs).1)
  have hwspecial := sum_group_constant s 6 (fun slot hs ↦ group_weights.2.2.2 slot (Finset.mem_sdiff.mp hs).1)
  rw [hwlow, hwmed, hwhigh, hwspecial]

theorem saturation_counts (selected : Fin 198 → Bool)
    (hdisjoint : (↑(selectedSet selected) : Set (Fin 198)).PairwiseDisjoint support)
    (hsize : 41 ≤ (selectedSet selected).card) :
    ((selectedSet selected) ∩ longGroup).card = 3 ∧
      (missingGroup selected specialGroup).card = 0 ∧
      (missingGroup selected mediumGroup).card ≤ 2 ∧
      (missingGroup selected highGroup).card ≤ 1 ∧
      ((missingGroup selected highGroup).card = 0 ∨
        (missingGroup selected mediumGroup).card = 0) := by
  have hweight := missing_weight_bound selected hdisjoint hsize
  rw [missing_weight_decomposition] at hweight
  have hlow : (missingGroup selected lowGroup).card +
      ((coveredSet selected) ∩ lowGroup).card = 22 := by
    simpa only [missingGroup, Finset.inter_comm, group_sizes.1] using
      Finset.card_sdiff_add_card_inter lowGroup (coveredSet selected)
  have hspecial : (missingGroup selected specialGroup).card +
      ((coveredSet selected) ∩ specialGroup).card = 22 := by
    simpa only [missingGroup, Finset.inter_comm, group_sizes.2.2.2.1] using
      Finset.card_sdiff_add_card_inter specialGroup (coveredSet selected)
  rw [covered_low_card selected hdisjoint] at hlow
  rw [covered_special_card selected hdisjoint] at hspecial
  omega

#print axioms saturation_counts

end JSP000404Research.ElevenPhase
