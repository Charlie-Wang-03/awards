import JSP000404Research.ElevenPhaseCNFSemantics
import JSP000404Research.ElevenPhaseSequential
import JSP000404Research.ElevenPhaseValuation

/-!
# Applying the LRAT certificate to a Boolean family of catalog rows

The remaining numeric hypotheses will be derived from the exact disjoint weighted cover.
-/

namespace JSP000404Research.ElevenPhase

set_option maxRecDepth 16384 in
theorem longRows_bounded : ∀ i : Fin 22, longRows i < 198 := by decide +kernel

theorem longIndex_bounded (i : ℕ) : longIndex i < 198 := by
  exact longRows_bounded ⟨i % 22, Nat.mod_lt _ (by decide)⟩

theorem coverers_bounded {slot n : ℕ} (hn : n ∈ coverers slot) : n < 198 := by
  unfold coverers at hn
  exact List.mem_range.mp (List.mem_filter.mp hn).1

set_option maxRecDepth 16384 in
theorem obstructionSets_bounded :
    obstructionSets.all (fun core ↦ core.all (fun n ↦ n < 198)) = true := by decide +kernel

theorem obstruction_mem_bounded {core : List ℕ} (hc : core ∈ obstructionSets)
    {n : ℕ} (hn : n ∈ core) : n < 198 := by
  have hall := (List.all_eq_true.mp obstructionSets_bounded) core hc
  exact of_decide_eq_true ((List.all_eq_true.mp hall) n hn)

def longSelected (selected : Fin 198 → Bool) : Finset ℕ :=
  (Finset.range 22).filter fun i ↦ chosenLong selected i

theorem longSelected_card (selected : Fin 198 → Bool) :
    (longSelected selected).card = prefixCount (chosenLong selected) 22 := by
  simp [longSelected, prefixCount]

theorem long_three_distinct (selected : Fin 198 → Bool)
    (hthree : 3 ≤ prefixCount (chosenLong selected) 22)
    {i j : ℕ} (hi : i < 22) (hj : j < 22) :
    ∃ k, k < 22 ∧ k ≠ i ∧ k ≠ j ∧ chosenLong selected k = true := by
  classical
  by_contra hn
  have hsubset : longSelected selected ⊆ ({i, j} : Finset ℕ) := by
    intro k hk
    have ⟨hkrange, hkchosen⟩ := Finset.mem_filter.mp hk
    have hklt : k < 22 := Finset.mem_range.mp hkrange
    by_cases hki : k = i
    · simp [hki]
    by_cases hkj : k = j
    · simp [hkj]
    have htrue : chosenLong selected k = true := by simpa using hkchosen
    exact False.elim (hn ⟨k, hklt, hki, hkj, htrue⟩)
  have hle := Finset.card_le_card hsubset
  have hpair : ({i, j} : Finset ℕ).card ≤ 2 := by
    simpa using Finset.card_insert_le i ({j} : Finset ℕ)
  rw [longSelected_card] at hle
  omega

theorem selected_long_counter_satisfied (selected : Fin 198 → Bool)
    (hbound : prefixCount (chosenLong selected) 22 ≤ 3) :
    (packingValuation selected).satisfies_fmla (sequentialClauses longIndex 198 22 3) := by
  apply sequentialClauses_satisfied (packingValuation selected) (chosenLong selected)
    longIndex 198 22 3 (by decide)
  · intro i hi
    simpa [chosenLong] using packingValuation_row selected (longIndex_bounded i)
  · intro i j hi hj
    simpa using packingValuation_long_counter selected hi hj
  · exact hbound

theorem missing_medium_counter_satisfied (selected : Fin 198 → Bool)
    (hbound : prefixCount (missingBit selected) 66 ≤ 2) :
    (packingValuation selected).satisfies_fmla
      (sequentialClauses (fun i ↦ 286 + i) 374 66 2) := by
  apply sequentialClauses_satisfied (packingValuation selected) (missingBit selected)
    (fun i ↦ 286 + i) 374 66 2 (by decide)
  · intro i hi
    exact packingValuation_missing selected (by omega)
  · intro i j hi hj
    simpa using packingValuation_medium_counter selected hi hj
  · exact hbound

theorem missing_high_counter_satisfied (selected : Fin 198 → Bool)
    (hbound : prefixCount (fun i ↦ missingBit selected (66 + i)) 22 ≤ 1) :
    (packingValuation selected).satisfies_fmla
      (sequentialClauses (fun i ↦ 286 + 66 + i) 572 22 1) := by
  apply sequentialClauses_satisfied (packingValuation selected)
    (fun i ↦ missingBit selected (66 + i)) (fun i ↦ 286 + 66 + i) 572 22 1 (by decide)
  · intro i hi
    have h := packingValuation_missing selected (show 66 + i < 88 by omega)
    have heq : 286 + (66 + i) = 286 + 66 + i := by omega
    rw [heq] at h
    exact h
  · intro i j hi hj
    simpa using packingValuation_high_counter selected hi hj
  · exact hbound

theorem packing_contradiction_of_counts (selected : Fin 198 → Bool)
    (hconflict : ∀ i j, i < 198 → j < 198 → i < j →
      ¬Separated (rowIndex i) (rowIndex j) →
        ¬(selected (rowIndex i) = true ∧ selected (rowIndex j) = true))
    (hcore : ∀ core ∈ obstructionSets, ¬∀ i ∈ core, selected (rowIndex i) = true)
    (hhigh : ∀ i, i < 22 → ∃ n ∈ coverers (high341Slot i), selected (rowIndex n) = true)
    (hlong : prefixCount (chosenLong selected) 22 = 3)
    (hmedium : prefixCount (missingBit selected) 66 ≤ 2)
    (hhighMissing : prefixCount (fun i ↦ missingBit selected (66 + i)) 22 ≤ 1)
    (hcross : ∀ h m, h < 22 → m < 66 →
      missingBit selected (66 + h) = true → missingBit selected m ≠ true) : False := by
  let v := packingValuation selected
  apply packing_contradiction v
  · intro i j hi hj hij hsep ⟨hvi, hvj⟩
    exact hconflict i j hi hj hij hsep
      ⟨(packingValuation_row selected hi).mp hvi, (packingValuation_row selected hj).mp hvj⟩
  · intro core hc hall
    apply hcore core hc
    intro i hi
    exact (packingValuation_row selected (obstruction_mem_bounded hc hi)).mp (hall i hi)
  · intro i hi
    obtain ⟨n, hn, hv⟩ := hhigh i hi
    exact ⟨n, hn, (packingValuation_row selected (coverers_bounded hn)).mpr hv⟩
  · intro i j hi hj hij
    obtain ⟨k, hk, hki, hkj, hv⟩ := long_three_distinct selected (by omega) hi hj
    exact ⟨k, hk, hki, hkj,
      (packingValuation_row selected (longIndex_bounded k)).mpr hv⟩
  · intro i hi
    by_cases h : ∃ row : Fin 198, selected row = true ∧
        covers row (slotIndex (missingSlot i)) = true
    · obtain ⟨row, hr, hcover⟩ := h
      right
      refine ⟨row.val, ?_, ?_⟩
      · unfold coverers
        apply List.mem_filter.mpr
        constructor
        · exact List.mem_range.mpr row.isLt
        · simpa [rowIndex, Nat.mod_eq_of_lt row.isLt] using hcover
      · apply (packingValuation_row selected row.isLt).mpr
        simpa [rowIndex, Nat.mod_eq_of_lt row.isLt] using hr
    · left
      apply (packingValuation_missing selected hi).mpr
      simp [missingBit, h]
  · exact selected_long_counter_satisfied selected (by omega)
  · exact missing_medium_counter_satisfied selected hmedium
  · exact missing_high_counter_satisfied selected hhighMissing
  · intro h m hh hm hvh
    have h1 := (packingValuation_missing selected (show 66 + h < 88 by omega)).mp (by
      have heq : 286 + (66 + h) = 286 + 66 + h := by omega
      rw [heq]
      exact hvh)
    intro hvm
    have h2 := (packingValuation_missing selected (show m < 88 by omega)).mp hvm
    exact hcross h m hh hm h1 h2

#print axioms packing_contradiction_of_counts

end JSP000404Research.ElevenPhase
