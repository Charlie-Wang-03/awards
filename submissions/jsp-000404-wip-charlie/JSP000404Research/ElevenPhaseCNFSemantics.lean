import JSP000404Research.ElevenPhaseCNFModel
import JSP000404Research.ElevenPhaseSATHelpers

/-!
# Interpreting the checked eleven-phase propositional certificate

These hypotheses describe the exact semantic content of the CNF clauses. Their derivation
from a separated coherent row family and a cardinality assumption is a separate step.
-/

namespace JSP000404Research.ElevenPhase

theorem conflictClauses_satisfied (v : Sat.Valuation)
    (hconflict : ∀ i j, i < 198 → j < 198 → i < j →
      ¬Separated (rowIndex i) (rowIndex j) → ¬(v i ∧ v j)) :
    v.satisfies_fmla conflictClauses := by
  classical
  constructor
  intro clause hc
  unfold conflictClauses at hc
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hi : i < 198 := List.mem_range.mp hi
  obtain ⟨hj, hijsep⟩ := List.mem_filter.mp hj
  have hj : j < 198 := List.mem_range.mp hj
  have ⟨hij, hsep⟩ : i < j ∧ ¬Separated (rowIndex i) (rowIndex j) := by simpa using hijsep
  have h := hconflict i j hi hj hij hsep
  by_cases hvi : v i
  · apply satisfies_neg_member v _ j (by simp [negative])
    intro hvj
    exact h ⟨hvi, hvj⟩
  · exact satisfies_neg_member v _ i (by simp [negative]) hvi

theorem coreClauses_satisfied (v : Sat.Valuation)
    (hcore : ∀ core ∈ obstructionSets, ¬∀ i ∈ core, v i) :
    v.satisfies_fmla coreClauses := by
  constructor
  intro clause hc
  unfold coreClauses at hc
  obtain ⟨core, hmem, rfl⟩ := List.mem_map.mp hc
  exact satisfies_mapped_negative v core (hcore core hmem)

theorem high341Clauses_satisfied (v : Sat.Valuation)
    (hhigh : ∀ i, i < 22 → ∃ n ∈ coverers (high341Slot i), v n) :
    v.satisfies_fmla high341Clauses := by
  constructor
  intro clause hc
  unfold high341Clauses at hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact satisfies_mapped_positive v _ (hhigh i (List.mem_range.mp hi))

theorem longAtLeastThreeClauses_satisfied (v : Sat.Valuation)
    (hlong : ∀ i j, i < 22 → j < 22 → i < j →
      ∃ k, k < 22 ∧ k ≠ i ∧ k ≠ j ∧ v (longIndex k)) :
    v.satisfies_fmla longAtLeastThreeClauses := by
  constructor
  intro clause hc
  unfold longAtLeastThreeClauses at hc
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hi : i < 22 := List.mem_range.mp hi
  obtain ⟨hj, hij⟩ := List.mem_filter.mp hj
  have hj : j < 22 := List.mem_range.mp hj
  have hij : i < j := by simpa using hij
  obtain ⟨k, hk, hki, hkj, hv⟩ := hlong i j hi hj hij
  apply satisfies_pos_member v _ (longIndex k) _ hv
  apply List.mem_map.mpr
  refine ⟨k, ?_, rfl⟩
  simp [hk, hki, hkj, positive]

theorem missingClauses_satisfied (v : Sat.Valuation)
    (hmissing : ∀ i, i < 88 → v (286 + i) ∨ ∃ n ∈ coverers (missingSlot i), v n) :
    v.satisfies_fmla missingClauses := by
  constructor
  intro clause hc
  unfold missingClauses at hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi : i < 88 := List.mem_range.mp hi
  rcases hmissing i hi with hm | ⟨n, hn, hv⟩
  · apply satisfies_pos_member v _ (286 + i) _ hm
    exact List.Mem.head _
  · apply satisfies_pos_member v _ n _ hv
    apply List.Mem.tail
    unfold coveredClause
    apply List.mem_map.mpr
    exact ⟨n, hn, rfl⟩

theorem crossClauses_satisfied (v : Sat.Valuation)
    (hcross : ∀ h m, h < 22 → m < 66 → v (286 + 66 + h) → ¬v (286 + m)) :
    v.satisfies_fmla crossClauses := by
  constructor
  intro clause hc
  unfold crossClauses at hc
  obtain ⟨h, hh, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc
  have hh : h < 22 := List.mem_range.mp hh
  have hm : m < 66 := List.mem_range.mp hm
  by_cases hv : v (286 + 66 + h)
  · exact satisfies_neg_member v _ (286 + m) (by simp [negative]) (hcross h m hh hm hv)
  · exact satisfies_neg_member v _ (286 + 66 + h) (by simp [negative]) hv

set_option maxRecDepth 65536 in
theorem packing_contradiction (v : Sat.Valuation)
    (hconflict : ∀ i j, i < 198 → j < 198 → i < j →
      ¬Separated (rowIndex i) (rowIndex j) → ¬(v i ∧ v j))
    (hcore : ∀ core ∈ obstructionSets, ¬∀ i ∈ core, v i)
    (hhigh : ∀ i, i < 22 → ∃ n ∈ coverers (high341Slot i), v n)
    (hlong : ∀ i j, i < 22 → j < 22 → i < j →
      ∃ k, k < 22 ∧ k ≠ i ∧ k ≠ j ∧ v (longIndex k))
    (hmissing : ∀ i, i < 88 → v (286 + i) ∨ ∃ n ∈ coverers (missingSlot i), v n)
    (hlongSeq : v.satisfies_fmla (sequentialClauses longIndex 198 22 3))
    (hmediumSeq : v.satisfies_fmla (sequentialClauses (fun i ↦ 286 + i) 374 66 2))
    (hhighSeq : v.satisfies_fmla (sequentialClauses (fun i ↦ 286 + 66 + i) 572 22 1))
    (hcross : ∀ h m, h < 22 → m < 66 → v (286 + 66 + h) → ¬v (286 + m)) : False := by
  have hmodel : v.satisfies_fmla modelFormula := by
    have h1 := satisfies_append v (conflictClauses_satisfied v hconflict)
      (coreClauses_satisfied v hcore)
    have h2 := satisfies_append v h1 (high341Clauses_satisfied v hhigh)
    have h3 := satisfies_append v h2 (longAtLeastThreeClauses_satisfied v hlong)
    have h4 := satisfies_append v h3 hlongSeq
    have h5 := satisfies_append v h4 (missingClauses_satisfied v hmissing)
    have h6 := satisfies_append v h5 hmediumSeq
    have h7 := satisfies_append v h6 hhighSeq
    exact satisfies_append v h7 (crossClauses_satisfied v hcross)
  exact packing_refutation v (modelFormula_eq ▸ hmodel)

#print axioms packing_contradiction

end JSP000404Research.ElevenPhase
