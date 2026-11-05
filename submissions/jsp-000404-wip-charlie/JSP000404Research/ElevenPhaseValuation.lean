import JSP000404Research.ElevenPhaseCNFModel
import JSP000404Research.ElevenPhaseSATHelpers

/-! Interpret the auxiliary CNF variables by actual finite row and slot counts. -/

namespace JSP000404Research.ElevenPhase

def chosenLong (selected : Fin 198 → Bool) (i : ℕ) : Bool :=
  selected (rowIndex (longIndex i))

def missingBit (selected : Fin 198 → Bool) (i : ℕ) : Bool :=
  !decide (∃ row : Fin 198, selected row = true ∧ covers row (slotIndex (missingSlot i)) = true)

def packingValuation (selected : Fin 198 → Bool) : Sat.Valuation := fun n ↦
  if n < 198 then selected (rowIndex n) = true
  else if n < 286 then
    (n - 198) % 4 + 1 ≤ prefixCount (chosenLong selected) ((n - 198) / 4 + 1)
  else if n < 374 then missingBit selected (n - 286) = true
  else if n < 572 then
    (n - 374) % 3 + 1 ≤ prefixCount (missingBit selected) ((n - 374) / 3 + 1)
  else if n < 616 then
    (n - 572) % 2 + 1 ≤ prefixCount (fun i ↦ missingBit selected (66 + i)) ((n - 572) / 2 + 1)
  else False

theorem packingValuation_row (selected : Fin 198 → Bool) {i : ℕ} (hi : i < 198) :
    packingValuation selected i ↔ selected (rowIndex i) = true := by
  simp [packingValuation, hi]

theorem packingValuation_long_counter (selected : Fin 198 → Bool) {i j : ℕ}
    (hi : i < 22) (hj : j ≤ 3) :
    packingValuation selected (198 + i * 4 + j) ↔
      j + 1 ≤ prefixCount (chosenLong selected) (i + 1) := by
  have h1 : ¬198 + i * 4 + j < 198 := by omega
  have h2 : 198 + i * 4 + j < 286 := by omega
  have hdiv : (198 + i * 4 + j - 198) / 4 = i := by omega
  have hmod : (198 + i * 4 + j - 198) % 4 = j := by omega
  simp [packingValuation, h1, h2, hdiv, hmod]

theorem packingValuation_missing (selected : Fin 198 → Bool) {i : ℕ} (hi : i < 88) :
    packingValuation selected (286 + i) ↔ missingBit selected i = true := by
  have h1 : ¬286 + i < 198 := by omega
  have h2 : ¬286 + i < 286 := by omega
  have h3 : 286 + i < 374 := by omega
  simp [packingValuation, h1, h2, h3]

theorem packingValuation_medium_counter (selected : Fin 198 → Bool) {i j : ℕ}
    (hi : i < 66) (hj : j ≤ 2) :
    packingValuation selected (374 + i * 3 + j) ↔
      j + 1 ≤ prefixCount (missingBit selected) (i + 1) := by
  have h1 : ¬374 + i * 3 + j < 198 := by omega
  have h2 : ¬374 + i * 3 + j < 286 := by omega
  have h3 : ¬374 + i * 3 + j < 374 := by omega
  have h4 : 374 + i * 3 + j < 572 := by omega
  have hdiv : (374 + i * 3 + j - 374) / 3 = i := by omega
  have hmod : (374 + i * 3 + j - 374) % 3 = j := by omega
  simp [packingValuation, h1, h2, h3, h4, hdiv, hmod]

theorem packingValuation_high_counter (selected : Fin 198 → Bool) {i j : ℕ}
    (hi : i < 22) (hj : j ≤ 1) :
    packingValuation selected (572 + i * 2 + j) ↔
      j + 1 ≤ prefixCount (fun k ↦ missingBit selected (66 + k)) (i + 1) := by
  have h1 : ¬572 + i * 2 + j < 198 := by omega
  have h2 : ¬572 + i * 2 + j < 286 := by omega
  have h3 : ¬572 + i * 2 + j < 374 := by omega
  have h4 : ¬572 + i * 2 + j < 572 := by omega
  have h5 : 572 + i * 2 + j < 616 := by omega
  have hdiv : (572 + i * 2 + j - 572) / 2 = i := by omega
  have hmod : (572 + i * 2 + j - 572) % 2 = j := by omega
  simp [packingValuation, h1, h2, h3, h4, h5, hdiv, hmod]

#print axioms packingValuation_long_counter
#print axioms packingValuation_medium_counter
#print axioms packingValuation_high_counter

end JSP000404Research.ElevenPhase
