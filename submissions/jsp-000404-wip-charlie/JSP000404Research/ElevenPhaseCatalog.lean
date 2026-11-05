import JSP000404Research.ElevenPhaseMaximal

/-!
# Finite eleven-phase catalog certificates

These statements verify row completion, weighted support, and separation directly in the
kernel. Their scope is the finite row model; no general geometric capacity is assumed.
-/

namespace JSP000404Research.ElevenPhase

open scoped BigOperators

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_weighted_coverage : ∀ i : Fin 198,
    (∑ slot : Fin 132, if covers i slot then slotWeight slot else 0) = 12 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem separated_iff_rows : ∀ i j : Fin 198, Separated i j ↔
    ∃ c a b, row i c = some a ∧ row j c = some b ∧ a ≠ b := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem separated_disjoint_covers : ∀ i j : Fin 198, Separated i j →
    ∀ slot : Fin 132, covers i slot = true → covers j slot = false := by
  decide +kernel

#print axioms catalog_completion
#print axioms catalog_weighted_coverage
#print axioms separated_iff_rows
#print axioms separated_disjoint_covers

end JSP000404Research.ElevenPhase
