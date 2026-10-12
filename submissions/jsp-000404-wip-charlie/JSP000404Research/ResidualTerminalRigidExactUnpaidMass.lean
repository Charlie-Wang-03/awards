import JSP000404Research.ResidualTerminalDoubleSaturatedHard
import JSP000404Research.ResidualHardOverlapRigidFaces
import Mathlib.Tactic

/-!
# Exact mass and zero local surplus of the doubly-saturated terminal rigid obstruction

After both mixed-rigid credits are removed, a remaining RIGID
hard overlap word forces BOTH projected profiles saturated. The
upper completion cube is nested in the lower, so the entire rigid
overlap face has cardinality exactly the UPPER target weight.

Neither endpoint offers any dyadic surplus. Additionally the
upper target exponent is at most the lower target exponent.

This is a terminal obstruction characterization, not a global
hole-payment theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The terminal doubly saturated rigid hard face has exact
upper-endpoint target weight, no local endpoint surplus, and
nonincreasing target exponents along the ordered carrier. -/
theorem terminal_rigid_hard_face_exact_upper_weight_zero_surpluses
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool} {p : V × V}
    (hremaining :
      word ∈ remainingUnpaidHardAfterMixedRigidWords C exponent)
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hpword : word ∈ carrierOverlapWords C p) :
    (carrierOverlapWords C p).card = 2 ^ exponent p.2 ∧
    exponent p.2 ≤ exponent p.1 ∧
    dyadicProfileSurplus exponent (projectedFree C) p.1 = 0 ∧
    dyadicProfileSurplus exponent (projectedFree C) p.2 = 0 := by
  obtain ⟨hsatLo, hsatHi⟩ :=
    remaining_rigid_hard_word_both_endpoints_saturated
      C exponent hexp honeLoss hremaining hrigid hpword
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  have hmass :
      (carrierOverlapWords C p).card = 2 ^ projectedFree C p.2 :=
    hard_no_transport_inter_card_eq_projected_cube
      C hsame hrig.2
  have hdim :
      projectedFree C p.2 ≤ projectedFree C p.1 :=
    hard_no_transport_upper_free_le_lower_free C hsame hrig.2
  have hlowzero :
      dyadicProfileSurplus exponent (projectedFree C) p.1 = 0 := by
    unfold dyadicProfileSurplus
    rw [← hsatLo]
    omega
  have hhizero :
      dyadicProfileSurplus exponent (projectedFree C) p.2 = 0 := by
    unfold dyadicProfileSurplus
    rw [← hsatHi]
    omega
  constructor
  · rw [hmass, ← hsatHi]
  constructor
  · omega
  exact ⟨hlowzero,hhizero⟩

#print axioms terminal_rigid_hard_face_exact_upper_weight_zero_surpluses

end OrderedEdgeColoring
end JSP000404Research
