import JSP000404Research.ResidualSaturatedHardRemainder
import Mathlib.Tactic

/-!
# Exact shape of unreserved rigid hard-overlap carriers

An unreserved rigid hard carrier with a strictly slack LOWER endpoint
must have equal projected-free dimensions and a saturated UPPER endpoint.
Therefore the target exponent strictly increases from lower to upper.

More generally, every unreserved rigid hard carrier satisfying the
ordinary projected-free endpoint budget is either lower-saturated or
has this precise strict-increase configuration.

These statements use the certified reservation, not an unjustified
global Hall-expansion assertion. They DO NOT pay the remaining overlap,
and they do not close the planar lower-branch conjecture.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- For a rigid hard carrier omitted from the certified global
surplus reservation, strict slack at the lower endpoint forces
EQUAL projected-free dimensions and upper-endpoint saturation. -/
theorem unpaid_rigid_strict_lower_forces_equal_free_upper_sat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hlo : exponent p.1 < projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    projectedFree C p.1 = projectedFree C p.2 ∧
      exponent p.2 = projectedFree C p.2 := by
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hhard : p ∈ hardOverlapCarrierPairs C := hrig.1
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hhard).2
  have hfreeLe : projectedFree C p.2 ≤ projectedFree C p.1 :=
    hard_no_transport_upper_free_le_lower_free C hsame hrig.2
  have hnotSmaller : ¬ projectedFree C p.2 < projectedFree C p.1 := by
    intro hsmaller
    apply hnot
    exact (mem_surplusPayableHardCarrierPairs C exponent p).2
      ⟨hhard, Or.inr ⟨hrigid, hsmaller, hlo⟩⟩
  have hequal : projectedFree C p.1 = projectedFree C p.2 := by
    omega
  have hnotUpperStrict : ¬ exponent p.2 < projectedFree C p.2 := by
    intro hhi
    apply hnot
    exact (mem_surplusPayableHardCarrierPairs C exponent p).2
      ⟨hhard, Or.inl ⟨hlo, hhi⟩⟩
  exact ⟨hequal, by omega⟩

/-- The exact rigid obstruction is either saturation at the lower
endpoint, or a projected-dimension equality with saturation and
strict target-exponent ascent at the upper endpoint. -/
theorem unpaid_rigid_carrier_saturation_or_exponent_ascent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hloBudget : exponent p.1 ≤ projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    exponent p.1 = projectedFree C p.1 ∨
      (projectedFree C p.1 = projectedFree C p.2 ∧
       exponent p.2 = projectedFree C p.2 ∧
       exponent p.1 < exponent p.2) := by
  by_cases hlo : exponent p.1 < projectedFree C p.1
  · right
    obtain ⟨hequal, hsat⟩ :=
      unpaid_rigid_strict_lower_forces_equal_free_upper_sat
        C exponent hrigid hnot hlo hhiBudget
    exact ⟨hequal, hsat, by omega⟩
  · left
    omega

#print axioms unpaid_rigid_strict_lower_forces_equal_free_upper_sat
#print axioms unpaid_rigid_carrier_saturation_or_exponent_ascent

end OrderedEdgeColoring
end JSP000404Research
