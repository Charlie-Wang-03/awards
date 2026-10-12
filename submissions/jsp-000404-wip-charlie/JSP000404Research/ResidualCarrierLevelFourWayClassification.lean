import JSP000404Research.ResidualTerminalRigidExactUnpaidMass
import Mathlib.Tactic

/-!
# Carrier-level exhausted hard overlap classification (no word witness)

The prior terminal structural theorem was word-level: given a
Boolean overlap word belonging to a rigid carrier, both endpoints
were saturated after full- and partial-payment exclusions.

This module proves a strictly simpler and stronger CARRIER-level
four-way decomposition, from the two endpoint projected budgets alone:

  1. outward/inactive transportable hard carrier,
  2. unpayable ascending mixed rigid carrier (lower strictly slack),
  3. unpayable descending mixed rigid carrier (upper strictly slack),
  4. doubly saturated rigid carrier.

This does NOT depend on choosing any shared Boolean word or on any
global planar Hall or payment hypothesis. In the terminal fourth
case the exact overlap face mass is the upper target weight and
both endpoint surplus amounts vanish.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every genuinely unpayable rigid hard carrier, under the
ordinary endpoint profile budgets, lies in one of exactly three
accounting classes: ascending mixed, descending mixed, or
both endpoints saturated. -/
theorem unpayable_rigid_carrier_ascending_descending_or_double_sat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hloBudget : exponent p.1 ≤ projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    p ∈ ascendingUnpaidRigidCarriers C exponent ∨
      p ∈ descendingUnpaidRigidCarriers C exponent ∨
      (exponent p.1 = projectedFree C p.1 ∧
        exponent p.2 = projectedFree C p.2) := by
  by_cases hloStrict : exponent p.1 < projectedFree C p.1
  · left
    exact (mem_ascendingUnpaidRigidCarriers C exponent p).2
      ⟨hrigid,hnot,hloStrict,hhiBudget⟩
  · have hloSat : exponent p.1 = projectedFree C p.1 := by
      omega
    by_cases hhiStrict : exponent p.2 < projectedFree C p.2
    · right
      left
      exact (mem_descendingUnpaidRigidCarriers C exponent p).2
        ⟨hrigid,hnot,hloSat,hhiStrict⟩
    · right
      right
      exact ⟨hloSat,by omega⟩

/-- The full carrier-level FOUR-WAY classification includes the
unconditionally transportable hard carrier case. -/
theorem unpayable_hard_carrier_transport_or_two_mixed_or_double_sat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hhard : p ∈ hardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hloBudget : exponent p.1 ≤ projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    HasOutgoingHardTransport C p.1 p.2 ∨
      p ∈ ascendingUnpaidRigidCarriers C exponent ∨
      p ∈ descendingUnpaidRigidCarriers C exponent ∨
      (p ∈ rigidHardOverlapCarrierPairs C ∧
        exponent p.1 = projectedFree C p.1 ∧
        exponent p.2 = projectedFree C p.2) := by
  by_cases htrans : HasOutgoingHardTransport C p.1 p.2
  · exact Or.inl htrans
  · have hr : p ∈ rigidHardOverlapCarrierPairs C :=
      (mem_rigidHardOverlapCarrierPairs C p).2 ⟨hhard,htrans⟩
    rcases unpayable_rigid_carrier_ascending_descending_or_double_sat
      C exponent hr hnot hloBudget hhiBudget
      with ha | hb | ⟨hsatLo,hsatHi⟩
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr ⟨hr,hsatLo,hsatHi⟩))

/-- Beyond the already credited ascending and descending
classes, every genuinely unpayable rigid hard carrier has TWO
saturated endpoints, even without a chosen overlap word. -/
theorem terminal_rigid_carrier_both_saturated_without_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hnotA : p ∉ ascendingUnpaidRigidCarriers C exponent)
    (hnotB : p ∉ descendingUnpaidRigidCarriers C exponent)
    (hloBudget : exponent p.1 ≤ projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    exponent p.1 = projectedFree C p.1 ∧
      exponent p.2 = projectedFree C p.2 := by
  rcases unpayable_rigid_carrier_ascending_descending_or_double_sat
    C exponent hrigid hnot hloBudget hhiBudget with ha | hb | hsat
  · exact (hnotA ha).elim
  · exact (hnotB hb).elim
  · exact hsat

/-- The terminal doubly saturated rigid face has mass equal to
its upper target exponent even at CARRIER LEVEL, without
selecting an actual shared word. -/
theorem terminal_rigid_carrier_mass_and_zero_surplus_without_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hnotA : p ∉ ascendingUnpaidRigidCarriers C exponent)
    (hnotB : p ∉ descendingUnpaidRigidCarriers C exponent)
    (hloBudget : exponent p.1 ≤ projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    (carrierOverlapWords C p).card = 2 ^ exponent p.2 ∧
    exponent p.2 ≤ exponent p.1 ∧
    dyadicProfileSurplus exponent (projectedFree C) p.1 = 0 ∧
    dyadicProfileSurplus exponent (projectedFree C) p.2 = 0 := by
  obtain ⟨hsatLo,hsatHi⟩ :=
    terminal_rigid_carrier_both_saturated_without_word
      C exponent hrigid hnot hnotA hnotB hloBudget hhiBudget
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  have hmass :
      (carrierOverlapWords C p).card = 2 ^ projectedFree C p.2 := by
    simpa only [carrierOverlapWords] using
      hard_no_transport_inter_card_eq_projected_cube C hsame hrig.2
  have hdim :=
    hard_no_transport_upper_free_le_lower_free C hsame hrig.2
  have hlozero :
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
  exact ⟨hlozero,hhizero⟩

#print axioms unpayable_rigid_carrier_ascending_descending_or_double_sat
#print axioms unpayable_hard_carrier_transport_or_two_mixed_or_double_sat
#print axioms terminal_rigid_carrier_both_saturated_without_word
#print axioms terminal_rigid_carrier_mass_and_zero_surplus_without_word

end OrderedEdgeColoring
end JSP000404Research
