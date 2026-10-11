import JSP000404Research.ResidualUnpaidRigidSaturation
import Mathlib.Tactic

/-!
# Exact uncompensated mass of an ascending unreserved rigid carrier

The previously certified classification says that an unreserved
rigid hard carrier whose lower endpoint is projected-strict
has equal projected-free dimensions and a saturated upper endpoint.

In fact its two retained Boolean completion cubes coincide.
The entire overlap face therefore has mass 2^nu, whereas the
two local dyadic surpluses sum to 2^nu - 2^k(lower).

Consequently its EXACT unpaid local deficit is 2^k(lower),
which is strictly positive. No pairing of the two endpoint
surpluses can pay it. A global argument must exploit other
vertices, actual Boolean holes, or planar geometry.

This module makes no unproved global payment assumption.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An unreserved rigid hard pair with a strict lower endpoint
has two IDENTICAL retained completion cubes. -/
theorem unpaid_rigid_strict_lower_completion_cubes_equal
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hlo : exponent p.1 < projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    retainedCompletionWords C p.1 =
      retainedCompletionWords C p.2 := by
  classical
  obtain ⟨hequal, _⟩ :=
    unpaid_rigid_strict_lower_forces_equal_free_upper_sat
      C exponent hrigid hnot hlo hhiBudget
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  have hsubset :
      retainedCompletionWords C p.2 ⊆
        retainedCompletionWords C p.1 :=
    hard_no_transport_upper_cube_subset_lower C hsame hrig.2
  have hcardEq :
      (retainedCompletionWords C p.1).card =
        (retainedCompletionWords C p.2).card := by
    calc
      (retainedCompletionWords C p.1).card =
          2 ^ projectedFree C p.1 := retainedCompletionWords_card C p.1
      _ = 2 ^ projectedFree C p.2 :=
        congrArg (fun k : ℕ => 2 ^ k) hequal
      _ = (retainedCompletionWords C p.2).card :=
        (retainedCompletionWords_card C p.2).symm
  exact (Finset.eq_of_subset_of_card_le hsubset
    (Nat.le_of_eq hcardEq)).symm

/-- The WHOLE hard overlap face is exactly the lower endpoint's
surplus plus the lower endpoint's target weight. The upper
endpoint is saturated, hence contributes zero profile surplus. -/
theorem unpaid_rigid_strict_lower_exact_overlap_debt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hlo : exponent p.1 < projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    (carrierOverlapWords C p).card =
      dyadicProfileSurplus exponent (projectedFree C) p.1 +
        dyadicProfileSurplus exponent (projectedFree C) p.2 +
          2 ^ exponent p.1 := by
  obtain ⟨hequal, hhiSat⟩ :=
    unpaid_rigid_strict_lower_forces_equal_free_upper_sat
      C exponent hrigid hnot hlo hhiBudget
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  have hmass :
      (carrierOverlapWords C p).card =
        2 ^ projectedFree C p.2 := by
    exact hard_no_transport_inter_card_eq_projected_cube
      C hsame hrig.2
  have hpow :
      2 ^ exponent p.1 ≤ 2 ^ projectedFree C p.1 :=
    Nat.pow_le_pow_right
      (by norm_num : (0 : ℕ) < 2) (Nat.le_of_lt hlo)
  have hzero :
      dyadicProfileSurplus exponent (projectedFree C) p.2 = 0 := by
    unfold dyadicProfileSurplus
    rw [hhiSat]
    omega
  have hsum :
      dyadicProfileSurplus exponent (projectedFree C) p.1 +
        2 ^ exponent p.1 = 2 ^ projectedFree C p.1 := by
    unfold dyadicProfileSurplus
    omega
  calc
    (carrierOverlapWords C p).card =
        2 ^ projectedFree C p.2 := hmass
    _ = 2 ^ projectedFree C p.1 := by rw [hequal]
    _ = dyadicProfileSurplus exponent (projectedFree C) p.1 +
          dyadicProfileSurplus exponent (projectedFree C) p.2 +
            2 ^ exponent p.1 := by
      rw [hzero]
      omega

/-- An ascending unreserved rigid carrier cannot be paid by
the sum of its OWN two endpoint surplus budgets. -/
theorem unpaid_rigid_strict_lower_not_pair_surplus_payable
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hlo : exponent p.1 < projectedFree C p.1)
    (hhiBudget : exponent p.2 ≤ projectedFree C p.2) :
    ¬ ((carrierOverlapWords C p).card ≤
      dyadicProfileSurplus exponent (projectedFree C) p.1 +
        dyadicProfileSurplus exponent (projectedFree C) p.2) := by
  have hexact :=
    unpaid_rigid_strict_lower_exact_overlap_debt
      C exponent hrigid hnot hlo hhiBudget
  have hpositive : 0 < 2 ^ exponent p.1 :=
    pow_pos (by norm_num : (0 : ℕ) < 2) _
  omega

#print axioms unpaid_rigid_strict_lower_completion_cubes_equal
#print axioms unpaid_rigid_strict_lower_exact_overlap_debt
#print axioms unpaid_rigid_strict_lower_not_pair_surplus_payable

end OrderedEdgeColoring
end JSP000404Research
