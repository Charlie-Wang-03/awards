import JSP000404Research.BinaryEdgePartition
import JSP000404Research.WeightedOneLayerCharge
import Mathlib.Tactic

/-!
# Weighted profile repair for binary edge partitions

The merged-wrap lower-branch construction naturally produces a
BinaryEdgePartition, not necessarily an OrderedEdgeColoring.

WeightedProfileRepair is independent of the internal certificate type: it
only compares the target exponent profile with the certificate's
free-coordinate profile

  nu(v) = n - card(active(v)).

This file exposes the direct BinaryEdgePartition outlets.

Thus a valid wrap-triangle-free n-colour partition closes JSP-000404 as soon
as either

* total dyadic loss is at most total dyadic surplus, or
* in the one-layer regime, exact loss vertices admit the weighted charging
  certificate of WeightedOneLayerCharge.
-/

namespace JSP000404Research
namespace BinaryEdgePartition

open scoped BigOperators

/-- Aggregate weighted-repair outlet for a binary edge partition. -/
theorem exponent_capacity_of_total_weighted_repair
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : BinaryEdgePartition V n)
    (exponent : V → ℕ)
    (hrepair :
      totalDyadicProfileLoss exponent
          (fun v => n - (active C v).card)
        ≤
      totalDyadicProfileSurplus exponent
          (fun v => n - (active C v).card)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  exact dyadic_capacity_of_total_loss_le_surplus
    exponent
    (fun v => n - (active C v).card)
    (2 ^ n) hrepair C.weighted_capacity

/-- One-layer aggregate weighted-repair outlet. -/
theorem exponent_capacity_of_oneLayer_weighted_repair
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : BinaryEdgePartition V n)
    (exponent : V → ℕ)
    (hone :
      ∀ v,
        exponent v ≤
          (n - (active C v).card) + 1)
    (hrepair :
      oneLayerLossWeight exponent
          (fun v => n - (active C v).card)
        ≤
      oneLayerSurplusCredit exponent
          (fun v => n - (active C v).card)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  exact dyadic_capacity_of_oneLayer_weighted_repair
    exponent
    (fun v => n - (active C v).card)
    (2 ^ n) hone hrepair C.weighted_capacity

/-- Weighted injection form: an exact one-layer loss may be paid by any
distinct surplus centre whose exponent dominates the loss centre's free
coordinate count. -/
theorem exponent_capacity_of_oneLayer_weighted_injection
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : BinaryEdgePartition V n)
    (exponent : V → ℕ)
    (hone :
      ∀ v,
        exponent v ≤
          (n - (active C v).card) + 1)
    (charge : V → V)
    (hmem :
      ∀ v,
        v ∈ oneLayerLossVertices exponent
          (fun w => n - (active C w).card) →
        charge v ∈ oneLayerSurplusVertices exponent
          (fun w => n - (active C w).card))
    (hinj :
      Set.InjOn charge
        (oneLayerLossVertices exponent
          (fun w => n - (active C w).card) : Set V))
    (hweight :
      ∀ v,
        v ∈ oneLayerLossVertices exponent
          (fun w => n - (active C w).card) →
        n - (active C v).card ≤ exponent (charge v)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hprofile :
      (∑ v, 2 ^ exponent v) ≤
        ∑ v, 2 ^ (n - (active C v).card) := by
    exact dyadic_sum_le_of_oneLayer_weighted_injection
      exponent
      (fun v => n - (active C v).card)
      hone charge hmem hinj hweight
  exact hprofile.trans C.weighted_capacity

#print axioms exponent_capacity_of_total_weighted_repair
#print axioms exponent_capacity_of_oneLayer_weighted_repair
#print axioms exponent_capacity_of_oneLayer_weighted_injection

end BinaryEdgePartition
end JSP000404Research
