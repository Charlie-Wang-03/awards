import JSP000404Research.ResidualUnpaidRigidNetPaymentReduction
import Mathlib.Tactic

/-!
# Descending rigid hard carriers: exact upper-surplus credit

For a rigid hard-overlap pair (a,v) with saturated LOWER vertex
and strictly slack UPPER vertex, the whole intersection is Q_v.
Thus the upper surplus can be charged against the face, leaving
exactly the UPPER target mass 2^k(v). The lower surplus is zero.

This local result does not assume the sought planar payment inequality.
It supplies the missing symmetric half of the previously certified
ascending-rigid partial reservation.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- Exact unpaid mass of an upper-strict rigid pair: its whole
overlap equals upper dyadic surplus plus upper target mass. -/
theorem rigid_saturated_lower_strict_upper_exact_debt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hloSat : exponent p.1 = projectedFree C p.1)
    (hhiStrict : exponent p.2 < projectedFree C p.2) :
    (carrierOverlapWords C p).card =
      dyadicProfileSurplus exponent (projectedFree C) p.2 +
        2 ^ exponent p.2 := by
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  have hmass :
      (carrierOverlapWords C p).card =
        2 ^ projectedFree C p.2 :=
    hard_no_transport_inter_card_eq_projected_cube
      C hsame hrig.2
  have hpow :
      2 ^ exponent p.2 ≤ 2 ^ projectedFree C p.2 :=
    Nat.pow_le_pow_right
      (by norm_num : (0 : ℕ) < 2) (Nat.le_of_lt hhiStrict)
  rw [hmass]
  unfold dyadicProfileSurplus
  omega

/-- A lower-saturated upper-strict rigid pair carries a strictly
positive residual target debt after spending its own surpluses. -/
theorem rigid_saturated_lower_strict_upper_not_fully_surplus_paid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hloSat : exponent p.1 = projectedFree C p.1)
    (hhiStrict : exponent p.2 < projectedFree C p.2) :
    ¬ ((carrierOverlapWords C p).card ≤
      dyadicProfileSurplus exponent (projectedFree C) p.1 +
        dyadicProfileSurplus exponent (projectedFree C) p.2) := by
  have hexact :=
    rigid_saturated_lower_strict_upper_exact_debt
      C exponent hrigid hloSat hhiStrict
  have hlowZero :
      dyadicProfileSurplus exponent (projectedFree C) p.1 = 0 := by
    unfold dyadicProfileSurplus
    rw [← hloSat]
    omega
  have hpositive : 0 < 2 ^ exponent p.2 :=
    pow_pos (by norm_num : (0 : ℕ) < 2) _
  omega

/-- The disjoint, previously UNPAID, descending mixed-rigid class.
The lower endpoint is saturated and the upper is strict. -/
noncomputable def descendingUnpaidRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (rigidHardOverlapCarrierPairs C).filter (fun p =>
    p ∉ surplusPayableHardCarrierPairs C exponent ∧
    exponent p.1 = projectedFree C p.1 ∧
    exponent p.2 < projectedFree C p.2)

@[simp] theorem mem_descendingUnpaidRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ descendingUnpaidRigidCarriers C exponent ↔
      p ∈ rigidHardOverlapCarrierPairs C ∧
      p ∉ surplusPayableHardCarrierPairs C exponent ∧
      exponent p.1 = projectedFree C p.1 ∧
      exponent p.2 < projectedFree C p.2 := by
  classical
  simp [descendingUnpaidRigidCarriers]

/-- No upper-strict, lower-saturated carrier can belong to the
ascending-rigid class, or the earlier full-face paid family. -/
theorem descendingRigid_disjoint_paid_and_ascending
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (descendingUnpaidRigidCarriers C exponent)
      (surplusPayableHardCarrierPairs C exponent) ∧
    Disjoint (descendingUnpaidRigidCarriers C exponent)
      (ascendingUnpaidRigidCarriers C exponent) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hd hp
    exact ((mem_descendingUnpaidRigidCarriers C exponent p).1 hd).2.1 hp
  · apply Finset.disjoint_left.mpr
    intro p hd ha
    have hsat :=
      ((mem_descendingUnpaidRigidCarriers C exponent p).1 hd).2.2.1
    have hstrict :=
      ((mem_ascendingUnpaidRigidCarriers C exponent p).1 ha).2.2.1
    omega

/-- Exact local budget identity aggregated over the descending
rigid family: all but the upper target masses is upper surplus. -/
theorem descending_rigid_mass_eq_partial_credit_add_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
      (carrierOverlapWords C p).card) =
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
        dyadicProfileSurplus exponent (projectedFree C) p.2) +
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
        2 ^ exponent p.2) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have h := (mem_descendingUnpaidRigidCarriers C exponent p).1 hp
  exact rigid_saturated_lower_strict_upper_exact_debt
    C exponent h.1 h.2.2.1 h.2.2.2

#print axioms rigid_saturated_lower_strict_upper_exact_debt
#print axioms rigid_saturated_lower_strict_upper_not_fully_surplus_paid
#print axioms descendingRigid_disjoint_paid_and_ascending
#print axioms descending_rigid_mass_eq_partial_credit_add_target

end OrderedEdgeColoring
end JSP000404Research
