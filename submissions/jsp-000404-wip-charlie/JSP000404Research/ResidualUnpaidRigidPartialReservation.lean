import JSP000404Research.ResidualUnpaidRigidExactDebt
import JSP000404Research.ResidualAllHardPaidDefectReduction
import Mathlib.Tactic

/-!
# Globally reserve partial surplus of ascending unpaid rigid carriers

The earlier whole-face reservation pays every hard carrier whose full
overlap intersection can be covered by two endpoint surpluses. The
remaining rigid carriers with STRICT lower profile have identical
Boolean cubes and a saturated upper endpoint. Their overlap has
exact mass:

    full_overlap = lower_endpoint_surplus + lower_target_weight.

We now reserve the LOWER surplus portion of *every* such carrier
SIMULTANEOUSLY, in addition to all already-paid hard faces.

Hard carrier pairs are a vertex matching. Therefore this additional
reservation NEVER reuses the surplus of a previously paid hard carrier.
The globally unpaid part of these equal-cube carriers is exactly the
sum of their lower target weights, rather than their entire cubes.

The soft overlap, remaining hard carriers and projected loss remain
unpaid. No unconditional planar capacity theorem is asserted here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- Rigid hard carriers excluded from full-face surplus payment,
but with a strictly slack LOWER endpoint and an upper endpoint
within the projected-free budget. These have exact residual debt
equal to the lower endpoint target weight. -/
noncomputable def ascendingUnpaidRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (rigidHardOverlapCarrierPairs C).filter (fun p =>
    p ∉ surplusPayableHardCarrierPairs C exponent ∧
    exponent p.1 < projectedFree C p.1 ∧
    exponent p.2 ≤ projectedFree C p.2)

@[simp] theorem mem_ascendingUnpaidRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ ascendingUnpaidRigidCarriers C exponent ↔
      p ∈ rigidHardOverlapCarrierPairs C ∧
      p ∉ surplusPayableHardCarrierPairs C exponent ∧
      exponent p.1 < projectedFree C p.1 ∧
      exponent p.2 ≤ projectedFree C p.2 := by
  classical
  simp [ascendingUnpaidRigidCarriers]

/-- No newly partial-paid ascending rigid carrier was in the
previously full-paid hard carrier family. -/
theorem paidHard_ascendingRigid_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (surplusPayableHardCarrierPairs C exponent)
      (ascendingUnpaidRigidCarriers C exponent) := by
  apply Finset.disjoint_left.mpr
  intro p hpaid ha
  exact ((mem_ascendingUnpaidRigidCarriers C exponent p).1 ha).2.1 hpaid

/-- Weighted version of the global hard-carrier matching principle:
ANY local nonnegative charge bounded by the two endpoint surpluses
can be reserved over a hard carrier subfamily without duplication. -/
theorem hard_matching_arbitrary_charge_le_total_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (S : Finset (V × V))
    (charge : V × V → ℕ)
    (hS : S ⊆ hardOverlapCarrierPairs C)
    (hlocal : ∀ p ∈ S,
      charge p ≤
        dyadicProfileSurplus exponent (projectedFree C) p.1 +
          dyadicProfileSurplus exponent (projectedFree C) p.2) :
    (∑ p ∈ S, charge p) ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let g : V → ℕ :=
    dyadicProfileSurplus exponent (projectedFree C)
  have hlocalSum :
      (∑ p ∈ S, charge p) ≤
        ∑ p ∈ S, (g p.1 + g p.2) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hlocal p hp
  have hres : S ⊆ residualCarrierPairs C := by
    intro p hp
    exact ((mem_overlapCarrierPairs C p).1
      ((mem_hardOverlapCarrierPairs C p).1 (hS hp)).1).1
  have hLoInj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q := by
    intro p hp q hq h
    exact hard_overlap_carriers_lower_unique C (hS hp) (hS hq) h
  have hHiInj : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q := by
    intro p hp q hq h
    exact hard_overlap_carriers_upper_unique C (hS hp) (hS hq) h
  have hLo :
      (∑ p ∈ S, g p.1) =
        ∑ v ∈ S.image Prod.fst, g v :=
    (Finset.sum_image hLoInj).symm
  have hHi :
      (∑ p ∈ S, g p.2) =
        ∑ v ∈ S.image Prod.snd, g v :=
    (Finset.sum_image hHiInj).symm
  have hdisj :=
    residual_carrier_lower_upper_images_disjoint C S hres
  have hUnion :
      (∑ v ∈ S.image Prod.fst, g v) +
        (∑ v ∈ S.image Prod.snd, g v) =
      ∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v := by
    symm
    exact Finset.sum_union hdisj
  have hsubset :
      S.image Prod.fst ∪ S.image Prod.snd ⊆
        (Finset.univ : Finset V) := Finset.subset_univ _
  have hsumLe :
      (∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v) ≤
        ∑ v : V, g v := Finset.sum_le_sum_of_subset hsubset
  unfold totalDyadicProfileSurplus
  calc
    (∑ p ∈ S, charge p) ≤
        ∑ p ∈ S, (g p.1 + g p.2) := hlocalSum
    _ = (∑ p ∈ S, g p.1) + (∑ p ∈ S, g p.2) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ v ∈ S.image Prod.fst, g v) +
        (∑ v ∈ S.image Prod.snd, g v) := by rw [hLo, hHi]
    _ = ∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v :=
      hUnion
    _ ≤ ∑ v : V, g v := hsumLe

/-- Global simultaneous budget: whole-face payments already certified
PLUS the additional lower surplus payments of ALL ascending rigid
unpaid carriers fit within TOTAL original dyadic surplus.
No vertex can be charged by two different hard carriers. -/
theorem paid_hard_mass_add_ascending_rigid_partial_le_total_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (surplusPaidHardOverlapWords C exponent).card +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
        dyadicProfileSurplus exponent (projectedFree C) p.1) ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let P := surplusPayableHardCarrierPairs C exponent
  let A := ascendingUnpaidRigidCarriers C exponent
  let S := P ∪ A
  let g : V → ℕ :=
    dyadicProfileSurplus exponent (projectedFree C)
  let charge : V × V → ℕ := fun p =>
    if p ∈ P then (carrierOverlapWords C p).card else g p.1
  have hdisj : Disjoint P A :=
    paidHard_ascendingRigid_disjoint C exponent
  have hS : S ⊆ hardOverlapCarrierPairs C := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpaid | hasc
    · exact ((mem_surplusPayableHardCarrierPairs
        C exponent p).1 hpaid).1
    · exact ((mem_rigidHardOverlapCarrierPairs C p).1
        ((mem_ascendingUnpaidRigidCarriers C exponent p).1 hasc).1).1
  have hlocal : ∀ p ∈ S, charge p ≤ g p.1 + g p.2 := by
    intro p hp
    by_cases hpaid : p ∈ P
    · simpa only [charge, if_pos hpaid] using
        surplusPayableHardCarrier_face_le_pair_surplus
          C exponent hpaid
    · simp only [charge, if_neg hpaid]
      omega
  have hbudget :=
    hard_matching_arbitrary_charge_le_total_surplus
      C exponent S charge hS hlocal
  have hpaidSum :
      (∑ p ∈ P, charge p) =
        ∑ p ∈ P, (carrierOverlapWords C p).card := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [charge, if_pos hp]
  have hascSum :
      (∑ p ∈ A, charge p) =
        ∑ p ∈ A, g p.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hnot : p ∉ P :=
      ((mem_ascendingUnpaidRigidCarriers C exponent p).1 hp).2.1
    simp only [charge, if_neg hnot]
  have hunion :
      (∑ p ∈ S, charge p) =
        (∑ p ∈ P, charge p) + (∑ p ∈ A, charge p) := by
    exact Finset.sum_union hdisj
  rw [hunion, hpaidSum, hascSum] at hbudget
  rw [surplusPaidHardOverlapWords_card_eq_carrier_mass]
  exact hbudget

/-- The complete ascending rigid overlap mass equals the extra
certified partial surplus reservation plus the remaining lower
target weights, with NO dyadic mass left unclassified. -/
theorem ascending_rigid_mass_eq_partial_credit_add_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
      (carrierOverlapWords C p).card) =
    (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
      dyadicProfileSurplus exponent (projectedFree C) p.1) +
    (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
      2 ^ exponent p.1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have h := (mem_ascendingUnpaidRigidCarriers C exponent p).1 hp
  obtain ⟨heq, hsat⟩ :=
    unpaid_rigid_strict_lower_forces_equal_free_upper_sat
      C exponent h.1 h.2.1 h.2.2.1 h.2.2.2
  have hzero :
      dyadicProfileSurplus exponent (projectedFree C) p.2 = 0 := by
    unfold dyadicProfileSurplus
    rw [hsat]
    omega
  have hmass :=
    unpaid_rigid_strict_lower_exact_overlap_debt
      C exponent h.1 h.2.1 h.2.2.1 h.2.2.2
  rw [hzero] at hmass
  omega

#print axioms hard_matching_arbitrary_charge_le_total_surplus
#print axioms paid_hard_mass_add_ascending_rigid_partial_le_total_surplus
#print axioms ascending_rigid_mass_eq_partial_credit_add_target

end OrderedEdgeColoring
end JSP000404Research
