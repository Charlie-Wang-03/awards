import JSP000404Research.ResidualRigidTwoEndpointSurplusPacking
import Mathlib.Tactic

/-!
# Global matching criterion pays whole Boolean faces of ANY hard carriers

Hard same-code overlap carriers are vertex-disjoint as residual pairs:
the lower and upper endpoint maps are individually injective, and
no residual lower endpoint can also be a residual upper endpoint.

Hence any selected hard-carrier subfamily whose intersection mass
is locally bounded by the sum of its TWO endpoint surpluses can be
paid GLOBALLY by total surplus, with no vertex charged twice.

In particular every hard pair STRICT at BOTH endpoints qualifies,
even if it is not rigid and irrespective of an outward safe colour.
We additionally retain rigid pairs with strictly smaller upper
projected-free dimensions and lower endpoint strictly slack.

This defines an UNCONDITIONAL certified payable class containing
all hard pairs with both endpoints strict and an extra rigid class.
Under the usual endpoint budget exponent<=projectedFree, every
remaining hard pair has at least one saturated endpoint.

This does NOT pay all soft overlap or projected profile loss.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- General exact mass payment for ANY hard-carrier subcollection,
provided each intersection face can locally be paid by the TWO
endpoint profile surpluses. The hard-carrier matching ensures that
no endpoint surplus is reused globally. -/
theorem hard_carrier_subset_paid_by_pair_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (S : Finset (V × V))
    (hS : S ⊆ hardOverlapCarrierPairs C)
    (hpair : ∀ p ∈ S,
      (carrierOverlapWords C p).card ≤
        dyadicProfileSurplus exponent (projectedFree C) p.1 +
          dyadicProfileSurplus exponent (projectedFree C) p.2) :
    (∑ p ∈ S, (carrierOverlapWords C p).card) ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let g : V → ℕ :=
    dyadicProfileSurplus exponent (projectedFree C)
  have hlocal :
      (∑ p ∈ S, (carrierOverlapWords C p).card) ≤
        ∑ p ∈ S, (g p.1 + g p.2) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hpair p hp
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
  have hdisj := residual_carrier_lower_upper_images_disjoint C S hres
  have hUnion :
      (∑ v ∈ S.image Prod.fst, g v) +
        (∑ v ∈ S.image Prod.snd, g v) =
      ∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v := by
    symm
    exact Finset.sum_union hdisj
  have hsubset : S.image Prod.fst ∪ S.image Prod.snd ⊆
      (Finset.univ : Finset V) := Finset.subset_univ _
  have hsumLe :
      (∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v) ≤
        ∑ v : V, g v := Finset.sum_le_sum_of_subset hsubset
  unfold totalDyadicProfileSurplus
  calc
    (∑ p ∈ S, (carrierOverlapWords C p).card)
        ≤ ∑ p ∈ S, (g p.1 + g p.2) := hlocal
    _ = (∑ p ∈ S, g p.1) + (∑ p ∈ S, g p.2) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ v ∈ S.image Prod.fst, g v) +
          (∑ v ∈ S.image Prod.snd, g v) := by rw [hLo, hHi]
    _ = ∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v := hUnion
    _ ≤ ∑ v : V, g v := hsumLe

/-- Sharpened payable hard carriers:
(1) BOTH endpoint exponents below projected-free dimensions; OR
(2) rigid nested, upper free dimension strictly smaller, lower
endpoint exponent strictly below its projected-free dimension. -/
noncomputable def surplusPayableHardCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (hardOverlapCarrierPairs C).filter (fun p =>
    (exponent p.1 < projectedFree C p.1 ∧
      exponent p.2 < projectedFree C p.2) ∨
    (p ∈ rigidHardOverlapCarrierPairs C ∧
      projectedFree C p.2 < projectedFree C p.1 ∧
      exponent p.1 < projectedFree C p.1))

@[simp] theorem mem_surplusPayableHardCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ surplusPayableHardCarrierPairs C exponent ↔
      p ∈ hardOverlapCarrierPairs C ∧
      ((exponent p.1 < projectedFree C p.1 ∧
        exponent p.2 < projectedFree C p.2) ∨
       (p ∈ rigidHardOverlapCarrierPairs C ∧
        projectedFree C p.2 < projectedFree C p.1 ∧
        exponent p.1 < projectedFree C p.1)) := by
  classical
  simp [surplusPayableHardCarrierPairs]

/-- The both-endpoint payable rigid class is a subfamily of
this sharper payable class of ALL hard residual carriers. -/
theorem twoEndpointPayableRigid_subset_surplusPayableHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    twoEndpointPayableRigidHardCarriers C exponent ⊆
      surplusPayableHardCarrierPairs C exponent := by
  intro p hp
  have h := (mem_twoEndpointPayableRigidHardCarriers C exponent p).1 hp
  have hhard := ((mem_rigidHardOverlapCarrierPairs C p).1 h.1).1
  apply (mem_surplusPayableHardCarrierPairs C exponent p).2
  constructor
  · exact hhard
  rcases h.2 with ⟨hfree,hlower⟩ | ⟨hfree,hlower,hupper⟩
  · right
    exact ⟨h.1,hfree,hlower⟩
  · left
    exact ⟨hlower,hupper⟩

/-- Pairwise profile surplus pays each eligible hard carrier,
regardless of whether its overlap cube can be flipped. -/
theorem surplusPayableHardCarrier_face_le_pair_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hp : p ∈ surplusPayableHardCarrierPairs C exponent) :
    (carrierOverlapWords C p).card ≤
      dyadicProfileSurplus exponent (projectedFree C) p.1 +
        dyadicProfileSurplus exponent (projectedFree C) p.2 := by
  have h := (mem_surplusPayableHardCarrierPairs C exponent p).1 hp
  rcases h.2 with ⟨hl,hr⟩ | ⟨hrigid,hfree,hlo⟩
  · have hpair := ((mem_overlapCarrierPairs C p).1
      ((mem_hardOverlapCarrierPairs C p).1 h.1).1).2
    obtain ⟨base,hbase⟩ := hpair
    exact overlap_card_le_pair_surplus_of_both_strict
      C exponent
      (Finset.mem_inter.mp hbase).1
      (Finset.mem_inter.mp hbase).2
      hl hr
  · have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
    have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
    have hlbound :=
      rigid_hard_overlap_paid_by_lower_surplus_of_strict_dimension
        C exponent hsame hrig.2 hfree hlo
    unfold carrierOverlapWords
    omega

/-- The ENTIRE eligible hard overlap mass is surplus-paid with
no reused vertex. In particular this includes ALL hard carriers
having two strictly slack endpoints. -/
theorem sum_surplusPayableHardMass_le_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ p ∈ surplusPayableHardCarrierPairs C exponent,
      (carrierOverlapWords C p).card) ≤
        totalDyadicProfileSurplus exponent (projectedFree C) := by
  apply hard_carrier_subset_paid_by_pair_surplus C exponent
  · intro p hp
    exact ((mem_surplusPayableHardCarrierPairs C exponent p).1 hp).1
  · intro p hp
    exact surplusPayableHardCarrier_face_le_pair_surplus C exponent hp

/-- Every hard carrier remaining OUTSIDE this certified
surplus-payable class has at least one saturated endpoint,
under the ordinary projected-free budget on both endpoints. -/
theorem hard_not_payable_implies_endpoint_saturation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hcarrier : p ∈ hardOverlapCarrierPairs C)
    (hbudgetLo : exponent p.1 ≤ projectedFree C p.1)
    (hbudgetHi : exponent p.2 ≤ projectedFree C p.2)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent) :
    exponent p.1 = projectedFree C p.1 ∨
      exponent p.2 = projectedFree C p.2 := by
  by_contra hsat
  push_neg at hsat
  have hlo : exponent p.1 < projectedFree C p.1 := by omega
  have hhi : exponent p.2 < projectedFree C p.2 := by omega
  exact hnot ((mem_surplusPayableHardCarrierPairs C exponent p).2
    ⟨hcarrier,Or.inl ⟨hlo,hhi⟩⟩)

#print axioms hard_carrier_subset_paid_by_pair_surplus
#print axioms twoEndpointPayableRigid_subset_surplusPayableHard
#print axioms sum_surplusPayableHardMass_le_totalSurplus
#print axioms hard_not_payable_implies_endpoint_saturation

end OrderedEdgeColoring
end JSP000404Research
