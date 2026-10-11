import JSP000404Research.ResidualRigidPaidDefectReduction
import JSP000404Research.ResidualOverlapSurplus
import Mathlib.Tactic

/-!
# Globally pack BOTH endpoint surplus budgets of rigid hard faces

Earlier only a strictly wider lower cube could pay a full rigid
upper cube, by its lower endpoint surplus. Here we also pay EQUAL
projected-free rigid faces when BOTH endpoint profiles are strict:
two half-block surpluses together dominate the entire overlap.

The genuinely new global step is that ALL residual carrier lower
endpoints form one subset of vertices, and all their upper endpoints
form a DISJOINT second subset. Moreover same-retained HARD carriers
are injective on each endpoint. Therefore every vertex surplus
occurs at most once even after allowing BOTH endpoints as payers.

This broadens the rigid class payable with fully reserved, non-reused
global surplus. Rigid equal-free pairs with a saturated endpoint,
or pairs with saturated lower endpoint, remain unresolved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- Same-retained hard residual pairs have UNIQUE upper endpoints:
two hard pairs with the same upper endpoint must coincide. -/
theorem hard_overlap_carriers_upper_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {p q : V × V}
    (hp : p ∈ hardOverlapCarrierPairs C)
    (hq : q ∈ hardOverlapCarrierPairs C)
    (hupper : p.2 = q.2) :
    p = q := by
  have hpdata := (mem_hardOverlapCarrierPairs C p).1 hp
  have hqdata := (mem_hardOverlapCarrierPairs C q).1 hq
  have hporder : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1 hpdata.1).1).1
  have hqorder : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1 hqdata.1).1).1
  have hqlt : q.1 < p.2 := by
    simpa only [hupper] using hqorder
  have hqsame : SameRetained C q.1 p.2 := by
    intro d
    simpa only [hupper] using hqdata.2 d
  have hlower :=
    sameRetained_pairs_same_upper_unique_lower
      C hporder hqlt hpdata.2 hqsame
  exact Prod.ext hlower hupper

/-- The lower and upper vertex sets of ANY finite subcollection
of residual edges are DISJOINT: otherwise one vertex would lie
in the middle of a forbidden residual-residual two-path. -/
theorem residual_carrier_lower_upper_images_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (S : Finset (V × V))
    (hsubset : S ⊆ residualCarrierPairs C) :
    Disjoint (S.image Prod.fst) (S.image Prod.snd) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvLower hvUpper
  obtain ⟨p,hp,hpv⟩ := Finset.mem_image.mp hvLower
  obtain ⟨q,hq,hqv⟩ := Finset.mem_image.mp hvUpper
  have hpRes := (mem_residualCarrierPairs C p.1 p.2).1 (hsubset hp)
  have hqRes := (mem_residualCarrierPairs C q.1 q.2).1 (hsubset hq)
  have hmid : q.2 = p.1 := hqv.trans hpv.symm
  have hpath : q.2 < p.2 := by
    rw [hmid]
    exact hpRes.1
  have hfirst : IsResidual C q.1 q.2 := hqRes.2
  have hsecond : IsResidual C q.2 p.2 := by
    rw [hmid]
    exact hpRes.2
  exact no_two_residual_on_path C hqRes.1 hpath hfirst hsecond

/-- Rigid carriers additionally payable using two endpoint surpluses:
either lower projected dimension is larger with lower strictly slack,
or dimensions are equal with BOTH endpoints strictly slack. -/
noncomputable def twoEndpointPayableRigidHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (rigidHardOverlapCarrierPairs C).filter (fun p =>
    (projectedFree C p.2 < projectedFree C p.1 ∧
      exponent p.1 < projectedFree C p.1) ∨
    (projectedFree C p.2 = projectedFree C p.1 ∧
      exponent p.1 < projectedFree C p.1 ∧
      exponent p.2 < projectedFree C p.2))

@[simp] theorem mem_twoEndpointPayableRigidHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ twoEndpointPayableRigidHardCarriers C exponent ↔
      p ∈ rigidHardOverlapCarrierPairs C ∧
        ((projectedFree C p.2 < projectedFree C p.1 ∧
          exponent p.1 < projectedFree C p.1) ∨
         (projectedFree C p.2 = projectedFree C p.1 ∧
          exponent p.1 < projectedFree C p.1 ∧
          exponent p.2 < projectedFree C p.2)) := by
  classical
  simp [twoEndpointPayableRigidHardCarriers]

/-- The previously payable lower-only rigid pairs stay payable. -/
theorem oneSidedPayable_subset_twoEndpointPayable
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    oneSidedPayableRigidHardCarriers C exponent ⊆
      twoEndpointPayableRigidHardCarriers C exponent := by
  intro p hp
  have h := (mem_oneSidedPayableRigidHardCarriers C exponent p).1 hp
  exact (mem_twoEndpointPayableRigidHardCarriers C exponent p).2
    ⟨h.1, Or.inl ⟨h.2.1,h.2.2⟩⟩

/-- An eligible rigid face's FULL DYADIC mass is paid by
the SUM of its lower and upper endpoint profile surpluses. -/
theorem twoEndpointPayableRigidFace_le_pair_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hp : p ∈ twoEndpointPayableRigidHardCarriers C exponent) :
    2 ^ projectedFree C p.2 ≤
      dyadicProfileSurplus exponent (projectedFree C) p.1 +
        dyadicProfileSurplus exponent (projectedFree C) p.2 := by
  have h := (mem_twoEndpointPayableRigidHardCarriers
    C exponent p).1 hp
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 h.1
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  rcases h.2 with ⟨hfree,hstrict⟩ | ⟨hfree,hstrictLo,hstrictHi⟩
  · have hlocal :=
      rigid_hard_overlap_paid_by_lower_surplus_of_strict_dimension
        C exponent hsame hrig.2 hfree hstrict
    rw [hard_no_transport_inter_card_eq_projected_cube
      C hsame hrig.2] at hlocal
    omega
  · have hbounds : projectedFree C p.2 ≤ projectedFree C p.1 := by
      omega
    have hpair :=
      pow_le_sum_dyadic_surplus_of_both_lt
        (d := projectedFree C p.2)
        (x := exponent p.1)
        (y := exponent p.2)
        (a := projectedFree C p.1)
        (b := projectedFree C p.2)
        hbounds (by omega) hstrictLo hstrictHi
    simpa only [dyadicProfileSurplus] using hpair

/-- ALL eligible rigid faces, including the new EQUAL-DIMENSION
strict/strict class, have their complete mass paid by GLOBAL
surplus with NO reused vertex budgets. -/
theorem sum_twoEndpointPayableRigidMass_le_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ p ∈ twoEndpointPayableRigidHardCarriers C exponent,
        2 ^ projectedFree C p.2) ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let S := twoEndpointPayableRigidHardCarriers C exponent
  let g : V → ℕ :=
    dyadicProfileSurplus exponent (projectedFree C)
  have hpLocal :
      (∑ p ∈ S, 2 ^ projectedFree C p.2) ≤
        ∑ p ∈ S, (g p.1 + g p.2) := by
    apply Finset.sum_le_sum
    intro p hp
    exact twoEndpointPayableRigidFace_le_pair_surplus C exponent hp
  have hsub : S ⊆ hardOverlapCarrierPairs C := by
    intro p hp
    exact ((mem_rigidHardOverlapCarrierPairs C p).1
      ((mem_twoEndpointPayableRigidHardCarriers C exponent p).1 hp).1).1
  have hres : S ⊆ residualCarrierPairs C := by
    intro p hp
    exact ((mem_overlapCarrierPairs C p).1
      ((mem_hardOverlapCarrierPairs C p).1 (hsub hp)).1).1
  have hLoInj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q := by
    intro p hp q hq h
    exact hard_overlap_carriers_lower_unique C (hsub hp) (hsub hq) h
  have hHiInj : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q := by
    intro p hp q hq h
    exact hard_overlap_carriers_upper_unique C (hsub hp) (hsub hq) h
  have hLo :
      (∑ p ∈ S, g p.1) = ∑ v ∈ S.image Prod.fst, g v := by
    exact (Finset.sum_image hLoInj).symm
  have hHi :
      (∑ p ∈ S, g p.2) = ∑ v ∈ S.image Prod.snd, g v := by
    exact (Finset.sum_image hHiInj).symm
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
  have hsplit :
      (∑ p ∈ S, (g p.1 + g p.2)) =
      (∑ p ∈ S, g p.1) + (∑ p ∈ S, g p.2) := by
    rw [Finset.sum_add_distrib]
  unfold totalDyadicProfileSurplus
  calc
    (∑ p ∈ S, 2 ^ projectedFree C p.2) ≤
      ∑ p ∈ S, (g p.1 + g p.2) := hpLocal
    _ = (∑ p ∈ S, g p.1) + (∑ p ∈ S, g p.2) := hsplit
    _ = (∑ v ∈ S.image Prod.fst, g v) +
          (∑ v ∈ S.image Prod.snd, g v) := by rw [hLo,hHi]
    _ = ∑ v ∈ S.image Prod.fst ∪ S.image Prod.snd, g v := hUnion
    _ ≤ ∑ v : V, g v := hsumLe

#print axioms hard_overlap_carriers_upper_unique
#print axioms residual_carrier_lower_upper_images_disjoint
#print axioms twoEndpointPayableRigidFace_le_pair_surplus
#print axioms sum_twoEndpointPayableRigidMass_le_totalSurplus

end OrderedEdgeColoring
end JSP000404Research
