import JSP000404Research.ResidualTerminalRigidTwinIncidence
import JSP000404Research.ResidualHardOverlapCubeSoftRouting
import JSP000404Research.ResidualUnsafeCarrierMatchingCard
import Mathlib.Tactic

/-!
# Every hard residual-overlap carrier occupies a disjoint pair of vertices

The same-retained code of the two vertices of a hard residual carrier
cannot be shared by a THIRD vertex, due to the previously certified
no-three-distinct-retained-completions lemma.

Here we strengthen unique Boolean-WORD ownership to unique VERTEX
ownership: distinct hard carriers cannot share even one endpoint,
irrespective of their individual overlap Boolean words.

Hence the entire family of hard overlap carriers (not just unsafe
ones or the terminal rigid subfamily) is a VERTEX MATCHING:

    2 * card(hardOverlapCarrierPairs C) <= card(V).

This is an unconditional combinatorial sparsity conclusion, even
before any planar one-layer geometric budget is applied. It does
NOT make the global defect-payment inequality true.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Distinct hard overlap carriers have disjoint endpoint pairs.
A retained code cannot have three distinct carriers' vertices. -/
theorem hard_carrier_shared_endpoint_implies_same_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {p q : V × V}
    (hp : p ∈ hardOverlapCarrierPairs C)
    (hq : q ∈ hardOverlapCarrierPairs C)
    (hshare :
      p.1 = q.1 ∨ p.1 = q.2 ∨
      p.2 = q.1 ∨ p.2 = q.2) :
    p = q := by
  have hpe : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hp).1).1).1
  have hqe : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hq).1).1).1
  have hpc : SameRetained C p.1 p.2 :=
    ((mem_hardOverlapCarrierPairs C p).1 hp).2
  have hqc : SameRetained C q.1 q.2 :=
    ((mem_hardOverlapCarrierPairs C q).1 hq).2
  rcases hshare with hll | hlr | hrl | hrr
  · have hcode : SameRetained C q.2 p.1 := by
      intro c
      calc
        retainedBit C q.2 c = retainedBit C q.1 c := (hqc c).symm
        _ = retainedBit C p.1 c := by rw [hll]
    have hneq : q.2 ≠ p.1 := by
      rw [hll]
      exact ne_of_gt hqe
    have hOther :=
      sameRetained_two_distinct_companions_equal C
        (ne_of_gt hpe) hneq (fun c => (hpc c).symm) hcode
    exact Prod.ext hll hOther
  · have hcode : SameRetained C q.1 p.1 := by
      intro c
      calc
        retainedBit C q.1 c = retainedBit C q.2 c := hqc c
        _ = retainedBit C p.1 c := by rw [hlr]
    have hneq : q.1 ≠ p.1 := by
      rw [hlr]
      exact ne_of_lt hqe
    have hOther :=
      sameRetained_two_distinct_companions_equal C
        (ne_of_gt hpe) hneq (fun c => (hpc c).symm) hcode
    have hless : q.1 < p.1 := by
      rw [hlr]
      exact hqe
    have hcycle : p.1 < p.1 := by
      calc
        p.1 < p.2 := hpe
        _ = q.1 := hOther
        _ < p.1 := hless
    exact (lt_irrefl _ hcycle).elim
  · have hcode : SameRetained C q.2 p.2 := by
      intro c
      calc
        retainedBit C q.2 c = retainedBit C q.1 c := (hqc c).symm
        _ = retainedBit C p.2 c := by rw [hrl]
    have hneq : q.2 ≠ p.2 := by
      rw [hrl]
      exact ne_of_gt hqe
    have hOther :=
      sameRetained_two_distinct_companions_equal C
        (ne_of_lt hpe) hneq hpc hcode
    have hless : p.2 < q.2 := by
      rw [hrl]
      exact hqe
    have hcycle : p.1 < p.1 := by
      calc
        p.1 < p.2 := hpe
        _ < q.2 := hless
        _ = p.1 := hOther.symm
    exact (lt_irrefl _ hcycle).elim
  · have hcode : SameRetained C q.1 p.2 := by
      intro c
      calc
        retainedBit C q.1 c = retainedBit C q.2 c := hqc c
        _ = retainedBit C p.2 c := by rw [hrr]
    have hneq : q.1 ≠ p.2 := by
      rw [hrr]
      exact ne_of_lt hqe
    have hOther :=
      sameRetained_two_distinct_companions_equal C
        (ne_of_lt hpe) hneq hpc hcode
    exact Prod.ext hOther hrr

/-- ALL hard residual-overlap carriers form a matching on the
vertices, even without any projected-free budget assumptions. -/
theorem hardOverlapCarrierPairs_two_mul_card_le_vertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    2 * (hardOverlapCarrierPairs C).card ≤ Fintype.card V := by
  classical
  apply matching_orderedPairs_two_mul_card_le
    (hardOverlapCarrierPairs C)
  · intro p hp
    have hpe : p.1 < p.2 :=
      ((mem_residualCarrierPairs C p.1 p.2).1
        ((mem_overlapCarrierPairs C p).1
          ((mem_hardOverlapCarrierPairs C p).1 hp).1).1).1
    exact ne_of_lt hpe
  · intro p hp q hq hshare
    exact hard_carrier_shared_endpoint_implies_same_pair C hp hq hshare

/-- In particular, double-saturated terminal rigid carriers use
two distinct vertices each and are bounded by half the vertex count. -/
theorem netRigidHardCarriers_two_mul_card_le_vertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    2 * (netRigidHardCarriers C exponent).card ≤ Fintype.card V := by
  classical
  apply matching_orderedPairs_two_mul_card_le
    (netRigidHardCarriers C exponent)
  · intro p hp
    have hhard :=
      ((mem_netUnpaidHardCarrierPairs C exponent p).1
        ((mem_netRigidHardCarriers C exponent p).1 hp).1).1
    have hpe : p.1 < p.2 :=
      ((mem_residualCarrierPairs C p.1 p.2).1
        ((mem_overlapCarrierPairs C p).1
          ((mem_hardOverlapCarrierPairs C p).1 hhard).1).1).1
    exact ne_of_lt hpe
  · intro p hp q hq hshare
    have hpHard :=
      ((mem_netUnpaidHardCarrierPairs C exponent p).1
        ((mem_netRigidHardCarriers C exponent p).1 hp).1).1
    have hqHard :=
      ((mem_netUnpaidHardCarrierPairs C exponent q).1
        ((mem_netRigidHardCarriers C exponent q).1 hq).1).1
    exact hard_carrier_shared_endpoint_implies_same_pair
      C hpHard hqHard hshare

#print axioms hard_carrier_shared_endpoint_implies_same_pair
#print axioms hardOverlapCarrierPairs_two_mul_card_le_vertices
#print axioms netRigidHardCarriers_two_mul_card_le_vertices

end OrderedEdgeColoring
end JSP000404Research
