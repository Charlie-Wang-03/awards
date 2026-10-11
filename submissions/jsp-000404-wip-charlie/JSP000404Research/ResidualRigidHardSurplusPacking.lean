import JSP000404Research.ResidualHardRigidMassAccounting
import Mathlib.Tactic

/-!
# Collision-free global surplus payment for the easy rigid subfamily

A hard pair (a,v) shares one retained canonical Boolean code;
therefore no lower endpoint a can participate in TWO different hard
carrier pairs. This is stronger than merely bounding the number
of times its projected completion cube appears.

Separate the rigid nested pairs with
  projectedFree(v) < projectedFree(a)
and
  exponent(a) < projectedFree(a).
For each such pair, its ENTIRE rigid overlap face
  2 ^ projectedFree(v)
is paid by the lower endpoint's own dyadic profile surplus.

Since distinct hard pairs have distinct LOWER endpoints, the
surplus accounts cannot be charged more than once. Consequently
the whole eligible rigid mass is bounded by the GLOBAL surplus.

The exceptional rigid pairs are those with equal free dimensions
or a saturated lower endpoint, under the usual exponent budget.
Nothing in this module pays the soft-overlap or profile-loss terms.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A lower vertex can be the lower endpoint of AT MOST ONE
hard same-retained overlapping residual carrier. -/
theorem hard_overlap_carriers_lower_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {p q : V × V}
    (hp : p ∈ hardOverlapCarrierPairs C)
    (hq : q ∈ hardOverlapCarrierPairs C)
    (hlower : p.1 = q.1) :
    p = q := by
  have hpdata := (mem_hardOverlapCarrierPairs C p).1 hp
  have hqdata := (mem_hardOverlapCarrierPairs C q).1 hq
  have hporder : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1 hpdata.1).1).1
  have hqorder : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1 hqdata.1).1).1
  have hpne : p.2 ≠ p.1 := ne_of_gt hporder
  have hqne : q.2 ≠ p.1 := by
    intro heq
    have h : q.2 = q.1 := heq.trans hlower
    exact (ne_of_gt hqorder) h
  have hpSame : SameRetained C p.2 p.1 := by
    intro c
    exact (hpdata.2 c).symm
  have hqSame : SameRetained C q.2 p.1 := by
    intro c
    simpa only [hlower] using (hqdata.2 c).symm
  have hupper :=
    sameRetained_two_distinct_companions_equal
      C hpne hqne hpSame hqSame
  exact Prod.ext hlower hupper

/-- Rigid nested pairs whose full upper face is paid by one
strictly wider, nonsaturated LOWER projected completion cube. -/
noncomputable def oneSidedPayableRigidHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (rigidHardOverlapCarrierPairs C).filter
    (fun p => projectedFree C p.2 < projectedFree C p.1 ∧
      exponent p.1 < projectedFree C p.1)

@[simp] theorem mem_oneSidedPayableRigidHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (p : V × V) :
    p ∈ oneSidedPayableRigidHardCarriers C exponent ↔
      p ∈ rigidHardOverlapCarrierPairs C ∧
      projectedFree C p.2 < projectedFree C p.1 ∧
      exponent p.1 < projectedFree C p.1 := by
  classical
  simp [oneSidedPayableRigidHardCarriers]

/-- No double charge of lower endpoint surplus is possible for
distinct payable rigid hard carriers. -/
theorem oneSidedPayableRigidHardCarriers_lower_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p q : V × V}
    (hp : p ∈ oneSidedPayableRigidHardCarriers C exponent)
    (hq : q ∈ oneSidedPayableRigidHardCarriers C exponent)
    (hlower : p.1 = q.1) :
    p = q := by
  apply hard_overlap_carriers_lower_unique C
  · have h := ((mem_oneSidedPayableRigidHardCarriers
      C exponent p).1 hp).1
    exact ((mem_rigidHardOverlapCarrierPairs C p).1 h).1
  · have h := ((mem_oneSidedPayableRigidHardCarriers
      C exponent q).1 hq).1
    exact ((mem_rigidHardOverlapCarrierPairs C q).1 h).1
  · exact hlower

/-- Every single eligible rigid face is paid by the
corresponding distinct lower endpoint's own surplus. -/
theorem oneSidedPayableRigidFace_le_lower_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V}
    (hp : p ∈ oneSidedPayableRigidHardCarriers C exponent) :
    2 ^ projectedFree C p.2 ≤
      dyadicProfileSurplus exponent (projectedFree C) p.1 := by
  have hparts := (mem_oneSidedPayableRigidHardCarriers
    C exponent p).1 hp
  have hrigid := (mem_rigidHardOverlapCarrierPairs
    C p).1 hparts.1
  have hsame := ((mem_hardOverlapCarrierPairs
    C p).1 hrigid.1).2
  have hlocal :=
    rigid_hard_overlap_paid_by_lower_surplus_of_strict_dimension
      C exponent hsame hrigid.2 hparts.2.1 hparts.2.2
  rw [hard_no_transport_inter_card_eq_projected_cube
    C hsame hrigid.2] at hlocal
  exact hlocal

/-- GLOBAL exact-face payment for all easy rigid pairs.
This uses unique lower endpoints, not a separate Hall assumption. -/
theorem sum_oneSidedPayableRigidMass_le_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ p ∈ oneSidedPayableRigidHardCarriers C exponent,
        2 ^ projectedFree C p.2) ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let S := oneSidedPayableRigidHardCarriers C exponent
  let g : V → ℕ :=
    fun v => dyadicProfileSurplus exponent (projectedFree C) v
  have hlocal :
      (∑ p ∈ S, 2 ^ projectedFree C p.2) ≤
        ∑ p ∈ S, g p.1 := by
    apply Finset.sum_le_sum
    intro p hp
    exact oneSidedPayableRigidFace_le_lower_surplus C exponent hp
  have hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q := by
    intro p hp q hq h
    exact oneSidedPayableRigidHardCarriers_lower_injective
      C exponent hp hq h
  have hsum :
      (∑ p ∈ S, g p.1) =
      ∑ v ∈ S.image Prod.fst, g v := by
    exact (Finset.sum_image hinj).symm
  have hsubset : S.image Prod.fst ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hupper :
      (∑ v ∈ S.image Prod.fst, g v) ≤
      ∑ v : V, g v := by
    exact Finset.sum_le_sum_of_subset hsubset
  unfold totalDyadicProfileSurplus
  exact hlocal.trans (hsum.le.trans hupper)

/-- A rigid hard pair failing lower-only surplus payment under
the residual-vertex budget must be an exceptional one: equal
free dimensions or saturated lower endpoint. -/
theorem unpaid_rigid_hard_exceptional_equal_free_or_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v)
    (hbudget : exponent a ≤ projectedFree C a)
    (hnotPay : ¬
      ((retainedCompletionWords C a ∩
        retainedCompletionWords C v).card ≤
          dyadicProfileSurplus exponent (projectedFree C) a)) :
    projectedFree C v = projectedFree C a ∨
      exponent a = projectedFree C a :=
  rigid_hard_unpaid_implies_equal_free_or_lower_saturated
    C exponent hsame hno hbudget hnotPay

#print axioms hard_overlap_carriers_lower_unique
#print axioms oneSidedPayableRigidHardCarriers_lower_injective
#print axioms sum_oneSidedPayableRigidMass_le_totalSurplus
#print axioms unpaid_rigid_hard_exceptional_equal_free_or_saturated

end OrderedEdgeColoring
end JSP000404Research
