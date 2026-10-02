import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Exact transfer formula for a unique-neighbour leaf

For an abstract finite block family, suppose v belongs to the core T and all
other blocks crossing B_v are the single block B_w, where w is another member
of T.  Then the shared words of v are exactly B_v ∩ B_w.

Consequently the deleted-vertex transfer is exactly

  |B_v ∩ B_w| - (|B_v| - demand(v)),

provided the local block has enough capacity for demand(v).

In an inclusion-minimal deficient core the transfer is positive, so every
unique-neighbour leaf satisfies the sharp edge inequality

  localSlack(v) < |B_v ∩ B_w|.

This is the tree-DP interpretation of the existing leaf machinery.
-/

namespace JSP000404Research

theorem sharedBlockWords_eq_unique_neighbor_intersection
    {V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    {T : Finset V}
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        BlocksCross blocks v z →
        z = w) :
    sharedBlockWords blocks T v = blocks v ∩ blocks w := by
  classical
  apply Finset.Subset.antisymm
  · exact
      sharedBlockWords_subset_single_neighbor_intersection
        blocks hvT
        (by
          intro z hzT hzv hcross
          exact hunique z hzT hzv hcross)
  · intro word hword
    have hparts := Finset.mem_inter.mp hword
    apply Finset.mem_inter.mpr
    refine ⟨hparts.1,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w,Finset.mem_erase.mpr ⟨hvw.symm,hwT⟩,hparts.2⟩

theorem deletedVertexTransfer_eq_unique_neighbor_overlap_minus_slack
    {V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        BlocksCross blocks v z →
        z = w)
    (hlocal : demand v ≤ (blocks v).card) :
    deletedVertexTransfer demand blocks T v =
      (blocks v ∩ blocks w).card -
        ((blocks v).card - demand v) := by
  rw [deletedVertexTransfer_eq_shared_minus_slack
        demand blocks T v hlocal]
  rw [sharedBlockWords_eq_unique_neighbor_intersection
        blocks hvT hwT hvw hunique]

theorem minimal_deficient_unique_neighbor_overlap_gt_slack
    {V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        BlocksCross blocks v z →
        z = w)
    (hlocal : demand v ≤ (blocks v).card) :
    (blocks v).card - demand v <
      (blocks v ∩ blocks w).card := by
  have htransfer :=
    minimal_deficient_deletedVertexTransfer_pos
      demand blocks hdef hmin hvT
  rw [deletedVertexTransfer_eq_unique_neighbor_overlap_minus_slack
        demand blocks hvT hwT hvw hunique hlocal] at htransfer
  omega

#print axioms sharedBlockWords_eq_unique_neighbor_intersection
#print axioms deletedVertexTransfer_eq_unique_neighbor_overlap_minus_slack
#print axioms minimal_deficient_unique_neighbor_overlap_gt_slack

end JSP000404Research
