import JSP000404Research.ResidualLossCrossSliceCarrier
import Mathlib.Tactic

/-!
# Pairwise upper bound for duplicate loss mass

The overcount caused by combining a finite sequence of Boolean-word
finsets never exceeds the sum of pairwise intersections.

This is a universal finite-set statement, independent of geometric
AngleCap, and cannot itself produce outside true holes or surplus.

First work with a natural prefix, to keep the exact telescoping argument
and each old/new intersection visible to Lean.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Union of the first k finite slices. -/
noncomputable def lossPrefixUnion
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) : Finset α :=
  (Finset.range k).biUnion A

/-- The union's overlap with the new slice is paid by pairwise
intersections with the preceding slices. This is ONLY a bound on
double counting, not a globally non-reusing terminal payment. -/
theorem lossPrefixUnion_inter_card_le_pairwise
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) :
    (lossPrefixUnion A k ∩ A k).card ≤
      ∑ j ∈ Finset.range k, (A k ∩ A j).card := by
  classical
  have heq :
      lossPrefixUnion A k ∩ A k =
        (Finset.range k).biUnion (fun j => A k ∩ A j) := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hU, hk⟩ := Finset.mem_inter.mp hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hU
      exact Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_inter.mpr ⟨hk, hxj⟩⟩
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hk, hjx⟩ := Finset.mem_inter.mp hxj
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨j, hj, hjx⟩, hk⟩
  rw [heq]
  exact Finset.card_biUnion_le

/-- General finite-prefix Bonferroni-type bound:
sum of individual slice cardinalities is at most the union
cardinality plus all PREVIOUS-vs-NEW pair intersections. -/
theorem lossSumCard_le_prefixUnion_add_pairwise
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) :
    (∑ i ∈ Finset.range k, (A i).card) ≤
      (lossPrefixUnion A k).card +
        ∑ i ∈ Finset.range k,
          ∑ j ∈ Finset.range i, (A i ∩ A j).card := by
  classical
  induction k with
  | zero =>
      simp [lossPrefixUnion]
  | succ k ih =>
      have hunion :
          lossPrefixUnion A (k + 1) =
            lossPrefixUnion A k ∪ A k := by
        simp [lossPrefixUnion, Finset.range_add_one, Finset.union_comm]
      have hcard :=
        Finset.card_union_add_card_inter (lossPrefixUnion A k) (A k)
      have hinter :=
        lossPrefixUnion_inter_card_le_pairwise A k
      simp only [Finset.sum_range_succ, hunion]
      omega

#print axioms lossPrefixUnion_inter_card_le_pairwise
#print axioms lossSumCard_le_prefixUnion_add_pairwise

end OrderedEdgeColoring
end JSP000404Research
