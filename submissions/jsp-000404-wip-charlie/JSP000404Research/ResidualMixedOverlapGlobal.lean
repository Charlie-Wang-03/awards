
import JSP000404Research.ResidualMixedOverlapForest
import Mathlib.Tactic

/-!
# Global half-mass bound for mixed unpaid overlaps

The mixed-unpaid relation is even simpler than a general forest:

* every parent is projected-budget saturated;
* every child is projected-strict.

So a child can never itself be a parent.  The graph has depth one.

ResidualMixedOverlapForest proves that for each parent p,

  2 * sum_{c child of p} 2^k(c) <= 2^k(p),

and that each child has at most one parent.

Therefore the child families of distinct parents are pairwise disjoint.
Summing the local Kraft inequalities gives the global estimate

  2 * sum_{all mixed-unpaid children c} 2^k(c)
    <= sum_v 2^k(v).

Equivalently, after the strict endpoint's profile surplus is spent, the exact
remaining target-weight cost of all mixed hard carriers is at most one half of
the total target mass.

This leaves saturated--saturated overlap carriers as the genuinely different
hard remainder.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- Child sets of distinct mixed-unpaid parents are disjoint, because every
child has a unique parent. -/
theorem mixedUnpaidChildren_family_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((Finset.univ : Finset V) : Set V).PairwiseDisjoint
      (mixedUnpaidChildren C exponent) := by
  intro p _hp q _hq hpq
  classical
  rw [Finset.disjoint_left]
  intro child hpc hqc
  have hpRel :
      MixedUnpaidChild C exponent p child :=
    (mem_mixedUnpaidChildren C exponent p child).1 hpc
  have hqRel :
      MixedUnpaidChild C exponent q child :=
    (mem_mixedUnpaidChildren C exponent q child).1 hqc
  exact hpq
    (mixedUnpaidChild_parent_unique
      C exponent hpRel hqRel)

noncomputable def allMixedUnpaidChildren
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset V := by
  classical
  exact (Finset.univ : Finset V).biUnion
    (mixedUnpaidChildren C exponent)

@[simp] theorem mem_allMixedUnpaidChildren
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (child : V) :
    child ∈ allMixedUnpaidChildren C exponent ↔
      ∃ parent : V,
        MixedUnpaidChild C exponent parent child := by
  classical
  simp [allMixedUnpaidChildren]

/-- Any parent with a nonempty child set is automatically saturated, so the
local Kraft branch inequality holds for every ambient vertex. -/
theorem mixedUnpaidChildren_kraft_branch_any
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent : V) :
    2 * (∑ child ∈ mixedUnpaidChildren C exponent parent,
      2 ^ exponent child)
      ≤
    2 ^ exponent parent := by
  classical
  by_cases hne :
      (mixedUnpaidChildren C exponent parent).Nonempty
  · obtain ⟨child, hchild⟩ := hne
    have hrel :
        MixedUnpaidChild C exponent parent child :=
      (mem_mixedUnpaidChildren C exponent parent child).1 hchild
    exact mixedUnpaidChildren_kraft_branch
      C exponent parent
      (mixedUnpaidChild_parent_saturated hrel)
  · have hempty :
        mixedUnpaidChildren C exponent parent = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- Sum over the disjoint family of child sets equals the weight of the global
mixed-child union. -/
theorem allMixedUnpaidChildren_weight_eq_double_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ child ∈ allMixedUnpaidChildren C exponent,
        2 ^ exponent child)
      =
    ∑ parent : V,
      ∑ child ∈ mixedUnpaidChildren C exponent parent,
        2 ^ exponent child := by
  classical
  unfold allMixedUnpaidChildren
  rw [Finset.sum_biUnion
    (mixedUnpaidChildren_family_pairwiseDisjoint
      C exponent)]

/-- Global mixed-unpaid child target mass is at most half of the total target
mass. -/
theorem two_mul_allMixedUnpaidChildren_weight_le_total
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    2 * (∑ child ∈ allMixedUnpaidChildren C exponent,
      2 ^ exponent child)
      ≤
    ∑ v : V, 2 ^ exponent v := by
  classical
  have hsum :
      ∑ parent : V,
        2 * (∑ child ∈ mixedUnpaidChildren C exponent parent,
          2 ^ exponent child)
        ≤
      ∑ parent : V, 2 ^ exponent parent := by
    exact Finset.sum_le_sum fun parent _ =>
      mixedUnpaidChildren_kraft_branch_any
        C exponent parent
  rw [← Finset.mul_sum] at hsum
  rw [allMixedUnpaidChildren_weight_eq_double_sum
      C exponent]
  exact hsum

/-- A mixed-unpaid child cannot simultaneously be a mixed-unpaid parent,
because child status is strict while parent status is saturated. -/
theorem mixedUnpaidChild_not_parent
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {parent child grandchild : V}
    (hpc : MixedUnpaidChild C exponent parent child)
    (hcg : MixedUnpaidChild C exponent child grandchild) :
    False := by
  have hstrict :=
    mixedUnpaidChild_child_strict hpc
  have hsat :=
    mixedUnpaidChild_parent_saturated hcg
  rw [hsat] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Hence the mixed-unpaid containment graph has no directed path of length
two; it is literally a star forest. -/
theorem no_two_step_mixedUnpaidChild
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ¬ ∃ a b c : V,
      MixedUnpaidChild C exponent a b ∧
      MixedUnpaidChild C exponent b c := by
  rintro ⟨a, b, c, hab, hbc⟩
  exact mixedUnpaidChild_not_parent
    C exponent hab hbc

#print axioms mixedUnpaidChildren_family_pairwiseDisjoint
#print axioms mixedUnpaidChildren_kraft_branch_any
#print axioms allMixedUnpaidChildren_weight_eq_double_sum
#print axioms two_mul_allMixedUnpaidChildren_weight_le_total
#print axioms no_two_step_mixedUnpaidChild

end OrderedEdgeColoring
end JSP000404Research
