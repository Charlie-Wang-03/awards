
import JSP000404Research.ResidualMixedOverlapPayment
import JSP000404Research.ResidualCompletionMultiplicity
import JSP000404Research.CompensatedDeletion
import Mathlib.Tactic

/-!
# Mixed unpaid overlaps form a Kraft containment forest

A mixed unpaid overlap has one projected-budget saturated endpoint (the
"parent") and one strict endpoint (the "child").  The strict endpoint's own
profile surplus is insufficient to pay the overlap.

ResidualMixedOverlapPayment proves two crucial facts:

* the entire retained completion cube of the child is contained in the
  parent's completion cube;
* the target exponent strictly decreases from parent to child.

This file packages those mixed hard carriers as a directed relation and proves
the forest/Kraft properties.

1. A child has at most one parent.  Otherwise one word of the child cube would
   lie in three distinct retained completion cubes, contradicting completion
   multiplicity at most two.

2. Distinct children of one parent have disjoint completion cubes, by the same
   three-cube obstruction.

3. Each strict child satisfies

     2 * 2^k(child) <= card(Q_child),

   because k(child) < projectedFree(child).

4. Since the child cubes are disjoint and all sit inside Q_parent,

     2 * sum_child 2^k(child)
       <= card(Q_parent)
       = 2^k(parent)

   for a saturated parent.

Thus the mixed unpaid remainder is not an arbitrary charging graph: it is a
genuine Kraft-descending forest with a sharp binary branching inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

def MixedUnpaidChild
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent child : V) : Prop :=
  parent ≠ child ∧
  ExactProjectedBudget C exponent parent ∧
  exponent child < projectedFree C child ∧
  ∃ base : Fin n → Bool,
    base ∈ retainedCompletionWords C parent ∧
    base ∈ retainedCompletionWords C child ∧
    ¬ ((retainedCompletionWords C parent ∩
          retainedCompletionWords C child).card
        ≤ dyadicProfileSurplus exponent (projectedFree C) child)

theorem mixedUnpaidChild_ne
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    {exponent : V → ℕ} {parent child : V}
    (h : MixedUnpaidChild C exponent parent child) :
    parent ≠ child :=
  h.1

theorem mixedUnpaidChild_parent_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    {exponent : V → ℕ} {parent child : V}
    (h : MixedUnpaidChild C exponent parent child) :
    ExactProjectedBudget C exponent parent :=
  h.2.1

theorem mixedUnpaidChild_child_strict
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    {exponent : V → ℕ} {parent child : V}
    (h : MixedUnpaidChild C exponent parent child) :
    exponent child < projectedFree C child :=
  h.2.2.1

theorem mixedUnpaidChild_cube_subset
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {parent child : V}
    (h : MixedUnpaidChild C exponent parent child) :
    retainedCompletionWords C child ⊆
      retainedCompletionWords C parent := by
  obtain ⟨_hne, _hsat, hstrict, base,
      hbaseP, hbaseC, hunpaid⟩ := h
  exact retainedCompletionWords_subset_of_mixed_unpaid
    C exponent hbaseP hbaseC hstrict hunpaid

/-- Mixed unpaid edges strictly decrease the Sendov target exponent. -/
theorem mixedUnpaidChild_exponent_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {parent child : V}
    (h : MixedUnpaidChild C exponent parent child) :
    exponent child < exponent parent := by
  obtain ⟨_hne, hsat, hstrict, base,
      hbaseP, hbaseC, hunpaid⟩ := h
  exact exponent_strictly_descends_on_mixed_unpaid
    C exponent hbaseP hbaseC hsat hstrict hunpaid

/-- A strict child can have at most one mixed-unpaid parent. -/
theorem mixedUnpaidChild_parent_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p q child : V}
    (hp : MixedUnpaidChild C exponent p child)
    (hq : MixedUnpaidChild C exponent q child) :
    p = q := by
  by_contra hpq
  obtain ⟨hpNe, _hpSat, _hcStrict, base,
      hpBase, hcBase, _hpUnpaid⟩ := hp
  have hqSub :
      retainedCompletionWords C child ⊆
        retainedCompletionWords C q :=
    mixedUnpaidChild_cube_subset C exponent hq
  have hqBase :
      base ∈ retainedCompletionWords C q :=
    hqSub hcBase
  have hqc : q ≠ child :=
    mixedUnpaidChild_ne hq
  exact no_three_distinct_share_retained_completion
    C hpNe hpq hqc.symm
    hpBase hcBase hqBase

noncomputable def mixedUnpaidChildren
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent : V) : Finset V := by
  classical
  exact Finset.univ.filter fun child =>
    MixedUnpaidChild C exponent parent child

@[simp] theorem mem_mixedUnpaidChildren
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent child : V) :
    child ∈ mixedUnpaidChildren C exponent parent ↔
      MixedUnpaidChild C exponent parent child := by
  classical
  simp [mixedUnpaidChildren]

/-- Distinct mixed-unpaid children of one parent have disjoint completion
cubes. -/
theorem mixedUnpaidChildren_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent : V) :
    ((mixedUnpaidChildren C exponent parent : Finset V) : Set V).PairwiseDisjoint
      (retainedCompletionWords C) := by
  intro a ha b hb hab
  classical
  rw [Finset.disjoint_left]
  intro word hwa hwb
  have haRel :
      MixedUnpaidChild C exponent parent a :=
    (mem_mixedUnpaidChildren C exponent parent a).1 ha
  have hbRel :
      MixedUnpaidChild C exponent parent b :=
    (mem_mixedUnpaidChildren C exponent parent b).1 hb
  have hpa :
      parent ≠ a :=
    mixedUnpaidChild_ne haRel
  have hpb :
      parent ≠ b :=
    mixedUnpaidChild_ne hbRel
  have hparent :
      word ∈ retainedCompletionWords C parent :=
    (mixedUnpaidChild_cube_subset
      C exponent haRel) hwa
  exact no_three_distinct_share_retained_completion
    C hpa hpb hab
    hparent hwa hwb

/-- The union of all mixed-unpaid child cubes lies inside the parent cube. -/
theorem mixedUnpaidChildren_biUnion_subset_parent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent : V) :
    (mixedUnpaidChildren C exponent parent).biUnion
        (retainedCompletionWords C)
      ⊆
    retainedCompletionWords C parent := by
  classical
  intro word hword
  obtain ⟨child, hchild, hwChild⟩ :=
    Finset.mem_biUnion.mp hword
  have hrel :
      MixedUnpaidChild C exponent parent child :=
    (mem_mixedUnpaidChildren C exponent parent child).1 hchild
  exact mixedUnpaidChild_cube_subset
    C exponent hrel hwChild

/-- One strict child uses at most half of its projected completion cube. -/
theorem two_mul_child_weight_le_completion_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {parent child : V}
    (h : MixedUnpaidChild C exponent parent child) :
    2 * 2 ^ exponent child ≤
      (retainedCompletionWords C child).card := by
  rw [retainedCompletionWords_card]
  exact two_mul_pow_le_pow_of_succ_le
    (by
      have hs :=
        mixedUnpaidChild_child_strict h
      omega)

/-- Total completion mass of the children fits inside the parent completion
cube. -/
theorem mixedUnpaidChildren_completion_mass_le_parent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent : V) :
    (∑ child ∈ mixedUnpaidChildren C exponent parent,
        (retainedCompletionWords C child).card)
      ≤
    (retainedCompletionWords C parent).card := by
  classical
  have hcardUnion :
      ((mixedUnpaidChildren C exponent parent).biUnion
          (retainedCompletionWords C)).card
        =
      ∑ child ∈ mixedUnpaidChildren C exponent parent,
        (retainedCompletionWords C child).card := by
    rw [Finset.card_biUnion
      (mixedUnpaidChildren_pairwiseDisjoint
        C exponent parent)]
  have hsub :=
    mixedUnpaidChildren_biUnion_subset_parent
      C exponent parent
  have hle :
      ((mixedUnpaidChildren C exponent parent).biUnion
          (retainedCompletionWords C)).card
        ≤
      (retainedCompletionWords C parent).card :=
    Finset.card_le_card hsub
  rw [hcardUnion] at hle
  exact hle

/-- Sharp Kraft branching inequality for all mixed-unpaid children of one
saturated parent. -/
theorem mixedUnpaidChildren_kraft_branch
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (parent : V)
    (hsat : ExactProjectedBudget C exponent parent) :
    2 * (∑ child ∈ mixedUnpaidChildren C exponent parent,
      2 ^ exponent child)
      ≤
    2 ^ exponent parent := by
  classical
  have hsum :
      ∑ child ∈ mixedUnpaidChildren C exponent parent,
          (2 * 2 ^ exponent child)
        ≤
      ∑ child ∈ mixedUnpaidChildren C exponent parent,
          (retainedCompletionWords C child).card := by
    apply Finset.sum_le_sum
    intro child hchild
    exact two_mul_child_weight_le_completion_card
      C exponent
      ((mem_mixedUnpaidChildren C exponent parent child).1 hchild)
  have hmass :=
    mixedUnpaidChildren_completion_mass_le_parent
      C exponent parent
  rw [← Finset.mul_sum] at hsum
  have hparentCard :
      (retainedCompletionWords C parent).card =
        2 ^ exponent parent := by
    rw [retainedCompletionWords_card, hsat]
  rw [hparentCard] at hmass
  exact hsum.trans hmass

#print axioms mixedUnpaidChild_parent_unique
#print axioms mixedUnpaidChildren_pairwiseDisjoint
#print axioms mixedUnpaidChildren_completion_mass_le_parent
#print axioms mixedUnpaidChildren_kraft_branch

end OrderedEdgeColoring
end JSP000404Research
