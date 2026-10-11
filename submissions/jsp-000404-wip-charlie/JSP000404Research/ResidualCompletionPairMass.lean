import JSP000404Research.ResidualCompletionPairAllocation
import Mathlib.Tactic

/-!
# Exact residual-edge allocation of global completion overlap mass

For each ordered residual edge u<v, record the intersection Q_u ∩ Q_v.
Every word in the global overlap set belongs to exactly one such
ordered residual edge, and distinct edges' intersection sets are disjoint.

Hence overlap mass is a sum of pairwise cube-intersection masses.
This is a certified global NO-DOUBLE-COUNT decomposition; it does NOT
by itself bound overlaps against holes, surplus or profile losses.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The finite set of ordered residual edges (including edges whose
completion intersections happen to be empty). -/
noncomputable def retainedOverlapEdges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter
    (fun q => q.1 < q.2 ∧ IsResidual C q.1 q.2)

@[simp] theorem mem_retainedOverlapEdges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (u,v) ∈ retainedOverlapEdges C ↔
      u < v ∧ IsResidual C u v := by
  classical
  simp [retainedOverlapEdges]

/-- Two covering vertices imply the word is counted exactly twice.
The key is the existing pointwise multiplicity ≤ 2. -/
theorem mem_overlapCompletionWords_of_pair_completion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u ≠ v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    word ∈ overlapCompletionWords C := by
  classical
  have huF : u ∈ completionFibre C word :=
    (mem_completionFibre C word u).2 hu
  have hvF : v ∈ completionFibre C word :=
    (mem_completionFibre C word v).2 hv
  have hsub : ({u,v} : Finset V) ⊆ completionFibre C word := by
    intro w hw
    rcases Finset.mem_insert.mp hw with heq | htail
    · simpa [heq] using huF
    · have h : w = v := Finset.mem_singleton.mp htail
      simpa [h] using hvF
  have hpair : ({u,v} : Finset V).card = 2 := by
    simp [huv]
  have hlow : 2 ≤ (completionFibre C word).card := by
    have hc := Finset.card_le_card hsub
    omega
  have hhigh := completionFibre_card_le_two C word
  exact (mem_overlapCompletionWords C word).2 (by omega)

/-- Every doubly covered Boolean word is covered by an increasing
pair of vertices connected by a residual edge. -/
theorem overlap_word_has_unique_residual_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C) :
    ∃ u v : V,
      u < v ∧ IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      (∀ a b : V, a < b →
        word ∈ retainedCompletionWords C a →
        word ∈ retainedCompletionWords C b →
        a = u ∧ b = v) := by
  classical
  have hcard :
      (completionFibre C word).card = 2 :=
    (mem_overlapCompletionWords C word).1 hoverlap
  obtain ⟨x,y,hxy,heq⟩ := Finset.card_eq_two.mp hcard
  have hx : word ∈ retainedCompletionWords C x := by
    apply (mem_completionFibre C word x).1
    rw [heq]
    simp
  have hy : word ∈ retainedCompletionWords C y := by
    apply (mem_completionFibre C word y).1
    rw [heq]
    simp
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · refine ⟨x,y,hlt,
      isResidual_of_retainedCompletion_overlap_lt C hlt hx hy,
      hx,hy,?_⟩
    intro a b hab ha hb
    have h := completion_word_unique_ordered_pair
      C hlt hab hx hy ha hb
    exact ⟨h.1.symm, h.2.symm⟩
  · refine ⟨y,x,hgt,
      isResidual_of_retainedCompletion_overlap_lt C hgt hy hx,
      hy,hx,?_⟩
    intro a b hab ha hb
    have h := completion_word_unique_ordered_pair
      C hgt hab hy hx ha hb
    exact ⟨h.1.symm, h.2.symm⟩

/-- Global overlap words are EXACTLY the union of residual edge
completion intersections; pair ownership is unique. -/
theorem overlapCompletionWords_eq_residualEdge_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C =
      (retainedOverlapEdges C).biUnion
        (fun q => retainedCompletionWords C q.1 ∩
          retainedCompletionWords C q.2) := by
  classical
  ext word
  constructor
  · intro hw
    obtain ⟨u,v,huv,hres,hu,hv,_hunique⟩ :=
      overlap_word_has_unique_residual_pair C hw
    apply Finset.mem_biUnion.mpr
    refine ⟨(u,v), ?_, ?_⟩
    · exact (mem_retainedOverlapEdges C u v).2 ⟨huv,hres⟩
    · exact Finset.mem_inter.mpr ⟨hu,hv⟩
  · intro hw
    obtain ⟨q,hq,hwq⟩ := Finset.mem_biUnion.mp hw
    exact mem_overlapCompletionWords_of_pair_completion
      C (ne_of_lt ((mem_retainedOverlapEdges C q.1 q.2).1 hq).1)
      (Finset.mem_inter.mp hwq).1
      (Finset.mem_inter.mp hwq).2

/-- The residual-edge completion intersections are pairwise disjoint,
so the global overlap mass is exactly their sum. -/
theorem overlapCompletionWords_card_eq_sum_residualEdge_intersections
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      ∑ q ∈ retainedOverlapEdges C,
        (retainedCompletionWords C q.1 ∩
          retainedCompletionWords C q.2).card := by
  classical
  rw [overlapCompletionWords_eq_residualEdge_union]
  apply Finset.card_biUnion
  intro q hq r hr hqr
  have hqord : q.1 < q.2 :=
    ((mem_retainedOverlapEdges C q.1 q.2).1 hq).1
  have hrord : r.1 < r.2 :=
    ((mem_retainedOverlapEdges C r.1 r.2).1 hr).1
  have hdiff : q.1 ≠ r.1 ∨ q.2 ≠ r.2 := by
    by_contra h
    push Not at h
    exact hqr (Prod.ext h.1 h.2)
  exact retained_completion_pair_intersections_disjoint
    C hqord hrord hdiff

#print axioms mem_overlapCompletionWords_of_pair_completion
#print axioms overlap_word_has_unique_residual_pair
#print axioms overlapCompletionWords_eq_residualEdge_union
#print axioms overlapCompletionWords_card_eq_sum_residualEdge_intersections

end OrderedEdgeColoring
end JSP000404Research
