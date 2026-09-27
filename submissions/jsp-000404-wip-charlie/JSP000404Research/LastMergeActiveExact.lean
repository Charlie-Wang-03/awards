import JSP000404Research.ProjectiveBandLastMergeCapacity
import Mathlib.Tactic

/-!
# Exact active palette under the last 0/n merge

The existing last-merge module only needed the one-sided inclusion

  active(merged,v) subset image(active(old,v)).

For equality terminals it is useful to retain the converse as well.  Every old
active colour is witnessed by an incident edge, and that same edge survives
with exactly the merged colour.  Hence the active set is exactly the image.

The quotient map identifies only old colours 0 and n.  Therefore on any local
palette which does not contain both boundary colours, the merge is injective
and preserves active cardinality exactly.

This is the local no-hidden-collision interface for saturation-bad centres.
-/

namespace JSP000404Research
namespace BinaryEdgePartition

theorem mergeLastPartition_active_eq_image
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V) :
    active (mergeLastPartition hn P wrapBit hwrap) v =
      (active P v).image (mergeLastColor hn) := by
  classical
  apply Finset.Subset.antisymm
  · exact mergeLastPartition_active_subset_image
      hn P wrapBit hwrap v
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    simp only [active, Finset.mem_filter,
      Finset.mem_univ, true_and] at hd ⊢
    rcases hd with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
    · left
      refine ⟨a, hav, ?_⟩
      simp [mergeLastPartition, hcol]
    · right
      refine ⟨w, hvw, ?_⟩
      simp [mergeLastPartition, hcol]

theorem mergeLastColor_injOn_of_not_both_boundary
    {n : ℕ}
    (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1)))
    (hboundary :
      ¬ ((0 : Fin (n + 1)) ∈ S ∧
         Fin.last n ∈ S)) :
    Set.InjOn (mergeLastColor hn) S := by
  intro a haS b hbS hab
  by_cases ha : a.val < n
  · by_cases hb : b.val < n
    · apply Fin.ext
      have hv := congrArg Fin.val hab
      simpa [mergeLastColor, ha, hb] using hv
    · have hbEq : b = Fin.last n := by
        apply Fin.ext
        simp
        have hble : b.val ≤ n := by omega
        omega
      have haZero : a = (0 : Fin (n + 1)) := by
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simp [mergeLastColor, ha, hb] at hv
        exact hv
      exfalso
      apply hboundary
      exact ⟨by simpa [haZero] using haS,
        by simpa [hbEq] using hbS⟩
  · by_cases hb : b.val < n
    · have haEq : a = Fin.last n := by
        apply Fin.ext
        simp
        have hale : a.val ≤ n := by omega
        omega
      have hbZero : b = (0 : Fin (n + 1)) := by
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simp [mergeLastColor, ha, hb] at hv
        exact hv.symm
      exfalso
      apply hboundary
      exact ⟨by simpa [hbZero] using hbS,
        by simpa [haEq] using haS⟩
    · apply Fin.ext
      have hale : a.val ≤ n := by omega
      have hble : b.val ≤ n := by omega
      omega

theorem mergeLastPartition_active_card_eq_of_not_both_boundary
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V)
    (hboundary :
      ¬ ((0 : Fin (n + 1)) ∈ active P v ∧
         Fin.last n ∈ active P v)) :
    (active (mergeLastPartition hn P wrapBit hwrap) v).card =
      (active P v).card := by
  rw [mergeLastPartition_active_eq_image
      hn P wrapBit hwrap v]
  exact Finset.card_image_iff.mpr
    (mergeLastColor_injOn_of_not_both_boundary
      hn (active P v) hboundary)

#print axioms mergeLastPartition_active_eq_image
#print axioms mergeLastColor_injOn_of_not_both_boundary
#print axioms mergeLastPartition_active_card_eq_of_not_both_boundary

end BinaryEdgePartition
end JSP000404Research
