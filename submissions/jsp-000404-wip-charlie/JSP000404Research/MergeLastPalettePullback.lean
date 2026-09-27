import JSP000404Research.LastMergeActiveExact
import Mathlib.Tactic

/-!
# Pulling equal merged palettes back through the last 0/n quotient

The map mergeLastColor is globally injective except for the single collision

  old 0  ~  old n.

Therefore, if two old active palettes each avoid containing both boundary
colours and their merged images are equal, then all interior old colours agree
exactly.  The two palettes can differ only by choosing opposite representatives
of the merged boundary colour.
-/

namespace JSP000404Research
namespace BinaryEdgePartition

theorem mergeLastColor_eq_implies_eq_of_positive_lt_last
    {n : ℕ}
    (hn : 1 ≤ n)
    {a b : Fin (n + 1)}
    (ha0 : 0 < a.val)
    (haN : a.val < n)
    (hEq : mergeLastColor hn a = mergeLastColor hn b) :
    a = b := by
  by_cases hbN : b.val < n
  · apply Fin.ext
    have hv := congrArg Fin.val hEq
    simp [mergeLastColor, haN, hbN] at hv
    exact hv
  · have hbEq : b = Fin.last n := by
      apply Fin.ext
      simp
      have hbLe : b.val ≤ n := by omega
      omega
    subst b
    have hv := congrArg Fin.val hEq
    simp [mergeLastColor, haN] at hv
    omega

theorem interior_mem_iff_of_equal_merge_image
    {n : ℕ}
    (hn : 1 ≤ n)
    (S T : Finset (Fin (n + 1)))
    (himage :
      S.image (mergeLastColor hn) =
        T.image (mergeLastColor hn))
    (a : Fin (n + 1))
    (ha0 : 0 < a.val)
    (haN : a.val < n) :
    a ∈ S ↔ a ∈ T := by
  classical
  constructor
  · intro haS
    have hma :
        mergeLastColor hn a ∈
          T.image (mergeLastColor hn) := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨a, haS, rfl⟩
    obtain ⟨b, hbT, hba⟩ :=
      Finset.mem_image.mp hma
    have hab :
        a = b :=
      mergeLastColor_eq_implies_eq_of_positive_lt_last
        hn ha0 haN hba.symm
    simpa [hab] using hbT
  · intro haT
    have hma :
        mergeLastColor hn a ∈
          S.image (mergeLastColor hn) := by
      rw [himage]
      exact Finset.mem_image.mpr ⟨a, haT, rfl⟩
    obtain ⟨b, hbS, hba⟩ :=
      Finset.mem_image.mp hma
    have hab :
        a = b :=
      mergeLastColor_eq_implies_eq_of_positive_lt_last
        hn ha0 haN hba.symm
    simpa [hab] using hbS

theorem merged_zero_mem_image_iff_boundary
    {n : ℕ}
    (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1))) :
    (0 : Fin n) ∈ S.image (mergeLastColor hn)
      ↔
    (0 : Fin (n + 1)) ∈ S ∨ Fin.last n ∈ S := by
  classical
  constructor
  · intro h
    obtain ⟨a, haS, ha0⟩ :=
      Finset.mem_image.mp h
    by_cases haN : a.val < n
    · have hv := congrArg Fin.val ha0
      simp [mergeLastColor, haN] at hv
      have haZero : a = (0 : Fin (n + 1)) := by
        apply Fin.ext
        exact hv
      exact Or.inl (by simpa [haZero] using haS)
    · have haLast : a = Fin.last n := by
        apply Fin.ext
        simp
        have haLe : a.val ≤ n := by omega
        omega
      exact Or.inr (by simpa [haLast] using haS)
  · intro h
    rcases h with h0 | hnS
    · apply Finset.mem_image.mpr
      refine ⟨(0 : Fin (n + 1)), h0, ?_⟩
      simp [mergeLastColor, hn]
    · apply Finset.mem_image.mpr
      refine ⟨Fin.last n, hnS, ?_⟩
      simp [mergeLastColor]

theorem boundary_union_iff_of_equal_merge_image
    {n : ℕ}
    (hn : 1 ≤ n)
    (S T : Finset (Fin (n + 1)))
    (himage :
      S.image (mergeLastColor hn) =
        T.image (mergeLastColor hn)) :
    ((0 : Fin (n + 1)) ∈ S ∨ Fin.last n ∈ S)
      ↔
    ((0 : Fin (n + 1)) ∈ T ∨ Fin.last n ∈ T) := by
  rw [← merged_zero_mem_image_iff_boundary hn S,
      ← merged_zero_mem_image_iff_boundary hn T,
      himage]

/-- If neither old palette contains both boundary colours, equal merged images
make the old palettes equal away from the single 0/n representative choice. -/
theorem equal_merge_image_old_palettes_differ_only_boundary
    {n : ℕ}
    (hn : 1 ≤ n)
    (S T : Finset (Fin (n + 1)))
    (hSboundary :
      ¬ ((0 : Fin (n + 1)) ∈ S ∧ Fin.last n ∈ S))
    (hTboundary :
      ¬ ((0 : Fin (n + 1)) ∈ T ∧ Fin.last n ∈ T))
    (himage :
      S.image (mergeLastColor hn) =
        T.image (mergeLastColor hn)) :
    (∀ a : Fin (n + 1),
      0 < a.val → a.val < n →
      (a ∈ S ↔ a ∈ T))
      ∧
    (((0 : Fin (n + 1)) ∈ S ∨ Fin.last n ∈ S)
      ↔
     ((0 : Fin (n + 1)) ∈ T ∨ Fin.last n ∈ T))
      ∧
    (
      S = T
      ∨
      (
        (0 : Fin (n + 1)) ∈ S ∧
        Fin.last n ∉ S ∧
        (0 : Fin (n + 1)) ∉ T ∧
        Fin.last n ∈ T
      )
      ∨
      (
        (0 : Fin (n + 1)) ∉ S ∧
        Fin.last n ∈ S ∧
        (0 : Fin (n + 1)) ∈ T ∧
        Fin.last n ∉ T
      )
    ) := by
  classical
  have hinterior :
      ∀ a : Fin (n + 1),
        0 < a.val → a.val < n →
        (a ∈ S ↔ a ∈ T) :=
    fun a ha0 haN =>
      interior_mem_iff_of_equal_merge_image
        hn S T himage a ha0 haN
  have hboundary :=
    boundary_union_iff_of_equal_merge_image
      hn S T himage
  refine ⟨hinterior, hboundary, ?_⟩
  by_cases h0S : (0 : Fin (n + 1)) ∈ S
  · by_cases hnS : Fin.last n ∈ S
    · exact False.elim (hSboundary ⟨h0S, hnS⟩)
    · have hTsome :
          (0 : Fin (n + 1)) ∈ T ∨ Fin.last n ∈ T :=
        hboundary.mp (Or.inl h0S)
      rcases hTsome with h0T | hnT
      · left
        ext a
        by_cases ha0 : a.val = 0
        · have haZero : a = (0 : Fin (n + 1)) := Fin.ext ha0
          subst a
          simp [h0S, h0T]
        · by_cases haN : a.val = n
          · have haLast : a = Fin.last n := by
              apply Fin.ext
              simpa using haN
            subst a
            simp [hnS]
            exact not_congr (not_congr? )
          · have hapos : 0 < a.val := by omega
            have halt : a.val < n := by
              have hale : a.val ≤ n := by omega
              omega
            exact propext (hinterior a hapos halt)
      · right
        left
        have h0T : (0 : Fin (n + 1)) ∉ T := by
          intro h
          exact hTboundary ⟨h, hnT⟩
        exact ⟨h0S, hnS, h0T, hnT⟩
  · by_cases hnS : Fin.last n ∈ S
    · have hTsome :
          (0 : Fin (n + 1)) ∈ T ∨ Fin.last n ∈ T :=
        hboundary.mp (Or.inr hnS)
      rcases hTsome with h0T | hnT
      · right
        right
        have hnTnot : Fin.last n ∉ T := by
          intro h
          exact hTboundary ⟨h0T, h⟩
        exact ⟨h0S, hnS, h0T, hnTnot⟩
      · left
        ext a
        by_cases ha0 : a.val = 0
        · have haZero : a = (0 : Fin (n + 1)) := Fin.ext ha0
          subst a
          simp [h0S]
          have h0Tnot : (0 : Fin (n + 1)) ∉ T := by
            intro h
            exact hTboundary ⟨h, hnT⟩
          simp [h0Tnot]
        · by_cases haN : a.val = n
          · have haLast : a = Fin.last n := by
              apply Fin.ext
              simpa using haN
            subst a
            simp [hnS, hnT]
          · have hapos : 0 < a.val := by omega
            have halt : a.val < n := by
              have hale : a.val ≤ n := by omega
              omega
            exact propext (hinterior a hapos halt)
    · have hTnone :
          (0 : Fin (n + 1)) ∉ T ∧ Fin.last n ∉ T := by
        have hnot :
            ¬ ((0 : Fin (n + 1)) ∈ T ∨ Fin.last n ∈ T) := by
          intro h
          have := hboundary.mpr h
          exact this.elim h0S hnS
        push_neg at hnot
        exact hnot
      left
      ext a
      by_cases ha0 : a.val = 0
      · have haZero : a = (0 : Fin (n + 1)) := Fin.ext ha0
        subst a
        simp [h0S, hTnone.1]
      · by_cases haN : a.val = n
        · have haLast : a = Fin.last n := by
            apply Fin.ext
            simpa using haN
          subst a
          simp [hnS, hTnone.2]
        · have hapos : 0 < a.val := by omega
          have halt : a.val < n := by
            have hale : a.val ≤ n := by omega
            omega
          exact propext (hinterior a hapos halt)

#print axioms mergeLastColor_eq_implies_eq_of_positive_lt_last
#print axioms interior_mem_iff_of_equal_merge_image
#print axioms merged_zero_mem_image_iff_boundary
#print axioms equal_merge_image_old_palettes_differ_only_boundary

end BinaryEdgePartition
end JSP000404Research
