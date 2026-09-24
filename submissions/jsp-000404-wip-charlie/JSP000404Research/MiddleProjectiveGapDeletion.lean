import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.PinnedCyclicDeletionGain
import JSP000404Research.FloorMergeCarry
import Mathlib.Tactic

/-!
# Deleting an interior angle from a sorted projective angle list

The arbitrary-position deletion problem has three list cases: first, interior,
and last.  The first case was already formalized in GeneralProjectiveGapDeletion.

This file handles the main interior case.

Write the parent angle list as

  a :: (pre ++ x :: y :: tail),

so x is the deleted angle, y is its successor, and

  prev = pre.getLastD a

is its predecessor.

Then the parent physical cyclic gaps decompose as

  prefix ++ [x-prev, y-x] ++ suffix ++ [wrap],

while the child list obtained by deleting x has gaps

  prefix ++ [y-prev] ++ suffix ++ [wrap].

Thus only two adjacent gaps merge.  At the normalized/floor level the usual
binary floor carry applies.
-/

namespace JSP000404Research

open Real

theorem getLastD_append_general
    {α : Type*}
    (xs ys : List α) (a : α) :
    (xs ++ ys).getLastD a =
      ys.getLastD (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp [List.getLastD_nil]
  | cons x xs ih =>
      simpa [List.getLastD_cons] using ih (a := x)

theorem successiveDiffsFrom_append_general
    (a : ℝ) (xs ys : List ℝ) :
    successiveDiffsFrom a (xs ++ ys) =
      successiveDiffsFrom a xs ++
        successiveDiffsFrom (xs.getLastD a) ys := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom, List.getLastD_nil]
  | cons x xs ih =>
      simp [successiveDiffsFrom, ih]

theorem projectiveGaps_interior_parent_decompose
    (a : ℝ) (pre : List ℝ) (x y : ℝ) (tail : List ℝ) :
    projectiveGaps (a :: (pre ++ x :: y :: tail)) =
      successiveDiffsFrom a pre ++
        [x - pre.getLastD a, y - x] ++
        successiveDiffsFrom y tail ++
        [a + Real.pi - tail.getLastD y] := by
  rw [projectiveGaps]
  rw [successiveDiffsFrom_append_general
      a pre (x :: y :: tail)]
  simp only [successiveDiffsFrom, List.append_assoc,
    getLastD_append_general, List.getLastD_cons]
  rfl

theorem projectiveGaps_interior_child_decompose
    (a : ℝ) (pre : List ℝ) (y : ℝ) (tail : List ℝ) :
    projectiveGaps (a :: (pre ++ y :: tail)) =
      successiveDiffsFrom a pre ++
        [y - pre.getLastD a] ++
        successiveDiffsFrom y tail ++
        [a + Real.pi - tail.getLastD y] := by
  rw [projectiveGaps]
  rw [successiveDiffsFrom_append_general
      a pre (y :: tail)]
  simp only [successiveDiffsFrom, List.append_assoc,
    getLastD_append_general, List.getLastD_cons]
  rfl

def normalizedPrefixGaps
    (a : ℝ) (pre : List ℝ) : List ℝ :=
  (successiveDiffsFrom a pre).map
    (fun d => d / Real.pi)

def normalizedSuffixGaps
    (y : ℝ) (tail : List ℝ) : List ℝ :=
  (successiveDiffsFrom y tail).map
    (fun d => d / Real.pi)

/-- Exact normalized parent decomposition around an interior deleted angle. -/
theorem normalizedProjectiveGaps_interior_parent
    (a : ℝ) (pre : List ℝ) (x y : ℝ) (tail : List ℝ) :
    normalizedProjectiveGaps
        (a :: (pre ++ x :: y :: tail))
      =
    normalizedPrefixGaps a pre ++
      [(x - pre.getLastD a) / Real.pi,
       (y - x) / Real.pi] ++
      normalizedSuffixGaps y tail ++
      [(a + Real.pi - tail.getLastD y) / Real.pi] := by
  rw [normalizedProjectiveGaps,
      projectiveGaps_interior_parent_decompose]
  simp [normalizedPrefixGaps, normalizedSuffixGaps,
    List.map_append]

/-- Exact normalized child decomposition; the two local gaps merge additively. -/
theorem normalizedProjectiveGaps_interior_child
    (a : ℝ) (pre : List ℝ) (x y : ℝ) (tail : List ℝ) :
    normalizedProjectiveGaps
        (a :: (pre ++ y :: tail))
      =
    normalizedPrefixGaps a pre ++
      [((x - pre.getLastD a) / Real.pi) +
       ((y - x) / Real.pi)] ++
      normalizedSuffixGaps y tail ++
      [(a + Real.pi - tail.getLastD y) / Real.pi] := by
  have hlocal :
      (y - pre.getLastD a) / Real.pi =
        ((x - pre.getLastD a) / Real.pi) +
          ((y - x) / Real.pi) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [normalizedProjectiveGaps,
      projectiveGaps_interior_child_decompose]
  simp [normalizedPrefixGaps, normalizedSuffixGaps,
    List.map_append, hlocal]

/-- Quotient-list deletion formula for an interior angle. -/
theorem quotientList_delete_interior
    {t a x y : ℝ}
    {pre tail : List ℝ}
    (ht : 0 ≤ t)
    (hgLeft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hgRight :
      0 ≤ (y - x) / Real.pi) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ x :: y :: tail)))
        =
      quotientList t (normalizedPrefixGaps a pre) ++
        [Nat.floor
            (t * ((x - pre.getLastD a) / Real.pi)),
         Nat.floor
            (t * ((y - x) / Real.pi))] ++
        quotientList t (normalizedSuffixGaps y tail) ++
        [Nat.floor
            (t * ((a + Real.pi -
              tail.getLastD y) / Real.pi))] ∧
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ y :: tail)))
        =
      quotientList t (normalizedPrefixGaps a pre) ++
        [Nat.floor
            (t * ((x - pre.getLastD a) / Real.pi)) +
         Nat.floor
            (t * ((y - x) / Real.pi)) + carry] ++
        quotientList t (normalizedSuffixGaps y tail) ++
        [Nat.floor
            (t * ((a + Real.pi -
              tail.getLastD y) / Real.pi))] := by
  obtain ⟨carry, hcarry, hmerge⟩ :=
    natFloor_scaled_gap_merge
      ht hgLeft hgRight
  refine ⟨carry, hcarry, ?_, ?_⟩
  · rw [normalizedProjectiveGaps_interior_parent]
    simp [quotientList, List.map_append]
  · rw [normalizedProjectiveGaps_interior_child]
    simp only [quotientList, List.map_append,
      List.map_cons, List.map_nil]
    rw [hmerge]

/-- Deleting an interior angle raises list exponent by at least one whenever
both adjacent parent quotients are positive. -/
theorem listExponent_gain_delete_interior
    {t a x y : ℝ}
    {pre tail : List ℝ}
    (ht : 0 ≤ t)
    (hgLeft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hgRight :
      0 ≤ (y - x) / Real.pi)
    (hLeft :
      1 ≤ Nat.floor
        (t * ((x - pre.getLastD a) / Real.pi)))
    (hRight :
      1 ≤ Nat.floor
        (t * ((y - x) / Real.pi))) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ x :: y :: tail)))) + 1
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ y :: tail))) := by
  obtain ⟨carry, _hcarry, hparent, hchild⟩ :=
    quotientList_delete_interior
      ht hgLeft hgRight
  let prefix :=
    quotientList t (normalizedPrefixGaps a pre)
  let suffix :=
    quotientList t (normalizedSuffixGaps y tail) ++
      [Nat.floor
        (t * ((a + Real.pi - tail.getLastD y) / Real.pi))]
  let qLeft :=
    Nat.floor
      (t * ((x - pre.getLastD a) / Real.pi))
  let qRight :=
    Nat.floor
      (t * ((y - x) / Real.pi))
  have hp :
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ x :: y :: tail)))
        =
      prefix ++ [qLeft, qRight] ++ suffix := by
    simpa [prefix, suffix, qLeft, qRight,
      List.append_assoc] using hparent
  have hc :
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ y :: tail)))
        =
      prefix ++ [qLeft + qRight + carry] ++ suffix := by
    simpa [prefix, suffix, qLeft, qRight,
      List.append_assoc] using hchild
  rw [hp, hc]
  repeat rw [listExponent_append]
  simp only [listExponent, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hlocal :=
    excess_merge_gain_of_both_pos
      (a := qLeft) (b := qRight) (c := carry)
      (by simpa [qLeft] using hLeft)
      (by simpa [qRight] using hRight)
  omega

#print axioms successiveDiffsFrom_append_general
#print axioms projectiveGaps_interior_parent_decompose
#print axioms projectiveGaps_interior_child_decompose
#print axioms quotientList_delete_interior
#print axioms listExponent_gain_delete_interior

end JSP000404Research
