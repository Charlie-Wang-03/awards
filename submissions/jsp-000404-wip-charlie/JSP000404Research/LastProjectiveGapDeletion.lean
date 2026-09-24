import JSP000404Research.MiddleProjectiveGapDeletion
import Mathlib.Tactic

/-!
# Deleting the last angle from a sorted projective angle list

Write the parent angle list as

  a :: (pre ++ [x]),

with prev = pre.getLastD a.

The two cyclic gaps adjacent to x are

  x-prev
  a+pi-x.

After deleting x they merge into the child wrap gap

  a+pi-prev.

Thus the last-position case is again one binary floor merge, and positivity of
both adjacent parent quotients gives one full exponent unit of deletion gain.
-/

namespace JSP000404Research

open Real

theorem projectiveGaps_last_parent_decompose
    (a : ℝ) (pre : List ℝ) (x : ℝ) :
    projectiveGaps (a :: (pre ++ [x])) =
      successiveDiffsFrom a pre ++
        [x - pre.getLastD a,
         a + Real.pi - x] := by
  rw [projectiveGaps]
  rw [successiveDiffsFrom_append_general
      a pre [x]]
  simp [successiveDiffsFrom,
    getLastD_append_general, List.getLastD_cons,
    List.append_assoc]

theorem projectiveGaps_last_child_decompose
    (a : ℝ) (pre : List ℝ) :
    projectiveGaps (a :: pre) =
      successiveDiffsFrom a pre ++
        [a + Real.pi - pre.getLastD a] := by
  rfl

theorem normalizedProjectiveGaps_last_parent
    (a : ℝ) (pre : List ℝ) (x : ℝ) :
    normalizedProjectiveGaps
        (a :: (pre ++ [x]))
      =
    normalizedPrefixGaps a pre ++
      [(x - pre.getLastD a) / Real.pi,
       (a + Real.pi - x) / Real.pi] := by
  rw [normalizedProjectiveGaps,
      projectiveGaps_last_parent_decompose]
  simp [normalizedPrefixGaps, List.map_append]

theorem normalizedProjectiveGaps_last_child
    (a : ℝ) (pre : List ℝ) (x : ℝ) :
    normalizedProjectiveGaps (a :: pre)
      =
    normalizedPrefixGaps a pre ++
      [((x - pre.getLastD a) / Real.pi) +
       ((a + Real.pi - x) / Real.pi)] := by
  have hlocal :
      (a + Real.pi - pre.getLastD a) / Real.pi =
        ((x - pre.getLastD a) / Real.pi) +
          ((a + Real.pi - x) / Real.pi) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [normalizedProjectiveGaps,
      projectiveGaps_last_child_decompose]
  simp [normalizedPrefixGaps, List.map_append, hlocal]

theorem quotientList_delete_last
    {t a x : ℝ} {pre : List ℝ}
    (ht : 0 ≤ t)
    (hgLeft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hgWrap :
      0 ≤ (a + Real.pi - x) / Real.pi) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ [x])))
        =
      quotientList t (normalizedPrefixGaps a pre) ++
        [Nat.floor
            (t * ((x - pre.getLastD a) / Real.pi)),
         Nat.floor
            (t * ((a + Real.pi - x) / Real.pi))] ∧
      quotientList t
          (normalizedProjectiveGaps (a :: pre))
        =
      quotientList t (normalizedPrefixGaps a pre) ++
        [Nat.floor
            (t * ((x - pre.getLastD a) / Real.pi)) +
         Nat.floor
            (t * ((a + Real.pi - x) / Real.pi)) + carry] := by
  obtain ⟨carry, hcarry, hmerge⟩ :=
    natFloor_scaled_gap_merge
      ht hgLeft hgWrap
  refine ⟨carry, hcarry, ?_, ?_⟩
  · rw [normalizedProjectiveGaps_last_parent]
    simp [quotientList, List.map_append]
  · rw [normalizedProjectiveGaps_last_child]
    simp only [quotientList, List.map_append,
      List.map_cons, List.map_nil]
    rw [hmerge]

theorem listExponent_gain_delete_last
    {t a x : ℝ} {pre : List ℝ}
    (ht : 0 ≤ t)
    (hgLeft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hgWrap :
      0 ≤ (a + Real.pi - x) / Real.pi)
    (hLeft :
      1 ≤ Nat.floor
        (t * ((x - pre.getLastD a) / Real.pi)))
    (hWrap :
      1 ≤ Nat.floor
        (t * ((a + Real.pi - x) / Real.pi))) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ [x])))) + 1
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: pre))) := by
  obtain ⟨carry, _hcarry, hparent, hchild⟩ :=
    quotientList_delete_last
      ht hgLeft hgWrap
  let prefix :=
    quotientList t (normalizedPrefixGaps a pre)
  let qLeft :=
    Nat.floor
      (t * ((x - pre.getLastD a) / Real.pi))
  let qWrap :=
    Nat.floor
      (t * ((a + Real.pi - x) / Real.pi))
  have hp :
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ [x])))
        =
      prefix ++ [qLeft, qWrap] := by
    simpa [prefix, qLeft, qWrap] using hparent
  have hc :
      quotientList t
          (normalizedProjectiveGaps (a :: pre))
        =
      prefix ++ [qLeft + qWrap + carry] := by
    simpa [prefix, qLeft, qWrap] using hchild
  rw [hp, hc, listExponent_append,
      listExponent_append]
  simp only [listExponent, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hlocal :=
    excess_merge_gain_of_both_pos
      (a := qLeft) (b := qWrap) (c := carry)
      (by simpa [qLeft] using hLeft)
      (by simpa [qWrap] using hWrap)
  omega

#print axioms projectiveGaps_last_parent_decompose
#print axioms projectiveGaps_last_child_decompose
#print axioms quotientList_delete_last
#print axioms listExponent_gain_delete_last

end JSP000404Research
