import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.CentreQuotientData
import JSP000404Research.FloorMergeCarry
import Mathlib.Tactic

/-!
# Deleting the first ray from an arbitrary sorted projective cycle

For a sorted nonempty angle list

  a :: b :: xs,

write the parent normalized cyclic gaps as

  gFirst :: gmid ++ [gLast],

where

  gFirst = (b-a)/pi,
  gmid   = successive gaps from b through xs,
  gLast  = (a+pi-last)/pi.

Deleting the first ray a leaves b :: xs.  Its cyclic gaps are exactly

  gmid ++ [gLast + gFirst].

At fixed nonnegative scale t, the child quotient list is therefore obtained by
merging the parent's final and first quotients with the usual binary floor
carry.  No cardinality restriction is used.
-/

namespace JSP000404Research

open Real

def normalizedSuccessiveTail
    (b : ℝ) (xs : List ℝ) : List ℝ :=
  (successiveDiffsFrom b xs).map (fun d => d / Real.pi)

theorem normalizedProjectiveGaps_cons_cons_decompose
    (a b : ℝ) (xs : List ℝ) :
    normalizedProjectiveGaps (a :: b :: xs) =
      ((b - a) / Real.pi) ::
        (normalizedSuccessiveTail b xs ++
          [(a + Real.pi - xs.getLastD b) / Real.pi]) := by
  simp [normalizedProjectiveGaps, projectiveGaps,
    successiveDiffsFrom, normalizedSuccessiveTail,
    List.map_append]

theorem normalizedProjectiveGaps_delete_first_general
    (a b : ℝ) (xs : List ℝ) :
    normalizedProjectiveGaps (b :: xs) =
      normalizedSuccessiveTail b xs ++
        [((a + Real.pi - xs.getLastD b) / Real.pi) +
          ((b - a) / Real.pi)] := by
  simp only [normalizedProjectiveGaps, projectiveGaps,
    List.map_append, List.map_singleton,
    normalizedSuccessiveTail]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Quotient-list form.  Deleting the first ray merges the parent's final and
first cyclic gaps with one binary carry. -/
theorem quotientList_delete_first_general
    {a b t : ℝ} {xs : List ℝ}
    (ht : 0 ≤ t)
    (hgFirst : 0 ≤ (b - a) / Real.pi)
    (hgLast :
      0 ≤ (a + Real.pi - xs.getLastD b) / Real.pi) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t (normalizedProjectiveGaps (a :: b :: xs)) =
        Nat.floor (t * ((b - a) / Real.pi)) ::
          ((normalizedSuccessiveTail b xs).map
            (fun g => Nat.floor (t * g)) ++
            [Nat.floor
                (t * ((a + Real.pi - xs.getLastD b) / Real.pi))]) ∧
      quotientList t (normalizedProjectiveGaps (b :: xs)) =
        (normalizedSuccessiveTail b xs).map
            (fun g => Nat.floor (t * g)) ++
          [Nat.floor
              (t * ((a + Real.pi - xs.getLastD b) / Real.pi)) +
            Nat.floor (t * ((b - a) / Real.pi)) + carry] := by
  obtain ⟨carry, hcarry, hmerge⟩ :=
    natFloor_scaled_gap_merge
      ht hgLast hgFirst
  refine ⟨carry, hcarry, ?_, ?_⟩
  · rw [normalizedProjectiveGaps_cons_cons_decompose]
    simp [quotientList, List.map_append]
  · rw [normalizedProjectiveGaps_delete_first_general]
    simp only [quotientList, List.map_append, List.map_singleton]
    rw [hmerge]

/-- Parent/child list-exponent gain when the first and final parent quotients
are positive. -/
theorem listExponent_gain_delete_first_general
    {a b t : ℝ} {xs : List ℝ}
    (ht : 0 ≤ t)
    (hgFirst : 0 ≤ (b - a) / Real.pi)
    (hgLast :
      0 ≤ (a + Real.pi - xs.getLastD b) / Real.pi)
    (hFirst :
      1 ≤ Nat.floor (t * ((b - a) / Real.pi)))
    (hLast :
      1 ≤ Nat.floor
        (t * ((a + Real.pi - xs.getLastD b) / Real.pi))) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: b :: xs))) + 1
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (b :: xs))) := by
  obtain ⟨carry, hcarry, hparent, hchild⟩ :=
    quotientList_delete_first_general
      ht hgFirst hgLast
  let qFirst :=
    Nat.floor (t * ((b - a) / Real.pi))
  let qLast :=
    Nat.floor
      (t * ((a + Real.pi - xs.getLastD b) / Real.pi))
  let qmid :=
    (normalizedSuccessiveTail b xs).map
      (fun g => Nat.floor (t * g))
  have hp :
      quotientList t
          (normalizedProjectiveGaps (a :: b :: xs)) =
        qFirst :: (qmid ++ [qLast]) := by
    simpa [qFirst, qLast, qmid] using hparent
  have hc :
      quotientList t
          (normalizedProjectiveGaps (b :: xs)) =
        qmid ++ [qLast + qFirst + carry] := by
    simpa [qFirst, qLast, qmid] using hchild
  rw [hp, hc]
  exact pinned_cyclic_merge_gain_of_end_positive
    qFirst qLast carry qmid
    (by simpa [qFirst] using hFirst)
    (by simpa [qLast] using hLast)

#print axioms normalizedProjectiveGaps_delete_first_general
#print axioms quotientList_delete_first_general
#print axioms listExponent_gain_delete_first_general

end JSP000404Research
