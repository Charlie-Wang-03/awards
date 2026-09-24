
import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.CyclicQuotientRotation
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Moving the projective cut only rotates the cyclic gap list

Suppose a projective-angle cycle, written at one cut, is split into two blocks

  low ++ high.

Move the cut between these blocks, move high to the front, and subtract pi
from every angle in high:

  high.map (fun x => x - pi) ++ low.

This is the ordinary unwrapped-angle representation of the same cyclic
projective directions at the new cut.

The cyclic physical projective-gap list is exactly rotated by low.length.
Consequently the normalized gap list, quotient list, and listExponent are all
unchanged up to the same cyclic rotation.
-/

namespace JSP000404Research

open Real

theorem getLastD_append_cons
    {α : Type*}
    (a b : α) (xs ys : List α) :
    (xs ++ b :: ys).getLastD a =
      ys.getLastD b := by
  induction xs generalizing a with
  | nil =>
      simp [List.getLastD_cons]
  | cons x xs ih =>
      simp [List.getLastD_cons, ih]

theorem getLastD_map_sub
    (a c : ℝ) (xs : List ℝ) :
    (xs.map (fun x => x - c)).getLastD (a - c) =
      xs.getLastD a - c := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.getLastD_cons, ih]

theorem successiveDiffsFrom_map_sub
    (a c : ℝ) (xs : List ℝ) :
    successiveDiffsFrom (a - c)
        (xs.map (fun x => x - c)) =
      successiveDiffsFrom a xs := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp [successiveDiffsFrom, ih]
      ring

/-- Successive differences through an appended nonempty block. -/
theorem successiveDiffsFrom_append_cons
    (a b : ℝ) (xs ys : List ℝ) :
    successiveDiffsFrom a (xs ++ b :: ys) =
      successiveDiffsFrom a xs ++
        (b - xs.getLastD a) ::
          successiveDiffsFrom b ys := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp [successiveDiffsFrom, ih, List.getLastD_cons]

/-- Translation of one whole nonempty angle list leaves all cyclic projective
gaps unchanged. -/
theorem projectiveGaps_map_sub
    (a c : ℝ) (xs : List ℝ) :
    projectiveGaps
        ((a :: xs).map (fun x => x - c)) =
      projectiveGaps (a :: xs) := by
  simp only [List.map_cons, projectiveGaps]
  rw [successiveDiffsFrom_map_sub,
      getLastD_map_sub]
  congr 1
  ring

/-- Explicit cyclic gaps for two consecutive nonempty blocks. -/
theorem projectiveGaps_two_nonempty_blocks
    (a b : ℝ) (as bs : List ℝ) :
    projectiveGaps ((a :: as) ++ (b :: bs)) =
      (successiveDiffsFrom a as ++
        [b - as.getLastD a]) ++
      (successiveDiffsFrom b bs ++
        [a + Real.pi - bs.getLastD b]) := by
  simp only [List.cons_append, projectiveGaps]
  rw [successiveDiffsFrom_append_cons,
      getLastD_append_cons]
  simp [List.append_assoc]

/-- After moving the second block to the front and subtracting pi from it,
the two block-gap pieces exchange order. -/
theorem projectiveGaps_shifted_two_blocks
    (a b : ℝ) (as bs : List ℝ) :
    projectiveGaps
        (((b :: bs).map
            (fun x => x - Real.pi)) ++
          (a :: as))
      =
      (successiveDiffsFrom b bs ++
        [a + Real.pi - bs.getLastD b]) ++
      (successiveDiffsFrom a as ++
        [b - as.getLastD a]) := by
  rw [projectiveGaps_two_nonempty_blocks
      (b - Real.pi) a
      (bs.map (fun x => x - Real.pi)) as]
  rw [successiveDiffsFrom_map_sub,
      getLastD_map_sub]
  congr 1 <;> ring

/-- Main nondegenerate cut-rotation identity. -/
theorem projectiveGaps_cut_rotate_nonempty
    (a b : ℝ) (as bs : List ℝ) :
    projectiveGaps
        (((b :: bs).map
            (fun x => x - Real.pi)) ++
          (a :: as))
      =
    (projectiveGaps ((a :: as) ++ (b :: bs))).rotate
      (a :: as).length := by
  let L :
      List ℝ :=
    successiveDiffsFrom a as ++
      [b - as.getLastD a]
  let H :
      List ℝ :=
    successiveDiffsFrom b bs ++
      [a + Real.pi - bs.getLastD b]
  have hcanon :
      projectiveGaps ((a :: as) ++ (b :: bs)) =
        L ++ H := by
    simpa [L, H] using
      projectiveGaps_two_nonempty_blocks a b as bs
  have hshift :
      projectiveGaps
          (((b :: bs).map
              (fun x => x - Real.pi)) ++
            (a :: as))
        =
        H ++ L := by
    simpa [L, H] using
      projectiveGaps_shifted_two_blocks a b as bs
  have hlen :
      L.length = (a :: as).length := by
    simp [L, successiveDiffsFrom_length]
  rw [hshift, hcanon, ← hlen]
  exact (List.rotate_append_length_eq L H).symm

/-- General cut-rotation identity, including one empty side. -/
theorem projectiveGaps_cut_rotate
    (low high : List ℝ)
    (hne : low ++ high ≠ []) :
    projectiveGaps
        (high.map (fun x => x - Real.pi) ++ low)
      =
    (projectiveGaps (low ++ high)).rotate low.length := by
  cases low with
  | nil =>
      cases high with
      | nil =>
          exact False.elim (hne rfl)
      | cons b bs =>
          simp only [List.nil_append, List.length_nil,
            List.rotate_zero]
          exact projectiveGaps_map_sub b Real.pi bs
  | cons a as =>
      cases high with
      | nil =>
          simp only [List.map_nil, List.nil_append,
            List.append_nil]
          rw [← projectiveGaps_length (a :: as)]
          exact
            (List.rotate_length
              (projectiveGaps (a :: as))).symm
      | cons b bs =>
          exact projectiveGaps_cut_rotate_nonempty
            a b as bs

/-- Normalized projective gaps obey the same cut rotation. -/
theorem normalizedProjectiveGaps_cut_rotate
    (low high : List ℝ)
    (hne : low ++ high ≠ []) :
    normalizedProjectiveGaps
        (high.map (fun x => x - Real.pi) ++ low)
      =
    (normalizedProjectiveGaps (low ++ high)).rotate
      low.length := by
  unfold normalizedProjectiveGaps
  rw [projectiveGaps_cut_rotate low high hne]
  exact list_map_rotate
    (fun g : ℝ => g / Real.pi)
    (projectiveGaps (low ++ high))
    low.length

/-- Therefore the Sendov quotient-list exponent is invariant under moving this
projective cut. -/
theorem listExponent_cut_rotate
    (t : ℝ) (low high : List ℝ)
    (hne : low ++ high ≠ []) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (high.map (fun x => x - Real.pi) ++ low)))
      =
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (low ++ high))) := by
  rw [normalizedProjectiveGaps_cut_rotate low high hne]
  exact listExponent_quotientList_rotate
    t (normalizedProjectiveGaps (low ++ high))
      low.length

#print axioms successiveDiffsFrom_append_cons
#print axioms projectiveGaps_map_sub
#print axioms projectiveGaps_cut_rotate
#print axioms normalizedProjectiveGaps_cut_rotate
#print axioms listExponent_cut_rotate

end JSP000404Research
