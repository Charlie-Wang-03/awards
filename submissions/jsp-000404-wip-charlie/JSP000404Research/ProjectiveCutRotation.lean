
import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.CyclicGapRotationInvariant
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Changing the cut of a projective angle circle rotates the gap list

Take two nonempty consecutive blocks

  pre  = a :: as,
  post = b :: bs

of one cyclic projective order.

Moving the cut from before a to before b, and lifting the old pre block by pi,
produces the real angle list

  (post shifted by -c) ++ (pre shifted by pi-c).

Internal successive differences are unchanged.  The old wrap gap becomes the
new bridge between the two blocks, while the old cut bridge becomes the new
wrap gap.

Therefore the new projective gap list is exactly the old gap list rotated by
pre.length.

No strict inequalities are used, so repeated projective angles are allowed.
-/

namespace JSP000404Research

open Real

theorem getLastD_append_cons
    {α : Type*}
    (xs : List α) (b : α) (bs : List α) (d : α) :
    (xs ++ b :: bs).getLastD d =
      bs.getLastD b := by
  induction xs generalizing d with
  | nil =>
      simp [List.getLastD_cons]
  | cons x xs ih =>
      simp [List.getLastD_cons, ih]

theorem getLastD_map_add
    (xs : List ℝ) (a c : ℝ) :
    (xs.map (fun x => x + c)).getLastD (a + c) =
      xs.getLastD a + c := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp [List.getLastD_cons, ih]

theorem successiveDiffsFrom_map_add
    (a c : ℝ) (xs : List ℝ) :
    successiveDiffsFrom (a + c)
        (xs.map (fun x => x + c))
      =
    successiveDiffsFrom a xs := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons, successiveDiffsFrom]
      have hhead : x + c - (a + c) = x - a := by ring
      rw [hhead, ih]

/-- Translating every angle by one common real constant leaves all cyclic
projective gaps unchanged. -/
theorem projectiveGaps_map_add
    (a c : ℝ) (xs : List ℝ) :
    projectiveGaps
        ((a :: xs).map (fun x => x + c))
      =
    projectiveGaps (a :: xs) := by
  simp only [List.map_cons, projectiveGaps]
  rw [successiveDiffsFrom_map_add,
      getLastD_map_add]
  congr 1
  ring

/-- The normalized cyclic projective gaps are translation invariant. -/
theorem normalizedProjectiveGaps_map_add
    (a c : ℝ) (xs : List ℝ) :
    normalizedProjectiveGaps
        ((a :: xs).map (fun x => x + c))
      =
    normalizedProjectiveGaps (a :: xs) := by
  unfold normalizedProjectiveGaps
  rw [projectiveGaps_map_add]

/-- Consequently the scaled quotient-list exponent is translation invariant. -/
theorem listExponent_quotientList_map_add
    (t a c : ℝ) (xs : List ℝ) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            ((a :: xs).map (fun x => x + c))))
      =
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: xs))) := by
  rw [normalizedProjectiveGaps_map_add]

/-- Split successive differences at a nonempty second block. -/
theorem successiveDiffsFrom_append_cons
    (a : ℝ) (xs : List ℝ)
    (b : ℝ) (bs : List ℝ) :
    successiveDiffsFrom a (xs ++ b :: bs)
      =
    successiveDiffsFrom a xs ++
      (b - xs.getLastD a) ::
        successiveDiffsFrom b bs := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp only [List.cons_append, successiveDiffsFrom]
      rw [ih]
      simp [List.getLastD_cons]

/-- Gap decomposition into the pre block and post block. -/
theorem projectiveGaps_two_block_decomp
    (a : ℝ) (as : List ℝ)
    (b : ℝ) (bs : List ℝ) :
    projectiveGaps ((a :: as) ++ (b :: bs))
      =
    (successiveDiffsFrom a as ++
      [b - as.getLastD a]) ++
    (successiveDiffsFrom b bs ++
      [a + Real.pi - bs.getLastD b]) := by
  simp only [List.cons_append, projectiveGaps]
  rw [successiveDiffsFrom_append_cons]
  rw [getLastD_append_cons]
  simp [List.append_assoc]

def anglesAfterProjectiveCut
    (c : ℝ)
    (pre post : List ℝ) : List ℝ :=
  post.map (fun x => x - c) ++
    pre.map (fun x => x + Real.pi - c)

/-- Main cut-change identity for two nonempty blocks. -/
theorem projectiveGaps_after_cut_eq_rotate
    (c a b : ℝ)
    (as bs : List ℝ) :
    projectiveGaps
        (anglesAfterProjectiveCut
          c (a :: as) (b :: bs))
      =
    (projectiveGaps
      ((a :: as) ++ (b :: bs))).rotate
        (a :: as).length := by
  let A : List ℝ :=
    successiveDiffsFrom a as ++
      [b - as.getLastD a]
  let B : List ℝ :=
    successiveDiffsFrom b bs ++
      [a + Real.pi - bs.getLastD b]
  have hold :
      projectiveGaps
          ((a :: as) ++ (b :: bs))
        =
      A ++ B := by
    exact projectiveGaps_two_block_decomp a as b bs
  have hpostDiff :
      successiveDiffsFrom (b - c)
        (bs.map (fun x => x - c))
      =
      successiveDiffsFrom b bs := by
    simpa [sub_eq_add_neg] using
      successiveDiffsFrom_map_add b (-c) bs
  have hpreDiff :
      successiveDiffsFrom (a + Real.pi - c)
        (as.map (fun x => x + Real.pi - c))
      =
      successiveDiffsFrom a as := by
    have h :=
      successiveDiffsFrom_map_add
        a (Real.pi - c) as
    simpa [sub_eq_add_neg, add_assoc] using h
  have hpostLast :
      (bs.map (fun x => x - c)).getLastD (b - c)
        =
      bs.getLastD b - c := by
    simpa [sub_eq_add_neg] using
      getLastD_map_add bs b (-c)
  have hpreLast :
      (as.map (fun x => x + Real.pi - c)).getLastD
          (a + Real.pi - c)
        =
      as.getLastD a + Real.pi - c := by
    have h :=
      getLastD_map_add as a (Real.pi - c)
    simpa [sub_eq_add_neg, add_assoc] using h
  have hnew :
      projectiveGaps
          (anglesAfterProjectiveCut
            c (a :: as) (b :: bs))
        =
      B ++ A := by
    rw [anglesAfterProjectiveCut]
    simp only [List.map_cons, List.cons_append]
    rw [projectiveGaps_two_block_decomp]
    rw [hpostDiff, hpreDiff,
        hpostLast, hpreLast]
    dsimp [A, B]
    congr 2 <;> ring
  rw [hold, hnew]
  have hlen :
      A.length = (a :: as).length := by
    simp [A, successiveDiffsFrom_length]
  rw [← hlen]
  exact List.rotate_append_length_eq A B

/-- Normalized gaps obey the same cut rotation. -/
theorem normalizedProjectiveGaps_after_cut_eq_rotate
    (c a b : ℝ)
    (as bs : List ℝ) :
    normalizedProjectiveGaps
        (anglesAfterProjectiveCut
          c (a :: as) (b :: bs))
      =
    (normalizedProjectiveGaps
      ((a :: as) ++ (b :: bs))).rotate
        (a :: as).length := by
  unfold normalizedProjectiveGaps
  rw [projectiveGaps_after_cut_eq_rotate]
  exact List.map_rotate _ _ _

/-- Consequently every scaled quotient exponent is cut-invariant. -/
theorem listExponent_after_projective_cut
    (t c a b : ℝ)
    (as bs : List ℝ) :
    listExponent
      (quotientList t
        (normalizedProjectiveGaps
          (anglesAfterProjectiveCut
            c (a :: as) (b :: bs))))
      =
    listExponent
      (quotientList t
        (normalizedProjectiveGaps
          ((a :: as) ++ (b :: bs))) ) := by
  apply listExponent_quotientList_eq_of_gap_rotate
    t
    (normalizedProjectiveGaps
      ((a :: as) ++ (b :: bs)))
    (normalizedProjectiveGaps
      (anglesAfterProjectiveCut
        c (a :: as) (b :: bs)))
    (a :: as).length
  exact normalizedProjectiveGaps_after_cut_eq_rotate
    c a b as bs

#print axioms projectiveGaps_map_add
#print axioms normalizedProjectiveGaps_map_add
#print axioms listExponent_quotientList_map_add
#print axioms successiveDiffsFrom_append_cons
#print axioms projectiveGaps_two_block_decomp
#print axioms projectiveGaps_after_cut_eq_rotate
#print axioms normalizedProjectiveGaps_after_cut_eq_rotate
#print axioms listExponent_after_projective_cut

end JSP000404Research
