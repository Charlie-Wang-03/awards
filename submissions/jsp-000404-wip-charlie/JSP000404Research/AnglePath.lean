import JSP000404Research.CyclicActualAngles
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Angle paths around one centre

For a fixed centre i, define the angular length of a finite path of vertices as
the sum of the successive Euclidean angles at i.

The triangle inequality for angles implies that the angle between any two
vertices appearing in the path is bounded by the full path length.

This deliberately forgets projective signs and cyclic representatives.  In
the support-two application the path is obtained by deleting the sharp ray
from the cyclic order; every remaining edge of that path is a zero quotient
gap and the full path length is paid by the delta remainder budget.
-/

namespace JSP000404Research

open Real

def anglePathLength
    {V : Type*} (p : V → Plane) (i : V) :
    List V → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: xs =>
      EuclideanGeometry.angle (p a) (p i) (p b) +
        anglePathLength p i (b :: xs)

@[simp] theorem anglePathLength_nil
    {V : Type*} (p : V → Plane) (i : V) :
    anglePathLength p i [] = 0 := rfl

@[simp] theorem anglePathLength_singleton
    {V : Type*} (p : V → Plane) (i a : V) :
    anglePathLength p i [a] = 0 := rfl

theorem anglePathLength_nonneg
    {V : Type*} (p : V → Plane) (i : V)
    (xs : List V) :
    0 ≤ anglePathLength p i xs := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      cases xs with
      | nil =>
          simp [anglePathLength]
      | cons b bs =>
          simp only [anglePathLength]
          have hangle :
              0 ≤ EuclideanGeometry.angle (p a) (p i) (p b) :=
            EuclideanGeometry.angle_nonneg _ _ _
          have htail := anglePathLength_nonneg p i (b :: bs)
          linarith

/-- From the head of a path to any member, the angle is bounded by the full
path length. -/
theorem angle_head_le_anglePathLength
    {V : Type*} (p : V → Plane) (i : V)
    (a : V) (xs : List V)
    {y : V} (hy : y ∈ a :: xs) :
    EuclideanGeometry.angle (p a) (p i) (p y) ≤
      anglePathLength p i (a :: xs) := by
  induction xs generalizing a with
  | nil =>
      simp at hy
      subst y
      simp [anglePathLength]
  | cons b bs ih =>
      simp only [List.mem_cons] at hy
      rcases hy with hya | hyTail
      · subst y
        simp [anglePathLength]
        exact anglePathLength_nonneg p i (b :: bs)
      · have htri :=
          EuclideanGeometry.angle_le_angle_add_angle
            (p i) (p a) (p b) (p y)
        have htail :=
          ih b hyTail
        simp only [anglePathLength]
        linarith

/-- Any two vertices occurring in one path have mutual angle bounded by the
full path length. -/
theorem angle_mem_mem_le_anglePathLength
    {V : Type*} (p : V → Plane) (i : V)
    (xs : List V)
    {x y : V}
    (hx : x ∈ xs) (hy : y ∈ xs) :
    EuclideanGeometry.angle (p x) (p i) (p y) ≤
      anglePathLength p i xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons a xs ih =>
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hxTail
      · exact angle_head_le_anglePathLength
          p i a xs (by simp [hy])
      · rcases hy with rfl | hyTail
        · rw [EuclideanGeometry.angle_comm]
          exact angle_head_le_anglePathLength
            p i a xs (by simp [hxTail])
        · have htail :=
            ih hxTail hyTail
          cases xs with
          | nil =>
              simp at hxTail
          | cons b bs =>
              simp only [anglePathLength]
              have hfirst :
                  0 ≤ EuclideanGeometry.angle (p a) (p i) (p b) :=
                EuclideanGeometry.angle_nonneg _ _ _
              linarith

/-- Completeness wrapper: if one path contains every vertex except i and s,
then a total path bound produces OuterSmallAwayFrom-type pairwise control. -/
theorem angle_le_of_complete_path
    {V : Type*} (p : V → Plane)
    {s i : V} (xs : List V)
    (hcomplete :
      ∀ j, j ≠ i → j ≠ s → j ∈ xs)
    {W : ℝ}
    (hW : anglePathLength p i xs ≤ W) :
    ∀ j k,
      j ≠ i → k ≠ i →
      j ≠ s → k ≠ s →
      j ≠ k →
      EuclideanGeometry.angle (p j) (p i) (p k) ≤ W := by
  intro j k hji hki hjs hks hjk
  have hj := hcomplete j hji hjs
  have hk := hcomplete k hki hks
  exact (angle_mem_mem_le_anglePathLength
    p i xs hj hk).trans hW


/-- For an OtherVertex path, anglePathLength is exactly the sum of the
recursive consecutive actual-angle list. -/
theorem anglePathLength_map_val_eq_consecutiveRayAngles_sum
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    anglePathLength p i ((first :: rest).map Subtype.val) =
      (consecutiveRayAngles (p := p) i first rest).sum := by
  induction rest generalizing first with
  | nil =>
      simp [anglePathLength, consecutiveRayAngles]
  | cons r rs ih =>
      simp [anglePathLength, consecutiveRayAngles, ih]

/-- Any two underlying vertices in an OtherVertex path have angle bounded by
the sum of its consecutiveRayAngles. -/
theorem angle_mem_otherVertex_path_le_consecutive_sum
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    {x y : V}
    (hx : x ∈ (first :: rest).map Subtype.val)
    (hy : y ∈ (first :: rest).map Subtype.val) :
    EuclideanGeometry.angle (p x) (p i) (p y) ≤
      (consecutiveRayAngles (p := p) i first rest).sum := by
  rw [← anglePathLength_map_val_eq_consecutiveRayAngles_sum
      (p := p) i first rest]
  exact angle_mem_mem_le_anglePathLength
    p i ((first :: rest).map Subtype.val) hx hy

#print axioms angle_head_le_anglePathLength
#print axioms anglePathLength_map_val_eq_consecutiveRayAngles_sum
#print axioms angle_mem_mem_le_anglePathLength
#print axioms angle_le_of_complete_path

end JSP000404Research
