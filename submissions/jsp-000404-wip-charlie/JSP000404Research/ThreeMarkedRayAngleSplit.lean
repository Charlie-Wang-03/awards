import JSP000404Research.CyclicActualAngles
import JSP000404Research.AnglePath
import Mathlib.Tactic

/-!
# Splitting consecutive and cyclic actual-angle lists at marked rays
-/

namespace JSP000404Research

theorem consecutiveRayAngles_append_cons
    {V : Type*} {p : V → Plane}
    (i : V)
    (prev : OtherVertex i)
    (xs : List (OtherVertex i))
    (y : OtherVertex i)
    (ys : List (OtherVertex i)) :
    consecutiveRayAngles (p := p) i prev (xs ++ y :: ys)
      =
    consecutiveRayAngles (p := p) i prev xs ++
      EuclideanGeometry.angle
        (p (xs.getLastD prev).1) (p i) (p y.1) ::
      consecutiveRayAngles (p := p) i y ys := by
  induction xs generalizing prev with
  | nil =>
      simp [consecutiveRayAngles]
  | cons x xs ih =>
      simp only [List.cons_append, consecutiveRayAngles]
      rw [ih x]
      simp [List.getLastD_cons]

/-- Three marked rays split the cyclic actual-angle list into the three
ordinary paths joining consecutive marked rays around the cycle. -/
theorem cyclicRayAngles_three_marked_split
    {V : Type*} {p : V → Plane}
    (i : V)
    (a b c : OtherVertex i)
    (X Y Z : List (OtherVertex i)) :
    cyclicRayAngles (p := p) i a
        (X ++ b :: Y ++ c :: Z)
      =
    consecutiveRayAngles (p := p) i a (X ++ [b]) ++
      consecutiveRayAngles (p := p) i b (Y ++ [c]) ++
      consecutiveRayAngles (p := p) i c (Z ++ [a]) := by
  unfold cyclicRayAngles
  rw [consecutiveRayAngles_append_cons
      (p := p) i a X b (Y ++ c :: Z)]
  rw [consecutiveRayAngles_append_cons
      (p := p) i b Y c Z]
  rw [consecutiveRayAngles_append_cons
      (p := p) i a X b []]
  rw [consecutiveRayAngles_append_cons
      (p := p) i b Y c []]
  rw [consecutiveRayAngles_append_cons
      (p := p) i c Z a []]
  simp only [consecutiveRayAngles]
  simp [List.append_assoc]

/-- Each of the three angle blocks controls its marked endpoint pair. -/
theorem three_marked_path_endpoint_bounds
    {V : Type*} {p : V → Plane}
    (i : V)
    (a b c : OtherVertex i)
    (X Y Z : List (OtherVertex i)) :
    EuclideanGeometry.angle (p a.1) (p i) (p b.1) ≤
        (consecutiveRayAngles (p := p) i a (X ++ [b])).sum
    ∧
    EuclideanGeometry.angle (p b.1) (p i) (p c.1) ≤
        (consecutiveRayAngles (p := p) i b (Y ++ [c])).sum
    ∧
    EuclideanGeometry.angle (p c.1) (p i) (p a.1) ≤
        (consecutiveRayAngles (p := p) i c (Z ++ [a])).sum := by
  constructor
  · apply angle_mem_otherVertex_path_le_consecutive_sum
      (p := p) i a (X ++ [b])
    · simp
    · simp
  · constructor
    · apply angle_mem_otherVertex_path_le_consecutive_sum
        (p := p) i b (Y ++ [c])
      · simp
      · simp
    · apply angle_mem_otherVertex_path_le_consecutive_sum
        (p := p) i c (Z ++ [a])
      · simp
      · simp

#print axioms consecutiveRayAngles_append_cons
#print axioms cyclicRayAngles_three_marked_split
#print axioms three_marked_path_endpoint_bounds

end JSP000404Research
