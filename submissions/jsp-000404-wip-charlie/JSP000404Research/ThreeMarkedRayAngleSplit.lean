import JSP000404Research.CyclicActualAngles
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Splitting consecutive and cyclic actual-angle lists at marked rays
-/

namespace JSP000404Research

private theorem marked_getLastD_append_cons
    {α : Type*}
    (pre : List α) (y : α) (tail : List α) (d : α) :
    (pre ++ y :: tail).getLastD d = tail.getLastD y := by
  induction pre generalizing d with
  | nil =>
      exact List.getLastD_cons
  | cons x xs ih =>
      rw [List.cons_append, List.getLastD_cons]
      exact ih x

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
      have hlast :
          (x :: xs).getLastD prev = xs.getLastD x :=
        List.getLastD_cons
      rw [hlast]

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
  have hrest :
      X ++ b :: Y ++ c :: Z =
        X ++ b :: (Y ++ c :: Z) := by
    simp [List.append_assoc]
  rw [hrest]
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
  have hlastFinal :
      (X ++ b :: (Y ++ c :: Z)).getLastD a =
        Z.getLastD c := by
    calc
      (X ++ b :: (Y ++ c :: Z)).getLastD a =
          (Y ++ c :: Z).getLastD b :=
        marked_getLastD_append_cons X b (Y ++ c :: Z) a
      _ = Z.getLastD c :=
        marked_getLastD_append_cons Y c Z b
  simp only [consecutiveRayAngles]
  rw [hlastFinal]
  simp [List.append_assoc]

/-- The angle between the endpoints of an OtherVertex path is bounded
by the sum of its successive actual angles.  Unlike the older generic
AnglePath wrapper, this formulation never introduces a degenerate singleton
path goal. -/
theorem angle_endpoints_le_consecutiveRayAngles_sum
    {V : Type*} {p : V → Plane}
    (i : V)
    (first last : OtherVertex i)
    (mid : List (OtherVertex i)) :
    EuclideanGeometry.angle (p first.1) (p i) (p last.1) ≤
      (consecutiveRayAngles (p := p) i first (mid ++ [last])).sum := by
  induction mid generalizing first with
  | nil =>
      simp [consecutiveRayAngles]
  | cons r rs ih =>
      have htri :=
        EuclideanGeometry.angle_le_angle_add_angle
          (p i) (p first.1) (p r.1) (p last.1)
      have htail := ih r
      simp only [List.cons_append, consecutiveRayAngles, List.sum_cons]
      linarith

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
  exact ⟨
    angle_endpoints_le_consecutiveRayAngles_sum
      (p := p) i a b X,
    angle_endpoints_le_consecutiveRayAngles_sum
      (p := p) i b c Y,
    angle_endpoints_le_consecutiveRayAngles_sum
      (p := p) i c a Z
  ⟩

#print axioms consecutiveRayAngles_append_cons
#print axioms angle_endpoints_le_consecutiveRayAngles_sum
#print axioms cyclicRayAngles_three_marked_split
#print axioms three_marked_path_endpoint_bounds

end JSP000404Research
