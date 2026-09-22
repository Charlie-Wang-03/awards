import JSP000404Research.CyclicActualAngles
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Cyclic edge values commute with list rotation

For a cyclically ordered vertex list l and an edge function w(a,b), the
position-aligned cyclic edge list is

  zipWith w l (l.rotate 1).

Mathlib's zipWith_rotate_distrib immediately shows that rotating the vertex
list by k rotates the cyclic edge list by exactly k positions.

The concrete cyclicRayAngles list is exactly this construction for

  w(a,b) = angle(p a, p i, p b).

Hence pinning any chosen ray at the head of a rotated cycle simultaneously
pins its outgoing actual angle at the first position and its incoming actual
angle at the final position.
-/

namespace JSP000404Research

def cyclicEdgeValues
    {α β : Type*}
    (w : α → α → β) (l : List α) : List β :=
  List.zipWith w l (l.rotate 1)

theorem cyclicEdgeValues_length
    {α β : Type*}
    (w : α → α → β) (l : List α) :
    (cyclicEdgeValues w l).length = l.length := by
  unfold cyclicEdgeValues
  rw [List.length_zipWith, List.length_rotate, min_self]

theorem cyclicEdgeValues_rotate
    {α β : Type*}
    (w : α → α → β)
    (l : List α) (k : ℕ) :
    cyclicEdgeValues w (l.rotate k) =
      (cyclicEdgeValues w l).rotate k := by
  unfold cyclicEdgeValues
  rw [List.zipWith_rotate_distrib
      w l (l.rotate 1) k (List.length_rotate l 1).symm]
  rw [List.rotate_rotate, List.rotate_rotate]
  congr 2
  omega

/-- Recursive consecutive edge values coincide with zipWith against the
one-step shifted list, before closing the cycle. -/
theorem zipWith_shift_eq_consecutive_append_last
    {α β : Type*}
    (w : α → α → β)
    (first : α) (rest : List α) :
    List.zipWith w (first :: rest)
        ((first :: rest).rotate 1)
      =
    let last := rest.getLastD first
    (match rest with
      | [] => [w first first]
      | _ =>
          (let rec go : α → List α → List β
            | _, [] => []
            | prev, x :: xs => w prev x :: go x xs
           go first rest) ++ [w last first]) := by
  cases rest with
  | nil =>
      simp
  | cons r rs =>
      simp only [List.zipWith_rotate_one]
      let rec go : α → List α → List β
        | _, [] => []
        | prev, x :: xs => w prev x :: go x xs
      have htail :
          List.zipWith w (r :: rs) (rs ++ [first]) =
            go r rs ++ [w ((r :: rs).getLastD first) first] := by
        induction rs generalizing r with
        | nil =>
            simp [go]
        | cons x xs ih =>
            simp [go, ih]
      simp [go, htail]

/-- Concrete actual cyclic angles are generic cyclic edge values. -/
theorem cyclicRayAngles_eq_cyclicEdgeValues
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    cyclicRayAngles (p := p) i first rest =
      cyclicEdgeValues
        (fun a b : OtherVertex i =>
          EuclideanGeometry.angle (p a.1) (p i) (p b.1))
        (first :: rest) := by
  unfold cyclicEdgeValues cyclicRayAngles
  cases rest with
  | nil =>
      simp [consecutiveRayAngles]
  | cons r rs =>
      simp only [List.zipWith_rotate_one]
      have htail :
          List.zipWith
              (fun a b : OtherVertex i =>
                EuclideanGeometry.angle (p a.1) (p i) (p b.1))
              (r :: rs) (rs ++ [first])
            =
          consecutiveRayAngles (p := p) i r rs ++
            [EuclideanGeometry.angle
              (p ((r :: rs).getLastD first).1)
              (p i) (p first.1)] := by
        induction rs generalizing r with
        | nil =>
            simp [consecutiveRayAngles]
        | cons x xs ih =>
            simp [consecutiveRayAngles, ih]
      simp [consecutiveRayAngles, htail]

theorem cyclicRayAngles_rotate
    {V : Type*} {p : V → Plane}
    (i : V)
    (rays : List (OtherVertex i))
    (k : ℕ)
    (hne : rays ≠ []) :
    let first := (rays.rotate k).head
      (by simpa using hne)
    let rest := (rays.rotate k).tail
    cyclicRayAngles (p := p) i first rest =
      (cyclicEdgeValues
        (fun a b : OtherVertex i =>
          EuclideanGeometry.angle (p a.1) (p i) (p b.1))
        rays).rotate k := by
  have hrot : rays.rotate k ≠ [] := by
    simpa using hne
  let first := (rays.rotate k).head hrot
  let rest := (rays.rotate k).tail
  have hrebuild : first :: rest = rays.rotate k := by
    dsimp [first, rest]
    exact List.cons_head_tail hrot
  rw [cyclicRayAngles_eq_cyclicEdgeValues]
  rw [hrebuild]
  exact cyclicEdgeValues_rotate _ rays k

#print axioms cyclicEdgeValues_rotate
#print axioms cyclicRayAngles_eq_cyclicEdgeValues
#print axioms cyclicRayAngles_rotate

end JSP000404Research
