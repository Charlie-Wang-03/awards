import JSP000404Research.CyclicActualAngles
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Pairwise angle control by a ray-chain length

For rays r0,r1,... around a fixed centre i, the unoriented angle metric
satisfies the triangle inequality.  Hence the angle between any two rays in a
linear ray list is bounded by the sum of all consecutive actual angles along
that list.

This converts a small total zero-angle block into pairwise small angles without
constructing explicit common-sign interval parameters.
-/

namespace JSP000404Research

open Real

theorem angle_first_to_member_le_consecutive_sum
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    {j : OtherVertex i}
    (hj : j ∈ first :: rest) :
    EuclideanGeometry.angle
        (p first.1) (p i) (p j.1)
      ≤
    (consecutiveRayAngles (p := p) i first rest).sum := by
  induction rest generalizing first with
  | nil =>
      simp at hj
      subst j
      simp [consecutiveRayAngles]
  | cons r rs ih =>
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · simp [consecutiveRayAngles]
      · have htri :
          EuclideanGeometry.angle
              (p first.1) (p i) (p j.1)
            ≤
          EuclideanGeometry.angle
              (p first.1) (p i) (p r.1) +
          EuclideanGeometry.angle
              (p r.1) (p i) (p j.1) := by
          change
            InnerProductGeometry.angle
                (p first.1 - p i) (p j.1 - p i)
              ≤
            InnerProductGeometry.angle
                (p first.1 - p i) (p r.1 - p i) +
            InnerProductGeometry.angle
                (p r.1 - p i) (p j.1 - p i)
          exact InnerProductGeometry.angle_le_angle_add_angle _ _ _
        have htail :=
          ih r (by simpa using hj)
        simp only [consecutiveRayAngles, List.sum_cons]
        linarith

/-- Any pair of rays in one linear block is controlled by the total
consecutive-angle length of the block. -/
theorem angle_pair_le_consecutive_sum
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    {j k : OtherVertex i}
    (hj : j ∈ first :: rest)
    (hk : k ∈ first :: rest) :
    EuclideanGeometry.angle
        (p j.1) (p i) (p k.1)
      ≤
    (consecutiveRayAngles (p := p) i first rest).sum := by
  induction rest generalizing first with
  | nil =>
      simp at hj hk
      subst j
      subst k
      simp [consecutiveRayAngles]
  | cons r rs ih =>
      simp only [List.mem_cons] at hj hk
      rcases hj with rfl | hj
      · exact angle_first_to_member_le_consecutive_sum
          (p := p) i first (r :: rs)
          (by simp [hk])
      · rcases hk with rfl | hk
        · rw [EuclideanGeometry.angle_comm]
          exact angle_first_to_member_le_consecutive_sum
            (p := p) i first (r :: rs)
            (by simp [hj])
        · have htail :=
            ih r (by simpa using hj) (by simpa using hk)
          have hhead0 :
              0 ≤
                EuclideanGeometry.angle
                  (p first.1) (p i) (p r.1) :=
            EuclideanGeometry.angle_nonneg _ _ _
          simp only [consecutiveRayAngles, List.sum_cons]
          linarith

#print axioms angle_first_to_member_le_consecutive_sum
#print axioms angle_pair_le_consecutive_sum

end JSP000404Research
