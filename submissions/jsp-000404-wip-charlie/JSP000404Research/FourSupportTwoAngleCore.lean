import JSP000404Research.SharpCentre
import JSP000404Research.FourSupportTwoDerangementCore
import Mathlib.Tactic

/-!
# Kernel-isolated geometric four-support-two core

This module keeps only the geometry needed for the 81-to-9 reduction.

The global angle cap says the third angle of a triangle is at most pi - lam.
If two distinct vertices of that triangle both carry angles at most
delta * lam, then delta < 1/2 gives

  2 * delta * lam < lam,

so the three triangle angles would sum to strictly less than pi.

Consequently the four local three-way small-pair choices form one of the nine
derangement patterns from FourSupportTwoDerangementCore.

No residual-colouring, Hall, whole-cube, or projection infrastructure is used.
-/

namespace JSP000404Research

def FourSupportTwoAnglePattern9Core
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  FourChoiceDerangement9
    (EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
    (EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam)
    (EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam)
    (EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam)
    (EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam)
    (EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam)
    (EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam)
    (EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam)
    (EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam)
    (EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam)
    (EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam)
    (EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam)

/-- Under the global cap, two delta*lam-small angles cannot lie at two
vertices of one nondegenerate triangle when delta < 1/2. -/
theorem two_delta_small_angles_same_triangle_impossible_core
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam) :
    False := by
  have hc :
      EuclideanGeometry.angle (p a) (p c) (p b) ≤ Real.pi - lam :=
    hcap a c b hac hab hbc.symm
  have hsum :
      EuclideanGeometry.angle (p b) (p a) (p c) +
      EuclideanGeometry.angle (p a) (p b) (p c) +
      EuclideanGeometry.angle (p a) (p c) (p b) = Real.pi := by
    have htri :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p b) (p₂ := p a) (p c)
        (hp.ne hab)
    simpa [EuclideanGeometry.angle_comm, add_assoc, add_left_comm, add_comm] using htri
  have htwo : 2 * delta * lam < lam :=
    two_delta_lam_lt_lam hdeltaHalf hlampos
  nlinarith

/-- Concrete planar 81-to-9 reduction. Each centre supplies one small pair
among the other three vertices; the angle-cap collision lemma removes all
assignments that reuse a triangle. -/
theorem four_small_pair_choices_reduce_to_angle_derangement_nine_core
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hA :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∨
      EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∨
      EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam)
    (hB :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam ∨
      EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∨
      EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∨
      EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam ∨
      EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam)
    (hD :
      EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam ∨
      EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam ∨
      EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam) :
    FourSupportTwoAnglePattern9Core p delta lam a b c d := by
  unfold FourSupportTwoAnglePattern9Core
  apply four_three_choices_pairwise_collision_reduce_to_nine hA hB hC hD
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hab hac hbc h1 h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hac hab hbc.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1) h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hbc hab.symm hac.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1)
      (by simpa [EuclideanGeometry.angle_comm] using h2)
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hab had hbd h1 h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos had hab hbd.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1) h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hbd hab.symm had.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1)
      (by simpa [EuclideanGeometry.angle_comm] using h2)
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hac had hcd h1 h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos had hac hcd.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1) h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hcd hac.symm had.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1)
      (by simpa [EuclideanGeometry.angle_comm] using h2)
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hbc hbd hcd h1 h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hbd hbc hcd.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1) h2
  · rintro ⟨h1,h2⟩
    exact two_delta_small_angles_same_triangle_impossible_core
      hp hcap hdeltaHalf hlampos hcd hbc.symm hbd.symm
      (by simpa [EuclideanGeometry.angle_comm] using h1)
      (by simpa [EuclideanGeometry.angle_comm] using h2)

#print axioms two_delta_small_angles_same_triangle_impossible_core
#print axioms four_small_pair_choices_reduce_to_angle_derangement_nine_core

end JSP000404Research
