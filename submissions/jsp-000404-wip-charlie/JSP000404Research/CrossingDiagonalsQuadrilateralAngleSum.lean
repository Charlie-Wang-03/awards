import JSP000404Research.SharpCentre
import Mathlib.Analysis.Convex.Hull
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.Between
import Mathlib.Tactic

/-!
# Quadrilateral angle sum from crossing diagonals

For four pairwise-distinct planar points in convex position, if the segments
[a,c] and [b,d] intersect, then the Hamiltonian cycle a-b-c-d is the convex
boundary cycle in the only sense needed downstream: its four unoriented
interior angles sum to 2*pi.

The proof avoids polygon infrastructure.  Pick an intersection point q.
The diagonal incidences let us split each of the four vertex angles through q.
Four triangle angle-sum identities then contribute 4*pi.  Since q lies
strictly between a and c (endpoint cases are excluded by convex-hull
exclusion), the four angles at q contribute exactly 2*pi.  Subtraction gives
the desired quadrilateral sum.
-/

namespace JSP000404Research

open Real

set_option maxHeartbeats 800000 in
theorem crossing_diagonals_four_angles_sum_two_pi
    {a b c d : Plane}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∉ convexHull ℝ ({b,c,d} : Set Plane))
    (hc : c ∉ convexHull ℝ ({a,b,d} : Set Plane))
    (hcross :
      (segment ℝ a c ∩ segment ℝ b d).Nonempty) :
    EuclideanGeometry.angle b a d +
      EuclideanGeometry.angle a b c +
      EuclideanGeometry.angle b c d +
      EuclideanGeometry.angle c d a
      = 2 * Real.pi := by
  rcases hcross with ⟨q,hqac,hqbd⟩
  have hqacW : Wbtw ℝ a q c :=
    mem_segment_iff_wbtw.mp hqac
  have hqbdW : Wbtw ℝ b q d :=
    mem_segment_iff_wbtw.mp hqbd

  have hsegBD_a :
      segment ℝ b d ⊆ convexHull ℝ ({b,c,d} : Set Plane) := by
    apply (convex_convexHull ℝ ({b,c,d} : Set Plane)).segment_subset
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
  have hsegBD_c :
      segment ℝ b d ⊆ convexHull ℝ ({a,b,d} : Set Plane) := by
    apply (convex_convexHull ℝ ({a,b,d} : Set Plane)).segment_subset
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)

  have hqa : q ≠ a := by
    intro h
    apply ha
    apply hsegBD_a
    simpa [h] using hqbd
  have hqc : q ≠ c := by
    intro h
    apply hc
    apply hsegBD_c
    simpa [h] using hqbd
  have hqacS : Sbtw ℝ a q c :=
    ⟨hqacW,hqa,hqc⟩
  have hacPi :
      EuclideanGeometry.angle a q c = Real.pi :=
    hqacS.angle₁₂₃_eq_pi

  have hA :=
    EuclideanGeometry.angle_add_of_ne_of_ne
      hab had hqbdW
  have hB :=
    EuclideanGeometry.angle_add_of_ne_of_ne
      hab.symm hbc hqacW
  have hC :=
    EuclideanGeometry.angle_add_of_ne_of_ne
      hbc.symm hcd hqbdW
  have hD :=
    EuclideanGeometry.angle_add_of_ne_of_ne
      hcd.symm had.symm hqacW

  have hABQ :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := b) (p₂ := a) q hab.symm
  have hBCQ :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := q) (p₂ := b) c
      (by
        intro h
        subst q
        exact hqbdW.left_ne_right_of_ne_left hbd)
  have hCDQ :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := q) (p₂ := c) d
      (by
        intro h
        subst q
        exact hqacW.left_ne_right_of_ne_left hac.symm)
  have hDAQ :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := q) (p₂ := d) a
      (by
        intro h
        subst q
        exact hqbdW.left_ne_right_of_ne_right hbd)

  have hQ1 :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi b hacPi
  have hQ2 :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi d hacPi

  rw [EuclideanGeometry.angle_comm b q a] at hQ1
  rw [EuclideanGeometry.angle_comm d q a,
      EuclideanGeometry.angle_comm d q c] at hQ2

  -- Normalize the four split-angle identities to the exact boundary angles.
  have hA' :
      EuclideanGeometry.angle b a q +
        EuclideanGeometry.angle q a d =
        EuclideanGeometry.angle b a d := by
    simpa using hA
  have hB' :
      EuclideanGeometry.angle a b q +
        EuclideanGeometry.angle q b c =
        EuclideanGeometry.angle a b c := by
    simpa using hB
  have hC' :
      EuclideanGeometry.angle b c q +
        EuclideanGeometry.angle q c d =
        EuclideanGeometry.angle b c d := by
    simpa using hC
  have hD' :
      EuclideanGeometry.angle c d q +
        EuclideanGeometry.angle q d a =
        EuclideanGeometry.angle c d a := by
    simpa using hD

  -- Reorient the triangle angle sums by symmetry where needed.
  have hABQ' :
      EuclideanGeometry.angle b a q +
        EuclideanGeometry.angle a q b +
        EuclideanGeometry.angle a b q = Real.pi := by
    simpa [EuclideanGeometry.angle_comm] using hABQ
  have hBCQ' :
      EuclideanGeometry.angle q b c +
        EuclideanGeometry.angle b c q +
        EuclideanGeometry.angle b q c = Real.pi := by
    simpa [EuclideanGeometry.angle_comm] using hBCQ
  have hCDQ' :
      EuclideanGeometry.angle q c d +
        EuclideanGeometry.angle c d q +
        EuclideanGeometry.angle c q d = Real.pi := by
    simpa [EuclideanGeometry.angle_comm] using hCDQ
  have hDAQ' :
      EuclideanGeometry.angle q d a +
        EuclideanGeometry.angle d a q +
        EuclideanGeometry.angle d q a = Real.pi := by
    simpa [EuclideanGeometry.angle_comm] using hDAQ

  have hVertex :
      (EuclideanGeometry.angle b a q + EuclideanGeometry.angle q a d) +
      (EuclideanGeometry.angle a b q + EuclideanGeometry.angle q b c) +
      (EuclideanGeometry.angle b c q + EuclideanGeometry.angle q c d) +
      (EuclideanGeometry.angle c d q + EuclideanGeometry.angle q d a)
        =
      EuclideanGeometry.angle b a d +
      EuclideanGeometry.angle a b c +
      EuclideanGeometry.angle b c d +
      EuclideanGeometry.angle c d a := by
    rw [hA', hB', hC', hD']

  have hTriangles :
      (EuclideanGeometry.angle b a q + EuclideanGeometry.angle a q b +
        EuclideanGeometry.angle a b q) +
      (EuclideanGeometry.angle q b c + EuclideanGeometry.angle b c q +
        EuclideanGeometry.angle b q c) +
      (EuclideanGeometry.angle q c d + EuclideanGeometry.angle c d q +
        EuclideanGeometry.angle c q d) +
      (EuclideanGeometry.angle q d a + EuclideanGeometry.angle d a q +
        EuclideanGeometry.angle d q a)
        = 4 * Real.pi := by
    rw [hABQ', hBCQ', hCDQ', hDAQ']
    ring

  have hQ :
      EuclideanGeometry.angle a q b +
      EuclideanGeometry.angle b q c +
      EuclideanGeometry.angle c q d +
      EuclideanGeometry.angle d q a
        = 2 * Real.pi := by
    linarith only [hQ1, hQ2]

  linarith only [hVertex, hTriangles, hQ]

#print axioms crossing_diagonals_four_angles_sum_two_pi

end JSP000404Research
