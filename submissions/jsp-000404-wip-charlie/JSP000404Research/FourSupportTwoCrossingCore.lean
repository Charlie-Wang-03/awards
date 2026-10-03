import JSP000404Research.FourSupportTwoDerangement
import JSP000404Research.CrossingDiagonalsQuadrilateralAngleSum
import Mathlib.Tactic

/-!
# Crossing-pair obstruction for the three surviving support-two patterns

After the sine-product reduction, the four-centre support-two terminal has
three double-transposition patterns.  Each pattern selects the four interior
angles of one Hamiltonian quadrilateral cycle.

If the corresponding perfect matching is the actual crossing-diagonal
pairing, those four angles sum to 2*pi.  But each is at most delta*lambda,
and delta < 1/2 with lambda <= pi/2 makes their total strictly smaller than
2*pi.  Hence the selected perfect matching must be noncrossing.

This module is independent of the residual / whole-cube chain.  It assumes
the four convex-hull exclusions directly; a separate bridge may later obtain
them from strict exposure.
-/

namespace JSP000404Research

open Real

private theorem four_delta_lam_lt_two_pi
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2) :
    4 * delta * lam < 2 * Real.pi := by
  have hsmall : 4 * delta * lam < 2 * lam := by
    nlinarith
  have hcap : 2 * lam ≤ Real.pi := by
    linarith
  linarith [Real.pi_pos]

theorem four_supportTwo_pattern1_impossible_of_cross_ad_bc
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha :
      p a ∉ convexHull ℝ ({p b,p c,p d} : Set Plane))
    (hd :
      p d ∉ convexHull ℝ ({p a,p b,p c} : Set Plane))
    (hcross :
      (segment ℝ (p a) (p d) ∩
        segment ℝ (p b) (p c)).Nonempty)
    (hpat :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam) :
    False := by
  have hsum :=
    crossing_diagonals_four_angles_sum_two_pi
      (a := p a) (b := p b) (c := p d) (d := p c)
      (hp.ne hab) (hp.ne had) (hp.ne hac)
      (hp.ne hbd) (hp.ne hbc) (hp.ne hcd.symm)
      ha
      (by
        simpa [Set.pair_insert_comm, Set.insert_comm, Set.insert_left_comm]
          using hd)
      hcross
  have hbound := four_delta_lam_lt_two_pi
    hdeltaHalf hlampos hlamHalf
  rcases hpat with ⟨hA,hB,hC,hD⟩
  have hsumLe :
      EuclideanGeometry.angle (p b) (p a) (p c) +
        EuclideanGeometry.angle (p a) (p b) (p d) +
        EuclideanGeometry.angle (p b) (p d) (p c) +
        EuclideanGeometry.angle (p d) (p c) (p a)
        ≤ 4 * delta * lam := by
    have hC' :
        EuclideanGeometry.angle (p d) (p c) (p a) ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hC
    nlinarith
  nlinarith

theorem four_supportTwo_pattern2_impossible_of_cross_ac_bd
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha :
      p a ∉ convexHull ℝ ({p b,p c,p d} : Set Plane))
    (hc :
      p c ∉ convexHull ℝ ({p a,p b,p d} : Set Plane))
    (hcross :
      (segment ℝ (p a) (p c) ∩
        segment ℝ (p b) (p d)).Nonempty)
    (hpat :
      EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam) :
    False := by
  have hsum :=
    crossing_diagonals_four_angles_sum_two_pi
      (a := p a) (b := p b) (c := p c) (d := p d)
      (hp.ne hab) (hp.ne hac) (hp.ne had)
      (hp.ne hbc) (hp.ne hbd) (hp.ne hcd)
      ha hc hcross
  have hbound := four_delta_lam_lt_two_pi
    hdeltaHalf hlampos hlamHalf
  rcases hpat with ⟨hA,hB,hC,hD⟩
  have hD' :
      EuclideanGeometry.angle (p c) (p d) (p a) ≤ delta * lam := by
    simpa [EuclideanGeometry.angle_comm] using hD
  have hsumLe :
      EuclideanGeometry.angle (p b) (p a) (p d) +
        EuclideanGeometry.angle (p a) (p b) (p c) +
        EuclideanGeometry.angle (p b) (p c) (p d) +
        EuclideanGeometry.angle (p c) (p d) (p a)
        ≤ 4 * delta * lam := by
    nlinarith
  nlinarith

theorem four_supportTwo_pattern3_impossible_of_cross_ab_cd
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha :
      p a ∉ convexHull ℝ ({p b,p c,p d} : Set Plane))
    (hb :
      p b ∉ convexHull ℝ ({p a,p c,p d} : Set Plane))
    (hcross :
      (segment ℝ (p a) (p b) ∩
        segment ℝ (p c) (p d)).Nonempty)
    (hpat :
      EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam) :
    False := by
  have hsum :=
    crossing_diagonals_four_angles_sum_two_pi
      (a := p a) (b := p c) (c := p b) (d := p d)
      (hp.ne hac) (hp.ne hab) (hp.ne had)
      (hp.ne hbc.symm) (hp.ne hcd) (hp.ne hbd)
      (by
        simpa [Set.pair_insert_comm, Set.insert_comm, Set.insert_left_comm]
          using ha)
      (by
        simpa [Set.pair_insert_comm, Set.insert_comm, Set.insert_left_comm]
          using hb)
      hcross
  have hbound := four_delta_lam_lt_two_pi
    hdeltaHalf hlampos hlamHalf
  rcases hpat with ⟨hA,hB,hC,hD⟩
  have hsumLe :
      EuclideanGeometry.angle (p c) (p a) (p d) +
        EuclideanGeometry.angle (p a) (p c) (p b) +
        EuclideanGeometry.angle (p c) (p b) (p d) +
        EuclideanGeometry.angle (p b) (p d) (p a)
        ≤ 4 * delta * lam := by
    have hD' :
        EuclideanGeometry.angle (p b) (p d) (p a) ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hD
    nlinarith
  nlinarith

/-- Every surviving double-transposition pattern avoids its corresponding
perfect matching as a crossing-diagonal pairing. -/
theorem four_supportTwo_pattern3_matching_is_noncrossing
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha :
      p a ∉ convexHull ℝ ({p b,p c,p d} : Set Plane))
    (hb :
      p b ∉ convexHull ℝ ({p a,p c,p d} : Set Plane))
    (hc :
      p c ∉ convexHull ℝ ({p a,p b,p d} : Set Plane))
    (hd :
      p d ∉ convexHull ℝ ({p a,p b,p c} : Set Plane))
    (hpat : FourSupportTwoDerangementPattern3 p delta lam a b c d) :
    (
      (
        EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
        EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
        EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam ∧
        EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam
      )
      ∧
      ¬(segment ℝ (p a) (p d) ∩
        segment ℝ (p b) (p c)).Nonempty
    )
    ∨
    (
      (
        EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
        EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam ∧
        EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam ∧
        EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam
      )
      ∧
      ¬(segment ℝ (p a) (p c) ∩
        segment ℝ (p b) (p d)).Nonempty
    )
    ∨
    (
      (
        EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
        EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
        EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∧
        EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam
      )
      ∧
      ¬(segment ℝ (p a) (p b) ∩
        segment ℝ (p c) (p d)).Nonempty
    ) := by
  unfold FourSupportTwoDerangementPattern3 at hpat
  unfold FourSupportTwoAnglePattern3Core at hpat
  rcases hpat with h1 | h2 | h3
  · left
    refine ⟨h1, ?_⟩
    intro hcross
    exact four_supportTwo_pattern1_impossible_of_cross_ad_bc
      hp hdeltaHalf hlampos hlamHalf
      hab hac had hbc hbd hcd ha hd hcross h1
  · right; left
    refine ⟨h2, ?_⟩
    intro hcross
    exact four_supportTwo_pattern2_impossible_of_cross_ac_bd
      hp hdeltaHalf hlampos hlamHalf
      hab hac had hbc hbd hcd ha hc hcross h2
  · right; right
    refine ⟨h3, ?_⟩
    intro hcross
    exact four_supportTwo_pattern3_impossible_of_cross_ab_cd
      hp hdeltaHalf hlampos hlamHalf
      hab hac had hbc hbd hcd ha hb hcross h3

#print axioms four_supportTwo_pattern1_impossible_of_cross_ad_bc
#print axioms four_supportTwo_pattern2_impossible_of_cross_ac_bd
#print axioms four_supportTwo_pattern3_impossible_of_cross_ab_cd
#print axioms four_supportTwo_pattern3_matching_is_noncrossing

end JSP000404Research
