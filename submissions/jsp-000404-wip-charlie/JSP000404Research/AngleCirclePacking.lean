import JSP000404Research.FiniteMeasurePacking
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Tactic

/-!
# Packing open arcs on the direction circle

We model ordinary directions modulo 2*pi by the additive circle

  AddCircle (2*pi).

For an arc of real angular length L with 0 <= L <= 2*pi, the corresponding
metric open ball of radius L/2 has Haar volume exactly L.  Therefore any finite
pairwise-disjoint family of such balls has total angular length at most 2*pi.

This is the measure-theoretic circle-packing shell needed by the strict-support
cone route for JSP-000404.
-/

namespace JSP000404Research

open scoped BigOperators MeasureTheory
open MeasureTheory Set Metric Real

abbrev DirectionCircle := AddCircle (2 * Real.pi)

private instance directionCirclePeriodPos : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨by positivity⟩

theorem directionCircle_measure_univ :
    volume (Set.univ : Set DirectionCircle) =
      ENNReal.ofReal (2 * Real.pi) := by
  simpa [DirectionCircle] using
    (AddCircle.measure_univ (T := 2 * Real.pi))

/-- An open ball on the direction circle has angular measure 2*r as long as
it does not exceed the whole circumference. -/
theorem directionCircle_volume_ball
    (x : DirectionCircle) (r : ℝ)
    (hr0 : 0 ≤ r)
    (hr : 2 * r ≤ 2 * Real.pi) :
    volume (Metric.ball x r) = ENNReal.ofReal (2 * r) := by
  have hae :
      Metric.closedBall x r =ᵐ[volume] Metric.ball x r :=
    AddCircle.closedBall_ae_eq_ball
      (T := 2 * Real.pi) (x := x) (ε := r)
  have hmeas :
      volume (Metric.ball x r) =
        volume (Metric.closedBall x r) := by
    exact (measure_congr hae).symm
  rw [hmeas, AddCircle.volume_closedBall]
  rw [min_eq_right hr]

/-- Length formulation: a ball of radius L/2 has measure exactly L. -/
theorem directionCircle_volume_ball_half_length
    (x : DirectionCircle) (L : ℝ)
    (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * Real.pi) :
    volume (Metric.ball x (L / 2)) = ENNReal.ofReal L := by
  have hr0 : 0 ≤ L / 2 := by linarith
  have hr : 2 * (L / 2) ≤ 2 * Real.pi := by
    linarith
  rw [directionCircle_volume_ball x (L / 2) hr0 hr]
  congr
  ring

/-- Finite pairwise-disjoint angular balls have total length at most 2*pi. -/
theorem directionCircle_disjoint_ball_length_sum_le
    {I : Type*} [Fintype I]
    (center : I → DirectionCircle)
    (length : I → ℝ)
    (hlength0 : ∀ i, 0 ≤ length i)
    (hlength2pi : ∀ i, length i ≤ 2 * Real.pi)
    (hdisj :
      PairwiseDisjoint (Set.univ : Set I)
        (fun i => Metric.ball (center i) (length i / 2))) :
    (∑ i, length i) ≤ 2 * Real.pi := by
  apply finite_disjoint_measurable_length_sum_le
    (mu := (volume : Measure DirectionCircle))
    (S := fun i => Metric.ball (center i) (length i / 2))
    (len := length)
    (T := 2 * Real.pi)
  · exact hlength0
  · intro i
    exact measurableSet_ball
  · exact hdisj
  · intro i
    exact directionCircle_volume_ball_half_length
      (center i) (length i)
      (hlength0 i) (hlength2pi i)
  · exact directionCircle_measure_univ
  · positivity

/-- Normalized form: if each length is pi*g_i, pairwise-disjoint support arcs
give sum g_i <= 2. -/
theorem normalized_directionCircle_disjoint_ball_sum_le_two
    {I : Type*} [Fintype I]
    (center : I → DirectionCircle)
    (gap : I → ℝ)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgappi : ∀ i, gap i ≤ 2)
    (hdisj :
      PairwiseDisjoint (Set.univ : Set I)
        (fun i =>
          Metric.ball (center i)
            ((Real.pi * gap i) / 2))) :
    (∑ i, gap i) ≤ 2 := by
  have hlen :=
    directionCircle_disjoint_ball_length_sum_le
      center
      (fun i => Real.pi * gap i)
      (fun i => mul_nonneg Real.pi_pos.le (hgap0 i))
      (fun i => by
        have := hgappi i
        nlinarith [Real.pi_pos])
      (by
        simpa [mul_div_assoc] using hdisj)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hfactor :
      (∑ i, Real.pi * gap i) =
        Real.pi * (∑ i, gap i) := by
    rw [Finset.mul_sum]
  rw [hfactor] at hlen
  nlinarith

#print axioms directionCircle_measure_univ
#print axioms directionCircle_volume_ball
#print axioms directionCircle_disjoint_ball_length_sum_le
#print axioms normalized_directionCircle_disjoint_ball_sum_le_two

end JSP000404Research
