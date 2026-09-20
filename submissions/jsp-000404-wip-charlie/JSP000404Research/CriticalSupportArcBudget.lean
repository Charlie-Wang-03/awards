import JSP000404Research.AngleCirclePacking
import JSP000404Research.CriticalBadMass
import Mathlib.Tactic

/-!
# Critical support-arc turn budget

The final lower-branch arithmetic only needs

  sum_c s(c) <= 2*t,

for the normalized widths of an irredundant family of critical obstructions.

A clean geometric way to obtain this is to attach to each critical obstruction
an open direction-circle arc of physical angular length

  lambda * s(c),

with all such arcs pairwise disjoint.  Since the full direction circle has
length 2*pi and pi=t*lambda, circle packing gives

  lambda * sum s(c) <= 2*pi = 2*t*lambda,

hence the desired normalized total-turn bound.

This file isolates that exact outlet.  The remaining geometry is only the
construction and disjointness of the critical support arcs.
-/

namespace JSP000404Research

open Real
open scoped BigOperators
open Metric Set

/-- Pairwise-disjoint physical arcs of lengths lambda*s(c) yield the normalized
critical total-turn budget sum s <= 2*t. -/
theorem critical_total_turn_of_disjoint_direction_arcs
    {C : Type*} [Fintype C]
    (center : C → DirectionCircle)
    (s : C → ℝ)
    {lam t : ℝ}
    (hlam : 0 < lam)
    (hpi : Real.pi = t * lam)
    (hs0 : ∀ c, 0 ≤ s c)
    (hsBound : ∀ c, lam * s c ≤ 2 * Real.pi)
    (hdisj :
      PairwiseDisjoint (Set.univ : Set C)
        (fun c =>
          Metric.ball (center c) ((lam * s c) / 2))) :
    (∑ c, s c) ≤ 2 * t := by
  have hlen :=
    directionCircle_disjoint_ball_length_sum_le
      center
      (fun c => lam * s c)
      (fun c => mul_nonneg hlam.le (hs0 c))
      hsBound
      hdisj
  have hfactor :
      (∑ c, lam * s c) =
        lam * (∑ c, s c) := by
    rw [Finset.mul_sum]
  rw [hfactor, hpi] at hlen
  nlinarith

/-- Sendov-normalized form with t=n+delta. -/
theorem critical_total_turn_sendov_of_disjoint_direction_arcs
    {C : Type*} [Fintype C]
    (center : C → DirectionCircle)
    (s : C → ℝ)
    {lam delta : ℝ} {n : ℕ}
    (hlam : 0 < lam)
    (hpi : Real.pi = ((n : ℝ) + delta) * lam)
    (hs0 : ∀ c, 0 ≤ s c)
    (hsBound : ∀ c, lam * s c ≤ 2 * Real.pi)
    (hdisj :
      PairwiseDisjoint (Set.univ : Set C)
        (fun c =>
          Metric.ball (center c) ((lam * s c) / 2))) :
    (∑ c, s c) ≤ 2 * ((n : ℝ) + delta) := by
  exact critical_total_turn_of_disjoint_direction_arcs
    center s hlam hpi hs0 hsBound hdisj

/-- Once the disjoint critical arcs are available, their bad phase intervals
have total mass strictly below the phase circumference in the lower branch. -/
theorem critical_bad_mass_lt_phase_of_disjoint_direction_arcs
    {C : Type*} [Fintype C]
    (center : C → DirectionCircle)
    (s : C → ℝ)
    {lam delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    (hpi : Real.pi = ((n : ℝ) + delta) * lam)
    (hone : ∀ c, 1 ≤ s c)
    (hsBound : ∀ c, lam * s c ≤ 2 * Real.pi)
    (hdisj :
      PairwiseDisjoint (Set.univ : Set C)
        (fun c =>
          Metric.ball (center c) ((lam * s c) / 2))) :
    (∑ c, criticalBadWidth delta (s c))
      < (n : ℝ) + delta := by
  have htotal :=
    critical_total_turn_sendov_of_disjoint_direction_arcs
      center s hlam hpi
      (fun c => (hone c).trans (by norm_num : (0 : ℝ) ≤ 1))
      hsBound hdisj
  exact sum_criticalBadWidth_lt_sendov_phase
    s hn hdelta0 hdelta hone htotal

#print axioms critical_total_turn_of_disjoint_direction_arcs
#print axioms critical_total_turn_sendov_of_disjoint_direction_arcs
#print axioms critical_bad_mass_lt_phase_of_disjoint_direction_arcs

end JSP000404Research
