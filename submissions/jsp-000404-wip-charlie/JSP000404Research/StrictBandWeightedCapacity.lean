import JSP000404Research.LocalDirectionCycle
import JSP000404Research.StandardBandColor
import Mathlib.Tactic

/-!
# One unit of additional local colour slack pays the residual band

For a colouring by n+1 bands, the standard local budget
  exponent(i) + active(i).card <= n+1
only yields total dyadic weight at most 2^(n+1).
A *one-unit strict improvement at every centre*
  exponent(i) + active(i).card <= n
recovers the needed 2^n weighted capacity by the Hansel inequality.

This is an exact sufficiency criterion, not a proof that all geometric
configurations satisfy its stronger hypothesis.
-/

namespace JSP000404Research

open scoped BigOperators
open OrderedEdgeColoring

/-- One extra unit of active-colour deficit, at every vertex, halves the
upper bound for the sum of prescribed dyadic weights. -/
theorem exponent_capacity_of_uniform_strict_band_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hstrict : ∀ v, exponent v + (active R v).card ≤ n) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hexp : ∀ v, exponent v ≤ n := by
    intro v
    have h := hstrict v
    omega
  have hact : ∀ v, (active R v).card ≤ n - exponent v := by
    intro v
    have h := hstrict v
    omega
  have hplus : ∀ v, exponent v + 1 ≤ n + 1 := by
    intro v
    have hv := hexp v
    omega
  have hell : ∀ v, n - exponent v =
      (n + 1) - (exponent v + 1) := by
    intro v
    have h := hexp v
    omega
  have hHansel :=
    cluster_capacity_of_active_le R
      (fun v => exponent v + 1)
      (fun v => n - exponent v) hplus hell hact
  have hsum :
      (∑ v : V, 2 ^ (exponent v + 1)) =
        2 * (∑ v : V, 2 ^ exponent v) := by
    calc
      (∑ v : V, 2 ^ (exponent v + 1)) =
          ∑ v : V, 2 * 2 ^ exponent v := by
            apply Finset.sum_congr rfl
            intro v hv
            simp [pow_succ, mul_comm]
      _ = 2 * (∑ v : V, 2 ^ exponent v) := by
            rw [Finset.mul_sum]
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
    simp [pow_succ, mul_comm]
  rw [hsum, hpow] at hHansel
  omega

namespace DirectionData
open OrderedEdgeColoring

/-- If each actual local direction cycle has a one-unit strict band budget,
the full standard colouring meets the target 2^n dyadic capacity. -/
theorem weighted_capacity_of_strict_local_direction_cycles
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hstrict : ∀ i : V,
      (cycles i).exponent +
        (D.incidentBands (n + 1) i).card ≤ n) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  let R : OrderedEdgeColoring V (n + 1) :=
    standardBandColoring D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast ht)
  have hbudget : ∀ i : V,
      (cycles i).exponent + (active R i).card ≤ n := by
    intro i
    simpa only [R, standardBand_active_eq_incidentBands] using hstrict i
  exact exponent_capacity_of_uniform_strict_band_slack
    R (fun i => (cycles i).exponent) hbudget

#print axioms exponent_capacity_of_uniform_strict_band_slack
#print axioms DirectionData.weighted_capacity_of_strict_local_direction_cycles

end DirectionData
end JSP000404Research
