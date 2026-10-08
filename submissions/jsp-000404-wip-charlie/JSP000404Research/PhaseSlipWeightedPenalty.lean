import JSP000404Research.CyclicBandNoPhaseSlipCapacity
import Mathlib.Tactic

/-!
# Quantitative global capacity penalty for phase-slip centres

For an ordered colouring by n+1 colours, suppose every centre i obeys
  exponent(i) + active(i).card <= n+1,
and each centre outside an explicitly designated exceptional set obeys the
strict version with n on the right.

Weighted Hansel then gives the sharp accounting inequality
  2 * sum_i 2^exponent(i)
    <= 2^(n+1) + sum_{i exceptional} 2^exponent(i).

In the concrete direction-cycle setting, the exceptional set is precisely
the centres admitting a paired (floor real gap, integer band jump) = (0,1).

This transfers the remaining capacity challenge from all vertices to an
explicitly defined exceptional weighted mass. It does *not* establish an
unconditional 2^n capacity bound.
-/

namespace JSP000404Research

open scoped BigOperators
open OrderedEdgeColoring

/-- Total dyadic weight of an explicitly chosen exceptional subset.
This definition deliberately encapsulates classical decidability, so the
global theorem does not require DecidablePred in its statement. -/
noncomputable def exceptionalDyadicMass
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (Bad : V → Prop) : ℕ := by
  classical
  exact ∑ v : V, if Bad v then 2 ^ exponent v else 0

/-- The one-bit palette loss can be charged entirely to a designated
exceptional family: ordinary centres pay twice their dyadic weight,
exceptional centres at least once. -/
theorem weighted_capacity_with_exceptional_penalty
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (Bad : V → Prop)
    (hfull : ∀ v, exponent v + (active R v).card ≤ n + 1)
    (hstrict : ∀ v, ¬ Bad v →
      exponent v + (active R v).card ≤ n) :
    2 * (∑ v : V, 2 ^ exponent v) ≤
      2 ^ (n + 1) + exceptionalDyadicMass exponent Bad := by
  classical
  change
    2 * (∑ v : V, 2 ^ exponent v) ≤
      2 ^ (n + 1) +
        ∑ v : V, (if Bad v then 2 ^ exponent v else 0)
  have hpoint : ∀ v : V,
      2 * 2 ^ exponent v ≤
        2 ^ (n + 1 - (active R v).card) +
          (if Bad v then 2 ^ exponent v else 0) := by
    intro v
    by_cases hb : Bad v
    · have hv := hfull v
      have hpow :
          2 ^ exponent v ≤ 2 ^ (n + 1 - (active R v).card) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      simp only [if_pos hb]
      omega
    · have hv := hstrict v hb
      have hpow :
          2 ^ (exponent v + 1) ≤
            2 ^ (n + 1 - (active R v).card) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      have hmul : 2 * 2 ^ exponent v ≤
          2 ^ (n + 1 - (active R v).card) := by
        simpa [pow_succ, mul_comm] using hpow
      simp only [if_neg hb, add_zero]
      exact hmul
  have hsum :
      (∑ v : V, 2 * 2 ^ exponent v) ≤
        ∑ v : V,
          (2 ^ (n + 1 - (active R v).card) +
            (if Bad v then 2 ^ exponent v else 0)) := by
    apply Finset.sum_le_sum
    intro v _
    exact hpoint v
  have hsplit :
      (∑ v : V,
        (2 ^ (n + 1 - (active R v).card) +
          (if Bad v then 2 ^ exponent v else 0))) =
        (∑ v : V, 2 ^ (n + 1 - (active R v).card)) +
          ∑ v : V, (if Bad v then 2 ^ exponent v else 0) := by
    rw [Finset.sum_add_distrib]
  have hcapacity := weighted_capacity R
  rw [hsplit] at hsum
  have htwice :
      2 * (∑ v : V, 2 ^ exponent v) =
        (∑ v : V, 2 * 2 ^ exponent v) := by
    rw [Finset.mul_sum]
  rw [← htwice] at hsum
  omega

namespace DirectionData

/-- Define phase-slip centres using the actual local direction-cycle
quotients and unit-band jumps, not an arbitrary abstract badness predicate. -/
def HasCyclicBandPhaseSlip
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t}
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (i : V) : Prop :=
  (0, 1) ∈ List.zip
    ((cyclicRealGapsAt t (cycles i).values).map Nat.floor)
    (cyclicBandJumps n ((cycles i).values.map Nat.floor))

/-- The unconditionally valid weighted penalty bound for genuine
local direction cycles: all loss beyond the n-bit baseline is
charged to the total dyadic mass of phase-slip centres. -/
theorem weighted_capacity_le_baseline_plus_phase_slip_penalty
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i) :
    2 * (∑ i : V, 2 ^ (cycles i).exponent) ≤
      2 ^ (n + 1) +
        exceptionalDyadicMass
          (fun i => (cycles i).exponent)
          (HasCyclicBandPhaseSlip cycles) := by
  classical
  let R : OrderedEdgeColoring V (n + 1) :=
    standardBandColoring D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast ht)
  have hactive : ∀ i, active R i =
      D.incidentBands (n + 1) i := by
    intro i
    exact standardBand_active_eq_incidentBands
      D (n + 1) (Nat.succ_pos n) (by exact_mod_cast ht) i
  have hfull : ∀ i,
      (cycles i).exponent + (active R i).card ≤ n + 1 := by
    intro i
    rw [hactive i]
    exact (cycles i).exponent_add_incidentBands_card_le ht
  have hstrict : ∀ i,
      ¬ HasCyclicBandPhaseSlip cycles i →
      (cycles i).exponent + (active R i).card ≤ n := by
    intro i hno
    rw [hactive i]
    exact (cycles i).exponent_add_incidentBands_card_le_n_of_no_phase_slip
      ht hno
  exact weighted_capacity_with_exceptional_penalty
    R (fun i => (cycles i).exponent)
    (HasCyclicBandPhaseSlip cycles) hfull hstrict

#print axioms weighted_capacity_with_exceptional_penalty
#print axioms weighted_capacity_le_baseline_plus_phase_slip_penalty

end DirectionData
end JSP000404Research
