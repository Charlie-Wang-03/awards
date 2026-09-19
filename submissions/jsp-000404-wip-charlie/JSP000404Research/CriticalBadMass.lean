import JSP000404Research.CriticalTurnBudget
import Mathlib.Tactic

/-!
# Direct bad-mass closure from a total critical-turn budget

For a critical transition of normalized width `s` in the lower branch, its
bad-phase interval has normalized width

  badWidth = 1 + delta - s,

with `1 <= s <= 1+delta`.

There is a sharper route than first bounding the number of critical
transitions.  Since `s >= 1` and `delta >= 0`,

  1 + delta - s <= delta * s.

Hence a global total-turn estimate

  sum s <= 2*t

immediately yields

  sum badWidth <= 2*delta*t < t

when `delta < 1/2` and `t>0`.

Thus the bad intervals cannot cover the full phase circle.  This module
isolates precisely that arithmetic shell; the remaining geometric theorem is
still only the global total-turn estimate.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Normalized bad-phase width attached to a critical transition. -/
def criticalBadWidth (delta s : ℝ) : ℝ :=
  1 + delta - s

/-- A critical width at least one pays for its own bad interval by a
`delta` fraction of the turn width. -/
theorem criticalBadWidth_le_delta_mul
    {delta s : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hs : 1 ≤ s) :
    criticalBadWidth delta s ≤ delta * s := by
  unfold criticalBadWidth
  nlinarith

/-- Summed version over a finite critical family. -/
theorem sum_criticalBadWidth_le_delta_mul_sum
    {C : Type*} [Fintype C]
    (s : C → ℝ) {delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hone : ∀ c, 1 ≤ s c) :
    (∑ c, criticalBadWidth delta (s c))
      ≤ delta * ∑ c, s c := by
  calc
    (∑ c, criticalBadWidth delta (s c))
        ≤ ∑ c, delta * s c := by
          exact Finset.sum_le_sum fun c _ =>
            criticalBadWidth_le_delta_mul hdelta0 (hone c)
    _ = delta * ∑ c, s c := by
          rw [Finset.mul_sum]

/-- A total critical-turn budget `sum s <= 2*t` forces total bad mass below
the phase circumference in the strict lower branch. -/
theorem sum_criticalBadWidth_lt_phase
    {C : Type*} [Fintype C]
    (s : C → ℝ) {delta t : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hone : ∀ c, 1 ≤ s c)
    (htotal : (∑ c, s c) ≤ 2 * t) :
    (∑ c, criticalBadWidth delta (s c)) < t := by
  have hbad :=
    sum_criticalBadWidth_le_delta_mul_sum s hdelta0 hone
  have hmul :
      delta * (∑ c, s c) ≤ delta * (2 * t) :=
    mul_le_mul_of_nonneg_left htotal hdelta0
  have hstrict : delta * (2 * t) < t := by
    nlinarith
  linarith

/-- In Sendov normalization `t=n+delta`, positivity follows from `n>=1`
and `delta>=0`. -/
theorem sum_criticalBadWidth_lt_sendov_phase
    {C : Type*} [Fintype C]
    (s : C → ℝ) {n : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hone : ∀ c, 1 ≤ s c)
    (htotal :
      (∑ c, s c) ≤ 2 * ((n : ℝ) + delta)) :
    (∑ c, criticalBadWidth delta (s c)) <
      (n : ℝ) + delta := by
  have ht : 0 < (n : ℝ) + delta := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact sum_criticalBadWidth_lt_phase
    s ht hdelta0 hdelta hone htotal

#print axioms criticalBadWidth_le_delta_mul
#print axioms sum_criticalBadWidth_le_delta_mul_sum
#print axioms sum_criticalBadWidth_lt_phase
#print axioms sum_criticalBadWidth_lt_sendov_phase

end JSP000404Research
