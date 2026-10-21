import JSP000404Research.ThreeScaleZeroGapAggregateBudget
import Mathlib.Tactic

/-!
# Aggregate zero quotient gaps share ONE delta budget at EVERY n

A saturated centre whose integer gap-quotient sum equals n at scale
t = n + delta has continuous floor remainder exactly delta.
Consequently all zero-quotient projective gaps, in aggregate, consume
at most delta of scaled angular width.  This is a genuine *local*
non-reusable budget valid without any global NET source assignment.

A centre of exponent n-3 and positive support 3 has precisely
quotient sum n, so this directly covers the general third-layer
support-three centres that enter deletion compensation.

Nothing here pays independent hard/soft/twin/duplicate NET debts.
-/

namespace JSP000404Research

open scoped BigOperators

theorem general_saturated_zero_floor_subset_sum_le_slack
    {I : Type*} [Fintype I]
    (g : I → ℝ) (n : ℕ) (t delta : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hg0 : ∀ i, 0 ≤ t * g i)
    (hgsum : (∑ i, g i) = 1)
    (hqsum : (∑ i, Nat.floor (t * g i)) = n)
    (S : Finset I)
    (hS : ∀ i ∈ S, Nat.floor (t * g i) = 0) :
    (∑ i ∈ S, t * g i) ≤ delta := by
  let rem : I → ℝ := fun i => t * g i - (Nat.floor (t * g i) : ℝ)
  have hnonneg (i : I) : 0 ≤ rem i := by
    dsimp [rem]
    exact sub_nonneg.mpr (Nat.floor_le (hg0 i))
  have hcast : (∑ i, (Nat.floor (t * g i) : ℝ)) = n := by
    exact_mod_cast hqsum
  have hremainders : (∑ i, rem i) = delta := by
    dsimp [rem]
    calc
      (∑ i, (t * g i - (Nat.floor (t * g i) : ℝ))) =
          t * (∑ i, g i) - (∑ i, (Nat.floor (t * g i) : ℝ)) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = delta := by rw [hgsum, hcast, ht]; ring
  have heq : (∑ i ∈ S, t * g i) = ∑ i ∈ S, rem i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [rem, hS i hi]
  calc
    (∑ i ∈ S, t * g i) = ∑ i ∈ S, rem i := heq
    _ ≤ ∑ i : I, rem i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro i hi _
      exact hnonneg i
    _ = delta := hremainders

/-- Entire actual zero-gap support at an arbitrary n-saturated centre. -/
theorem saturated_centre_zero_gap_total_le_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hquotient : (∑ r, centreQuotient C t r) = n) :
    (∑ r ∈ (Finset.univ.filter
      (fun r : Fin C.gaps.length => centreQuotient C t r = 0)),
      t * C.gaps.get r) ≤ delta := by
  let S : Finset (Fin C.gaps.length) :=
    Finset.univ.filter (fun r => centreQuotient C t r = 0)
  have ht0 : 0 ≤ t := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hg0 : ∀ r : Fin C.gaps.length, 0 ≤ t * C.gaps.get r := by
    intro r
    exact mul_nonneg ht0
      (C.gaps_nonneg (C.gaps.get r) (List.get_mem _ _))
  have hgsum : (∑ r : Fin C.gaps.length, C.gaps.get r) = 1 := by
    rw [← List.sum_ofFn]
    simpa using C.gaps_sum
  have hqsum :
      (∑ r : Fin C.gaps.length, Nat.floor (t * C.gaps.get r)) = n := by
    simpa [centreQuotient] using hquotient
  have hS : ∀ r ∈ S, Nat.floor (t * C.gaps.get r) = 0 := by
    intro r hr
    have hr0 : centreQuotient C t r = 0 :=
      (Finset.mem_filter.mp hr).2
    simpa [centreQuotient] using hr0
  exact general_saturated_zero_floor_subset_sum_le_slack
    (fun r => C.gaps.get r) n t delta ht hg0 hgsum hqsum S hS

/-- All support-three deficit-three centres, for arbitrary n>=3,
consume at most one delta in *total* zero-floor angular gaps. -/
theorem third_layer_support_three_all_zero_gaps_le_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (hn : 3 ≤ n)
    {t delta : ℝ} (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsup : positiveSupport (centreQuotient C t) = 3) :
    (∑ r ∈ (Finset.univ.filter
      (fun r : Fin C.gaps.length => centreQuotient C t r = 0)),
      t * C.gaps.get r) ≤ delta := by
  have hfloor : floorExcess (centreQuotient C t) = n - 3 := by
    simpa [centreExponent] using hexp
  have hidentity :=
    floorExcess_add_positiveSupport (centreQuotient C t)
  have hquotient : (∑ r, centreQuotient C t r) = n := by
    rw [hfloor, hsup] at hidentity
    omega
  exact saturated_centre_zero_gap_total_le_slack
    C n hdelta0 ht hquotient

#print axioms general_saturated_zero_floor_subset_sum_le_slack
#print axioms saturated_centre_zero_gap_total_le_slack
#print axioms third_layer_support_three_all_zero_gaps_le_slack

end JSP000404Research
