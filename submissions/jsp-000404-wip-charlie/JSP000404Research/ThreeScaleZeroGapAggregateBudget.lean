import JSP000404Research.ThreeFiveNoTopNarrowZeroGaps
import Mathlib.Tactic

/-!
# Aggregate, non-reusable angular slack at the three-unit scale

The previous individually small zero-quotient arcs do not capture the
one TOTAL remainder budget.  This lemma proves that all zero-floor
normalized gaps share exactly one budget delta, including when there
are several such gaps.

The application concerns actual n=3 planar centres and is a necessary
condition on the still unresolved five-centre profiles, not a global
proof of JSP-000404.
-/

namespace JSP000404Research

open scoped BigOperators

/-- For any subset S whose quotient floors are zero, their *combined*
scaled normalized gap is at most the single global slack delta. -/
theorem scaled_zero_floor_subset_sum_le_three_slack
    {I : Type*} [Fintype I]
    (g : I → ℝ) (t delta : ℝ)
    (ht : t = (3 : ℝ) + delta)
    (hg0 : ∀ i, 0 ≤ t * g i)
    (hgsum : (∑ i, g i) = 1)
    (hqsum : (∑ i, Nat.floor (t * g i)) = 3)
    (S : Finset I)
    (hS : ∀ i ∈ S, Nat.floor (t * g i) = 0) :
    (∑ i ∈ S, t * g i) ≤ delta := by
  let rem : I → ℝ := fun i => t * g i - (Nat.floor (t * g i) : ℝ)
  have hnonneg (i : I) : 0 ≤ rem i := by
    dsimp [rem]
    exact sub_nonneg.mpr (Nat.floor_le (hg0 i))
  have hcast : (∑ i, (Nat.floor (t * g i) : ℝ)) = 3 := by
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

/-- The sum of *all* actual zero quotient angular gaps at a saturated
n=3 support-two centre has only one delta budget. -/
theorem saturated_next_all_zero_gaps_total_le_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hsat : nextSaturatedSupportTwo C t) :
    (∑ r ∈ (Finset.univ.filter
      (fun r : Fin C.gaps.length => centreQuotient C t r = 0)),
        t * C.gaps.get r) ≤ delta := by
  let S : Finset (Fin C.gaps.length) :=
    Finset.univ.filter
      (fun r => centreQuotient C t r = 0)
  have ht0 : 0 ≤ t := by linarith
  have hg0 : ∀ r : Fin C.gaps.length, 0 ≤ t * C.gaps.get r := by
    intro r
    exact mul_nonneg ht0
      (C.gaps_nonneg (C.gaps.get r) (List.get_mem _ _))
  have hgsum : (∑ r : Fin C.gaps.length, C.gaps.get r) = 1 := by
    rw [← List.sum_ofFn]
    simpa using C.gaps_sum
  have hqsum :
      (∑ r : Fin C.gaps.length, Nat.floor (t * C.gaps.get r)) = 3 := by
    simpa [centreQuotient] using hsat.2.1
  have hS : ∀ r ∈ S, Nat.floor (t * C.gaps.get r) = 0 := by
    intro r hr
    have hr0 : centreQuotient C t r = 0 :=
      (Finset.mem_filter.mp hr).2
    simpa [centreQuotient] using hr0
  exact scaled_zero_floor_subset_sum_le_three_slack
    (fun r => C.gaps.get r) t delta ht hg0 hgsum hqsum S hS

#print axioms scaled_zero_floor_subset_sum_le_three_slack
#print axioms saturated_next_all_zero_gaps_total_le_slack

end JSP000404Research
