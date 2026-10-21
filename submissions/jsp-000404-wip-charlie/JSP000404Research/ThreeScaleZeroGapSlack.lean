import JSP000404Research.ThreeFiveCompanionUnitQuotients
import Mathlib.Tactic

/-!
# Zero-quotient angular gaps in the exact three-unit companion

At scale t = 3 + delta, if the normalized gaps sum to one and the
integer quotient sum is three, the total continuous remainder is
delta. Every nonnegative remainder controls its own summand.

For an actual planar centre forced to have support at least three
in the n=3 five-centre top-plus-next motif, this gives
t * gap(r) <= delta at every zero quotient gap r.

This is local quantitative geometry, not exclusion of the motif.
-/

namespace JSP000404Research

open scoped BigOperators

/-- No floor remainder at a single index may exceed the total
nonnegative remainder budget, which is exactly delta. -/
theorem scaled_zero_floor_gap_le_three_slack
    {I : Type*} [Fintype I]
    (g : I → ℝ) (t delta : ℝ)
    (ht : t = 3 + delta)
    (hg0 : ∀ r, 0 ≤ t * g r)
    (hgsum : (∑ r, g r) = 1)
    (hqsum : (∑ r, Nat.floor (t * g r)) = 3)
    (i : I)
    (hzero : Nat.floor (t * g i) = 0) :
    t * g i ≤ delta := by
  have hnonneg (r : I) :
      0 ≤ t * g r - (Nat.floor (t * g r) : ℝ) := by
    exact sub_nonneg.mpr (Nat.floor_le (hg0 r))
  have hcast : (∑ r, (Nat.floor (t * g r) : ℝ)) = 3 := by
    exact_mod_cast hqsum
  have hremainders :
      (∑ r, (t * g r - (Nat.floor (t * g r) : ℝ))) =
        delta := by
    calc
      _ = t * (∑ r, g r) -
            (∑ r, (Nat.floor (t * g r) : ℝ)) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = delta := by rw [hgsum, hcast, ht]; ring
  have hi :
      t * g i - (Nat.floor (t * g i) : ℝ) ≤
        ∑ r, (t * g r - (Nat.floor (t * g r) : ℝ)) :=
    Finset.single_le_sum
      (f := fun r => t * g r - (Nat.floor (t * g r) : ℝ))
      (fun r _ => hnonneg r)
      (Finset.mem_univ i)
  rw [hremainders] at hi
  simpa [hzero] using hi

/-- Actual projective gap with quotient zero has scaled width <= delta
when the centre has three positive unit quotients at n=3. -/
theorem three_scale_high_support_zero_gap_le_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {delta t : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hsupport : 3 ≤ positiveSupport (centreQuotient C t))
    (r : Fin C.gaps.length)
    (hzero : centreQuotient C t r = 0) :
    t * C.gaps.get r ≤ delta := by
  have hrigid := three_scale_high_support_exact_rigidity C
    hdelta0 hdeltaHalf ht hsupport
  have ht0 : 0 ≤ t := by linarith
  have hg0 : ∀ j : Fin C.gaps.length, 0 ≤ t * C.gaps.get j := by
    intro j
    exact mul_nonneg ht0
      (C.gaps_nonneg (C.gaps.get j) (List.get_mem _ _))
  have hgsum : (∑ j : Fin C.gaps.length, C.gaps.get j) = 1 := by
    rw [← List.sum_ofFn]
    simpa using C.gaps_sum
  have hqsum :
      (∑ j : Fin C.gaps.length, Nat.floor (t * C.gaps.get j)) = 3 := by
    simpa [centreQuotient] using hrigid.2.2
  exact scaled_zero_floor_gap_le_three_slack
    (fun j => C.gaps.get j) t delta ht hg0 hgsum hqsum
    r (by simpa [centreQuotient] using hzero)

#print axioms scaled_zero_floor_gap_le_three_slack
#print axioms three_scale_high_support_zero_gap_le_slack

end JSP000404Research
