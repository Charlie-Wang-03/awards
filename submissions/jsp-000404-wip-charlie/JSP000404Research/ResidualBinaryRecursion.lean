
import JSP000404Research.ResidualSideWidthReduction
import Mathlib.Tactic

/-!
# Binary Kraft recursion induced by the residual high band

Assume the high band has width < 1, so no vertex is both a high source and a
high sink.

The natural two recursive children are overlapping:

  left  = vertices which are not high sinks,
  right = vertices which are not high sources.

A genuine source belongs only to the left child.
A genuine sink belongs only to the right child.
A high-inactive vertex belongs to both children.

To preserve dyadic mass, keep the exponent of source/sink vertices and lower
the exponent of duplicated inactive vertices by one.

Pointwise:

* source: 2^k appears once;
* sink:   2^k appears once;
* inactive with k>0: 2^(k-1)+2^(k-1)=2^k;
* inactive with k=0: the two child unit weights only overpay.

Hence the root dyadic mass is bounded by the sum of the two child masses.
If both child masses are at most 2^(n-1), the sharp root bound 2^n follows.

This is a binary Kraft recursion skeleton.  It does not assume any comb
profile or pointwise deletion gain.
-/

namespace JSP000404Research
namespace DirectionData

open scoped BigOperators

def leftChildExponent
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (exponent : V → ℕ)
    (v : V) : ℕ :=
  if HighSource D n v then exponent v else exponent v - 1

def rightChildExponent
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (exponent : V → ℕ)
    (v : V) : ℕ :=
  if HighSink D n v then exponent v else exponent v - 1

def leftChildWeight
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (exponent : V → ℕ)
    (v : V) : ℕ :=
  if ¬ HighSink D n v then
    2 ^ leftChildExponent D n exponent v
  else 0

def rightChildWeight
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (exponent : V → ℕ)
    (v : V) : ℕ :=
  if ¬ HighSource D n v then
    2 ^ rightChildExponent D n exponent v
  else 0

/-- Two copies of the decremented natural exponent dominate one original
dyadic weight. -/
theorem pow_le_two_decremented_copies
    (k : ℕ) :
    2 ^ k ≤ 2 ^ (k - 1) + 2 ^ (k - 1) := by
  cases k with
  | zero =>
      norm_num
  | succ k =>
      simp [pow_succ]
      omega

/-- Pointwise mass accounting for the overlapping residual children. -/
theorem root_weight_le_child_weights
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (exponent : V → ℕ)
    (v : V) :
    2 ^ exponent v ≤
      leftChildWeight D n exponent v +
        rightChildWeight D n exponent v := by
  by_cases hsrc : HighSource D n v
  · have hnotSink : ¬ HighSink D n v := by
      intro hsink
      exact (not_highSource_and_highSink
        D hwidth hdelta v) ⟨hsrc, hsink⟩
    simp [leftChildWeight, rightChildWeight,
      leftChildExponent, rightChildExponent,
      hsrc, hnotSink]
  · by_cases hsink : HighSink D n v
    · simp [leftChildWeight, rightChildWeight,
        leftChildExponent, rightChildExponent,
        hsrc, hsink]
    · simp only [leftChildWeight, rightChildWeight,
        leftChildExponent, rightChildExponent,
        hsrc, hsink, not_false_eq_true, if_true, if_false]
      exact pow_le_two_decremented_copies (exponent v)

/-- Global mass accounting. -/
theorem root_mass_le_residual_children
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (exponent : V → ℕ) :
    (∑ v, 2 ^ exponent v) ≤
      (∑ v, leftChildWeight D n exponent v) +
      (∑ v, rightChildWeight D n exponent v) := by
  have hsum :
      (∑ v, 2 ^ exponent v) ≤
        ∑ v,
          (leftChildWeight D n exponent v +
            rightChildWeight D n exponent v) := by
    exact Finset.sum_le_sum fun v _ =>
      root_weight_le_child_weights
        D hwidth hdelta exponent v
  rw [Finset.sum_add_distrib] at hsum
  exact hsum

/-- The desired sharp capacity follows from half-capacity bounds on the two
recursive children. -/
theorem root_capacity_of_two_child_capacities
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (exponent : V → ℕ)
    (hn : 1 ≤ n)
    (hleft :
      (∑ v, leftChildWeight D n exponent v) ≤
        2 ^ (n - 1))
    (hright :
      (∑ v, rightChildWeight D n exponent v) ≤
        2 ^ (n - 1)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hroot :=
    root_mass_le_residual_children
      D hwidth hdelta exponent
  have hpow :
      2 ^ n = 2 * 2 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ m =>
        simp [pow_succ, Nat.add_comm]
  rw [hpow]
  omega

/-- If the original exponent is strictly below n, every child exponent is at
most n-1. -/
theorem leftChildExponent_le_pred
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    {n : ℕ} (exponent : V → ℕ)
    (hexp : ∀ v, exponent v < n)
    (v : V) :
    leftChildExponent D n exponent v ≤ n - 1 := by
  unfold leftChildExponent
  split_ifs <;> have h := hexp v <;> omega

theorem rightChildExponent_le_pred
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    {n : ℕ} (exponent : V → ℕ)
    (hexp : ∀ v, exponent v < n)
    (v : V) :
    rightChildExponent D n exponent v ≤ n - 1 := by
  unfold rightChildExponent
  split_ifs <;> have h := hexp v <;> omega

#print axioms pow_le_two_decremented_copies
#print axioms root_weight_le_child_weights
#print axioms root_mass_le_residual_children
#print axioms root_capacity_of_two_child_capacities
#print axioms leftChildExponent_le_pred
#print axioms rightChildExponent_le_pred

end DirectionData
end JSP000404Research
