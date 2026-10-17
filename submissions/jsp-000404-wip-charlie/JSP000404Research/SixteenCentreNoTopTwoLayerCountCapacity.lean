import JSP000404Research.EightCentreNoTopNextCountCapacity
import Mathlib.Tactic

/-!
# Two-layer refined dyadic accounting with no top exponent

For n >= 4 and absent exponent n-1, let
  m = |V|,
  r = #{i | k i = n-2},
  q = #{i | k i = n-3}.
Every other exponent is <= n-4, hence
  sum_i 2^k <= (m + 3*r + q)*2^(n-4).
In particular m + 3*r + q <= 16 suffices for capacity.

The latter is an explicit, independently checkable condition on
actual centre exponents, not a universally derived AngleCap property.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Sharp arithmetic two-high-layer profile budget in units of 2^(n-4). -/
theorem dyadic_capacity_of_no_top_two_layer_count_tradeoff
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ)
    (hn : 4 ≤ n)
    (hmax : ∀ i : V, k i ≤ n - 2)
    (htrade : Fintype.card V +
      3 * ((Finset.univ : Finset V).filter (fun i => k i = n - 2)).card +
      ((Finset.univ : Finset V).filter (fun i => k i = n - 3)).card ≤ 16) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let H : Finset V :=
    (Finset.univ : Finset V).filter (fun i => k i = n - 2)
  let M : Finset V :=
    (Finset.univ : Finset V).filter (fun i => k i = n - 3)
  let B : ℕ := 2 ^ (n - 4)
  have hhi : 2 ^ (n - 2) = 4 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
    norm_num [mul_comm]
  have hmid : 2 ^ (n - 3) = 2 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 3 = (n - 4) + 1 by omega, pow_add]
    norm_num [mul_comm]
  have hpoint : ∀ i : V,
      2 ^ k i ≤ B +
        (if k i = n - 2 then 3 * B else 0) +
        (if k i = n - 3 then B else 0) := by
    intro i
    by_cases hiH : k i = n - 2
    · have hiM : k i ≠ n - 3 := by omega
      simp only [if_pos hiH, if_neg hiM]
      rw [hiH, hhi]
      omega
    · by_cases hiM : k i = n - 3
      · simp only [if_neg hiH, if_pos hiM]
        rw [hiM, hmid]
        omega
      · have hlo : k i ≤ n - 4 := by
          have hbound := hmax i
          omega
        simp only [if_neg hiH, if_neg hiM, add_zero]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hlo
  have hsumBound :
      (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (B +
          (if k i = n - 2 then 3 * B else 0) +
          (if k i = n - 3 then B else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  have hH :
      (∑ i : V, if k i = n - 2 then 3 * B else 0) =
        H.card * (3 * B) := by
    simp [H, Finset.sum_ite]
  have hM :
      (∑ i : V, if k i = n - 3 then B else 0) =
        M.card * B := by
    simp [M, Finset.sum_ite]
  have hsumEq :
      (∑ i : V, (B +
          (if k i = n - 2 then 3 * B else 0) +
          (if k i = n - 3 then B else 0))) =
        (Fintype.card V + 3 * H.card + M.card) * B := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hH, hM]
    simp [add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hBudget : 16 * B = 2 ^ n := by
    dsimp [B]
    calc
      16 * 2 ^ (n - 4) = 2 ^ 4 * 2 ^ (n - 4) := by norm_num
      _ = 2 ^ (4 + (n - 4)) := by rw [← pow_add]
      _ = 2 ^ n := by congr 1 <;> omega
  calc
    (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (B +
          (if k i = n - 2 then 3 * B else 0) +
          (if k i = n - 3 then B else 0)) := hsumBound
    _ = (Fintype.card V + 3 * H.card + M.card) * B := hsumEq
    _ ≤ 16 * B := Nat.mul_le_mul_right _ (by simpa [H, M] using htrade)
    _ = 2 ^ n := hBudget

/-- Real planar AngleCap version, based on the proven universal
centreExponent_lt_n and an explicitly absent top n-1 layer. -/
theorem planar_no_top_two_layer_count_tradeoff_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hnoTop : ∀ i : V, centreExponent (C i) t ≠ n - 1)
    (htrade : Fintype.card V +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3)).card ≤ 16) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have hmax : ∀ i : V, centreExponent (C i) t ≤ n - 2 := by
    intro i
    have hi : centreExponent (C i) t < n :=
      centreExponent_lt_n (C i) n delta t
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht
    have hTop := hnoTop i
    omega
  exact dyadic_capacity_of_no_top_two_layer_count_tradeoff
    (fun i : V => centreExponent (C i) t) n hn hmax htrade

/-- Necessary two-high-layer census for an actual overweight configuration
whose top n-1 exponent layer is empty. This is the rigorous
contrapositive obstruction, not an assertion that such configurations
exist or satisfy AngleCap. -/
theorem planar_no_top_overweight_forces_two_layer_count_excess
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hnoTop : ∀ i : V, centreExponent (C i) t ≠ n - 1)
    (hover : 2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    16 < Fintype.card V +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3)).card := by
  classical
  by_contra hnot
  have htrade : Fintype.card V +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3)).card ≤ 16 := by
    omega
  have hcapacity :=
    planar_no_top_two_layer_count_tradeoff_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C hnoTop htrade
  exact (not_lt_of_ge hcapacity) hover

#print axioms dyadic_capacity_of_no_top_two_layer_count_tradeoff
#print axioms planar_no_top_two_layer_count_tradeoff_capacity
#print axioms planar_no_top_overweight_forces_two_layer_count_excess

end JSP000404Research
