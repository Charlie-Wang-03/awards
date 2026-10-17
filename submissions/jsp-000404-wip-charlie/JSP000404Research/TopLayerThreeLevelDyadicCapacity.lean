import JSP000404Research.SixteenCentreNoTopTwoLayerCountCapacity
import Mathlib.Tactic

/-!
# Exact top/next/third-layer cardinal census at dyadic resolution n-4

For n>=4, the true exponent profile of any actual finite planar
AngleCap centre cycle satisfies k(i)<n. Thus k(i)<=n-1.

Let m be total centre cardinal, r the number of top centres k=n-1,
q the number of next centres k=n-2, and u the number of third-layer
centres k=n-3. All remaining exponents are <=n-4.

Then sum_i 2^k(i) <= (m + 7*r + 3*q + u) * 2^(n-4).
This closes every configuration obeying m+7r+3q+u<=16
WITHOUT assuming top centres are absent and without crediting
synthetic holes or reusing paid surplus.

The census inequality is a genuine sufficient condition; it is
not claimed for all planar configurations.
-/

namespace JSP000404Research

open scoped BigOperators

theorem dyadic_capacity_of_top_three_layer_count_tradeoff
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ)
    (hn : 4 ≤ n)
    (hmax : ∀ i : V, k i ≤ n - 1)
    (htrade : Fintype.card V +
      7 * ((Finset.univ : Finset V).filter (fun i => k i = n - 1)).card +
      3 * ((Finset.univ : Finset V).filter (fun i => k i = n - 2)).card +
      ((Finset.univ : Finset V).filter (fun i => k i = n - 3)).card ≤ 16) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let H : Finset V :=
    (Finset.univ : Finset V).filter (fun i => k i = n - 1)
  let M : Finset V :=
    (Finset.univ : Finset V).filter (fun i => k i = n - 2)
  let L : Finset V :=
    (Finset.univ : Finset V).filter (fun i => k i = n - 3)
  let B : ℕ := 2 ^ (n - 4)
  have htop : 2 ^ (n - 1) = 8 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 1 = (n - 4) + 3 by omega, pow_add]
    norm_num [mul_comm]
  have hnext : 2 ^ (n - 2) = 4 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
    norm_num [mul_comm]
  have hthird : 2 ^ (n - 3) = 2 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 3 = (n - 4) + 1 by omega, pow_add]
    norm_num [mul_comm]
  have hpoint : ∀ i : V,
      2 ^ k i ≤ B +
        (if k i = n - 1 then 7 * B else 0) +
        (if k i = n - 2 then 3 * B else 0) +
        (if k i = n - 3 then B else 0) := by
    intro i
    by_cases hiH : k i = n - 1
    · have hiM : k i ≠ n - 2 := by omega
      have hiL : k i ≠ n - 3 := by omega
      simp only [if_pos hiH, if_neg hiM, if_neg hiL, add_zero]
      rw [hiH, htop]
      omega
    · by_cases hiM : k i = n - 2
      · have hiL : k i ≠ n - 3 := by omega
        simp only [if_neg hiH, if_pos hiM, if_neg hiL, add_zero]
        rw [hiM, hnext]
        omega
      · by_cases hiL : k i = n - 3
        · simp only [if_neg hiH, if_neg hiM, if_pos hiL, add_zero]
          rw [hiL, hthird]
          omega
        · have hlo : k i ≤ n - 4 := by
            have hbound := hmax i
            omega
          simp only [if_neg hiH, if_neg hiM, if_neg hiL, add_zero]
          exact Nat.pow_le_pow_right (by decide : 0 < 2) hlo
  have hsumBound :
      (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (B +
          (if k i = n - 1 then 7 * B else 0) +
          (if k i = n - 2 then 3 * B else 0) +
          (if k i = n - 3 then B else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  have hH :
      (∑ i : V, if k i = n - 1 then 7 * B else 0) =
        H.card * (7 * B) := by
    simp [H, Finset.sum_ite]
  have hM :
      (∑ i : V, if k i = n - 2 then 3 * B else 0) =
        M.card * (3 * B) := by
    simp [M, Finset.sum_ite]
  have hL :
      (∑ i : V, if k i = n - 3 then B else 0) =
        L.card * B := by
    simp [L, Finset.sum_ite]
  have hsumEq :
      (∑ i : V, (B +
          (if k i = n - 1 then 7 * B else 0) +
          (if k i = n - 2 then 3 * B else 0) +
          (if k i = n - 3 then B else 0))) =
        (Fintype.card V + 7 * H.card + 3 * M.card + L.card) * B := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hH, hM, hL]
    simp [add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hbudget : 16 * B = 2 ^ n := by
    dsimp [B]
    calc
      16 * 2 ^ (n - 4) = 2 ^ 4 * 2 ^ (n - 4) := by norm_num
      _ = 2 ^ (4 + (n - 4)) := by rw [← pow_add]
      _ = 2 ^ n := by congr 1 <;> omega
  calc
    (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (B +
          (if k i = n - 1 then 7 * B else 0) +
          (if k i = n - 2 then 3 * B else 0) +
          (if k i = n - 3 then B else 0)) := hsumBound
    _ = (Fintype.card V + 7 * H.card + 3 * M.card + L.card) * B := hsumEq
    _ ≤ 16 * B := Nat.mul_le_mul_right _ (by simpa [H,M,L] using htrade)
    _ = 2 ^ n := hbudget

theorem planar_top_three_layer_count_tradeoff_capacity
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
    (htrade : Fintype.card V +
      7 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 1)).card +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3)).card ≤ 16) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have hmax : ∀ i : V, centreExponent (C i) t ≤ n - 1 := by
    intro i
    have hlt : centreExponent (C i) t < n :=
      centreExponent_lt_n (C i) n delta t
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht
    omega
  exact dyadic_capacity_of_top_three_layer_count_tradeoff
    (fun i : V => centreExponent (C i) t) n hn hmax htrade

/-- Any genuine overweight configuration in the regime n>=4
must violate the explicitly counted top/next/third-layer budget. -/
theorem planar_overweight_forces_top_three_layer_count_excess
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
    (hover : 2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    16 < Fintype.card V +
      7 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 1)).card +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3)).card := by
  classical
  by_contra hntrade
  have htrade : Fintype.card V +
      7 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 1)).card +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3)).card ≤ 16 := by
    omega
  have hcapacity :=
    planar_top_three_layer_count_tradeoff_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C htrade
  exact (not_lt_of_ge hcapacity) hover

#print axioms dyadic_capacity_of_top_three_layer_count_tradeoff
#print axioms planar_top_three_layer_count_tradeoff_capacity
#print axioms planar_overweight_forces_top_three_layer_count_excess

end JSP000404Research
