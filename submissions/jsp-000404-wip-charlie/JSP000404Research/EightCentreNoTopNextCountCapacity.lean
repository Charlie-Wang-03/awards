import JSP000404Research.EightCentreNoHighLayerCapacity
import Mathlib.Tactic

/-!
# A sharp cardinality/next-layer trade-off below the top dyadic layer

If the top n-1 layer is absent, all actual exponents are <= n-2.
Let m be the total number of centres and r the number with exponent
exactly n-2. Every other centre has exponent <= n-3. Hence

  sum_i 2^(k i) <= (m+r) * 2^(n-3).

Whenever m+r <= 8, this proves the original dyadic capacity.
No arbitrary AngleCap configuration is asserted to satisfy m+r <= 8.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Genuine finite-profile capacity with a *weighted* cardinality of
second-layer centres, rather than requiring every exponent <= n-3. -/
theorem dyadic_capacity_of_no_top_next_count_tradeoff
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ)
    (hn : 3 ≤ n)
    (hmax : ∀ i : V, k i ≤ n - 2)
    (htrade : Fintype.card V +
      ((Finset.univ : Finset V).filter (fun i => k i = n - 2)).card ≤ 8) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let H : Finset V :=
    (Finset.univ : Finset V).filter (fun i => k i = n - 2)
  have hpowNext :
      2 ^ (n - 2) = 2 ^ (n - 3) + 2 ^ (n - 3) := by
    calc
      2 ^ (n - 2) = 2 ^ ((n - 3) + 1) := by congr 1 <;> omega
      _ = 2 ^ (n - 3) + 2 ^ (n - 3) := by
        rw [pow_add]
        norm_num
        omega
  have hpoint : ∀ i : V,
      2 ^ k i ≤
        2 ^ (n - 3) +
          (if k i = n - 2 then 2 ^ (n - 3) else 0) := by
    intro i
    by_cases hi : k i = n - 2
    · simpa [hi] using (le_of_eq hpowNext)
    · have hsmall : k i ≤ n - 3 := by
        have hle := hmax i
        omega
      simp only [if_neg hi, add_zero]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
  have hsum : (∑ i : V, 2 ^ k i) ≤
      ∑ i : V,
        (2 ^ (n - 3) +
          (if k i = n - 2 then 2 ^ (n - 3) else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  have hfilter :
      (∑ i : V, if k i = n - 2 then 2 ^ (n - 3) else 0) =
      H.card * 2 ^ (n - 3) := by
    simp [H, Finset.sum_ite]
  have hbudget : 8 * 2 ^ (n - 3) = 2 ^ n := by
    calc
      8 * 2 ^ (n - 3) = 2 ^ 3 * 2 ^ (n - 3) := by norm_num
      _ = 2 ^ (3 + (n - 3)) := by rw [← pow_add]
      _ = 2 ^ n := by congr 1 <;> omega
  calc
    (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (2 ^ (n - 3) +
          (if k i = n - 2 then 2 ^ (n - 3) else 0)) := hsum
    _ = (Fintype.card V + H.card) * 2 ^ (n - 3) := by
      rw [Finset.sum_add_distrib, hfilter]
      simp [add_mul]
    _ ≤ 8 * 2 ^ (n - 3) := by
      exact Nat.mul_le_mul_right _ (by simpa [H] using htrade)
    _ = 2 ^ n := hbudget

/-- True AngleCap exponent-profile certificate. The absence of the
top layer is the additional geometric profile premise; the tradeoff
counts actual next-to-top centres, not synthetic hole credits. -/
theorem planar_no_top_next_count_tradeoff_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hnoTop : ∀ i : V, centreExponent (C i) t ≠ n - 1)
    (htrade : Fintype.card V +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 2)).card ≤ 8) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have hmax : ∀ i : V, centreExponent (C i) t ≤ n - 2 := by
    intro i
    have hi : centreExponent (C i) t < n :=
      centreExponent_lt_n (C i) n delta t
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht
    have hnTop := hnoTop i
    omega
  exact dyadic_capacity_of_no_top_next_count_tradeoff
    (fun i : V => centreExponent (C i) t) n hn hmax htrade

#print axioms dyadic_capacity_of_no_top_next_count_tradeoff
#print axioms planar_no_top_next_count_tradeoff_capacity

end JSP000404Research
