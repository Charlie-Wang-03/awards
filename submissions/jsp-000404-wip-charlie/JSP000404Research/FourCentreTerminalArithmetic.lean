import Mathlib.Tactic

/-!
# Four-centre dyadic terminal arithmetic

For n>=3, the Sendov four-centre extremal dyadic profile is

  n-1, n-2, n-3, n-3,

whose weight is exactly 2^n.

This file isolates the purely natural-number arithmetic.  Geometry only has to
show that, once one sharp exponent n-1 is present, the other three exponents
are at most n-2 and at most one of them can equal n-2 (or close the remaining
case by a compensated deletion).
-/

namespace JSP000404Research

theorem four_extremal_dyadic_eq
    {n : ℕ} (hn : 3 ≤ n) :
    2 ^ (n - 1) + 2 ^ (n - 2) +
        2 ^ (n - 3) + 2 ^ (n - 3) =
      2 ^ n := by
  let m := n - 3
  have hnEq : n = m + 3 := by
    dsimp [m]
    omega
  rw [hnEq]
  simp [pow_succ]
  ring

/-- If there is no sharp layer, four exponents at most n-2 already fit. -/
theorem four_dyadic_le_of_all_le_n_sub_two
    {n k0 k1 k2 k3 : ℕ}
    (hn : 2 ≤ n)
    (h0 : k0 ≤ n - 2)
    (h1 : k1 ≤ n - 2)
    (h2 : k2 ≤ n - 2)
    (h3 : k3 ≤ n - 2) :
    2 ^ k0 + 2 ^ k1 + 2 ^ k2 + 2 ^ k3 ≤ 2 ^ n := by
  have hp :
      ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hab
  have hp0 := hp h0
  have hp1 := hp h1
  have hp2 := hp h2
  have hp3 := hp h3
  have hbase :
      2 ^ k0 + 2 ^ k1 + 2 ^ k2 + 2 ^ k3
        ≤ 4 * 2 ^ (n - 2) := by
    omega
  have heq : 4 * 2 ^ (n - 2) = 2 ^ n := by
    let m := n - 2
    have hnEq : n = m + 2 := by
      dsimp [m]
      omega
    rw [hnEq]
    simp [pow_succ]
    ring
  rwa [heq] at hbase

/-- With one sharp exponent n-1, at most one n-2 exponent among the remaining
three gives the exact four-centre capacity. -/
theorem four_dyadic_le_of_one_top_atMostOne_next
    {n k1 k2 k3 : ℕ}
    (hn : 3 ≤ n)
    (h1 : k1 ≤ n - 2)
    (h2 : k2 ≤ n - 2)
    (h3 : k3 ≤ n - 2)
    (h12 : ¬ (k1 = n - 2 ∧ k2 = n - 2))
    (h13 : ¬ (k1 = n - 2 ∧ k3 = n - 2))
    (h23 : ¬ (k2 = n - 2 ∧ k3 = n - 2)) :
    2 ^ (n - 1) + 2 ^ k1 + 2 ^ k2 + 2 ^ k3 ≤ 2 ^ n := by
  have hp :
      ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hab
  by_cases hk1 : k1 = n - 2
  · have hk2 : k2 ≤ n - 3 := by
      have hne : k2 ≠ n - 2 := by
        intro h
        exact h12 ⟨hk1, h⟩
      omega
    have hk3 : k3 ≤ n - 3 := by
      have hne : k3 ≠ n - 2 := by
        intro h
        exact h13 ⟨hk1, h⟩
      omega
    have hp2 := hp hk2
    have hp3 := hp hk3
    rw [hk1]
    calc
      2 ^ (n - 1) + 2 ^ (n - 2) + 2 ^ k2 + 2 ^ k3
          ≤
        2 ^ (n - 1) + 2 ^ (n - 2) +
          2 ^ (n - 3) + 2 ^ (n - 3) := by
            omega
      _ = 2 ^ n := four_extremal_dyadic_eq hn
  · by_cases hk2 : k2 = n - 2
    · have hk1' : k1 ≤ n - 3 := by omega
      have hk3' : k3 ≤ n - 3 := by
        have hne : k3 ≠ n - 2 := by
          intro h
          exact h23 ⟨hk2, h⟩
        omega
      have hp1 := hp hk1'
      have hp3 := hp hk3'
      rw [hk2]
      calc
        2 ^ (n - 1) + 2 ^ k1 + 2 ^ (n - 2) + 2 ^ k3
            ≤
          2 ^ (n - 1) + 2 ^ (n - 3) +
            2 ^ (n - 2) + 2 ^ (n - 3) := by
              omega
        _ = 2 ^ n := by
          rw [← four_extremal_dyadic_eq hn]
          omega
    · by_cases hk3 : k3 = n - 2
      · have hk1' : k1 ≤ n - 3 := by omega
        have hk2' : k2 ≤ n - 3 := by omega
        have hp1 := hp hk1'
        have hp2 := hp hk2'
        rw [hk3]
        calc
          2 ^ (n - 1) + 2 ^ k1 + 2 ^ k2 + 2 ^ (n - 2)
              ≤
            2 ^ (n - 1) + 2 ^ (n - 3) +
              2 ^ (n - 3) + 2 ^ (n - 2) := by
                omega
          _ = 2 ^ n := by
            rw [← four_extremal_dyadic_eq hn]
            omega
      · have hk1' : k1 ≤ n - 3 := by omega
        have hk2' : k2 ≤ n - 3 := by omega
        have hk3' : k3 ≤ n - 3 := by omega
        have hp1 := hp hk1'
        have hp2 := hp hk2'
        have hp3 := hp hk3'
        have hnext :
            2 ^ (n - 3) ≤ 2 ^ (n - 2) := by
          apply hp
          omega
        calc
          2 ^ (n - 1) + 2 ^ k1 + 2 ^ k2 + 2 ^ k3
              ≤
            2 ^ (n - 1) + 2 ^ (n - 3) +
              2 ^ (n - 3) + 2 ^ (n - 3) := by
                omega
          _ ≤
            2 ^ (n - 1) + 2 ^ (n - 2) +
              2 ^ (n - 3) + 2 ^ (n - 3) := by
                omega
          _ = 2 ^ n := four_extremal_dyadic_eq hn

#print axioms four_extremal_dyadic_eq
#print axioms four_dyadic_le_of_all_le_n_sub_two
#print axioms four_dyadic_le_of_one_top_atMostOne_next

end JSP000404Research
