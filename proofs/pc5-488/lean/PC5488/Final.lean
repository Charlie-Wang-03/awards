import PC5488.Bonferroni

namespace PC5488

/-- Reciprocal-density proxy used in the final sandwich. -/
def S (q₁ q₂ q₃ q₄ q₅ : ℕ) : ℚ :=
  1 / (q₁ : ℚ) + 1 / (q₂ : ℚ) + 1 / (q₃ : ℚ) + 1 / (q₄ : ℚ) + 1 / (q₅ : ℚ)

/-- The rational quotient lies strictly below one more than the natural quotient. -/
theorem div_lt_natDiv_add_one
    (n q : ℕ) (hq : 0 < q) :
    (n : ℚ) / (q : ℚ) < ((n / q : ℕ) : ℚ) + 1 := by
  have hnat : n < (n / q + 1) * q := by
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (n / q))
  apply (div_lt_iff₀ (by exact_mod_cast hq)).2
  exact_mod_cast hnat

/-- Summing the five strict floor inequalities gives `nS < M + 5`. -/
theorem n_mul_S_lt_M_add_five
    {q₁ q₂ q₃ q₄ q₅ n : ℕ}
    (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂)
    (hq₃ : 0 < q₃)
    (hq₄ : 0 < q₄)
    (hq₅ : 0 < q₅) :
    (n : ℚ) * S q₁ q₂ q₃ q₄ q₅ < (M q₁ q₂ q₃ q₄ q₅ n : ℚ) + 5 := by
  have h1 := div_lt_natDiv_add_one n q₁ hq₁
  have h2 := div_lt_natDiv_add_one n q₂ hq₂
  have h3 := div_lt_natDiv_add_one n q₃ hq₃
  have h4 := div_lt_natDiv_add_one n q₄ hq₄
  have h5 := div_lt_natDiv_add_one n q₅ hq₅
  calc
    (n : ℚ) * S q₁ q₂ q₃ q₄ q₅ =
        (n : ℚ) / q₁ + (n : ℚ) / q₂ + (n : ℚ) / q₃ +
          (n : ℚ) / q₄ + (n : ℚ) / q₅ := by
            simp [S]
            ring
    _ < (((n / q₁ : ℕ) : ℚ) + 1) + (((n / q₂ : ℕ) : ℚ) + 1) +
          (((n / q₃ : ℕ) : ℚ) + 1) + (((n / q₄ : ℕ) : ℚ) + 1) +
          (((n / q₅ : ℕ) : ℚ) + 1) := by
            linarith
    _ = (M q₁ q₂ q₃ q₄ q₅ n : ℚ) + 5 := by
          simp [M]
          ring

/-- Bonferroni plus the double-counted overlap margin gives `M + 5 ≤ 2F`. -/
theorem M_add_five_le_two_count
    {q₁ q₂ q₃ q₄ q₅ n : ℕ}
    (h3 : 3 ≤ q₁)
    (h12 : q₁ < q₂)
    (h23 : q₂ < q₃)
    (h34 : q₃ < q₄)
    (h45 : q₄ < q₅)
    (h5n : q₅ ≤ n)
    (hc12 : Nat.Coprime q₁ q₂)
    (hc13 : Nat.Coprime q₁ q₃)
    (hc14 : Nat.Coprime q₁ q₄)
    (hc15 : Nat.Coprime q₁ q₅)
    (hc23 : Nat.Coprime q₂ q₃)
    (hc24 : Nat.Coprime q₂ q₄)
    (hc25 : Nat.Coprime q₂ q₅)
    (hc34 : Nat.Coprime q₃ q₄)
    (hc35 : Nat.Coprime q₃ q₅)
    (hc45 : Nat.Coprime q₄ q₅) :
    M q₁ q₂ q₃ q₄ q₅ n + 5 ≤
      2 * countMultiples5 q₁ q₂ q₃ q₄ q₅ n := by
  have hagg := two_D_add_five_le_M h3 h12 h23 h34 h45 h5n
  have hbon := M_le_count_add_D (n := n)
    hc12 hc13 hc14 hc15 hc23 hc24 hc25 hc34 hc35 hc45
  omega

/-- The strict lower-density half of the sandwich: `nS < 2F(n)`. -/
theorem n_mul_S_lt_two_count
    {q₁ q₂ q₃ q₄ q₅ n : ℕ}
    (h3 : 3 ≤ q₁)
    (h12 : q₁ < q₂)
    (h23 : q₂ < q₃)
    (h34 : q₃ < q₄)
    (h45 : q₄ < q₅)
    (h5n : q₅ ≤ n)
    (hc12 : Nat.Coprime q₁ q₂)
    (hc13 : Nat.Coprime q₁ q₃)
    (hc14 : Nat.Coprime q₁ q₄)
    (hc15 : Nat.Coprime q₁ q₅)
    (hc23 : Nat.Coprime q₂ q₃)
    (hc24 : Nat.Coprime q₂ q₄)
    (hc25 : Nat.Coprime q₂ q₅)
    (hc34 : Nat.Coprime q₃ q₄)
    (hc35 : Nat.Coprime q₃ q₅)
    (hc45 : Nat.Coprime q₄ q₅) :
    (n : ℚ) * S q₁ q₂ q₃ q₄ q₅ <
      2 * (countMultiples5 q₁ q₂ q₃ q₄ q₅ n : ℚ) := by
  have hq₁ : 0 < q₁ := by omega
  have hq₂ : 0 < q₂ := by omega
  have hq₃ : 0 < q₃ := by omega
  have hq₄ : 0 < q₄ := by omega
  have hq₅ : 0 < q₅ := by omega
  have hfloor := n_mul_S_lt_M_add_five (n := n) hq₁ hq₂ hq₃ hq₄ hq₅
  have hcount := M_add_five_le_two_count
    h3 h12 h23 h34 h45 h5n hc12 hc13 hc14 hc15 hc23 hc24 hc25 hc34 hc35 hc45
  have hcountQ :
      (M q₁ q₂ q₃ q₄ q₅ n : ℚ) + 5 ≤
        2 * (countMultiples5 q₁ q₂ q₃ q₄ q₅ n : ℚ) := by
    exact_mod_cast hcount
  exact hfloor.trans_le hcountQ

/-- Elementary five-set union upper bound. -/
theorem card_union5_le_sum
    {α : Type*} [DecidableEq α]
    (A B C D E : Finset α) :
    ((((A ∪ B) ∪ C) ∪ D) ∪ E).card ≤
      A.card + B.card + C.card + D.card + E.card := by
  have h2 := Finset.card_union_le A B
  have h3 := Finset.card_union_le (A ∪ B) C
  have h4 := Finset.card_union_le ((A ∪ B) ∪ C) D
  have h5 := Finset.card_union_le (((A ∪ B) ∪ C) ∪ D) E
  omega

/-- Union bound in natural-number floor form: `F(m) ≤ M(m)`. -/
theorem count_le_M
    (q₁ q₂ q₃ q₄ q₅ m : ℕ) :
    countMultiples5 q₁ q₂ q₃ q₄ q₅ m ≤ M q₁ q₂ q₃ q₄ q₅ m := by
  have h := card_union5_le_sum
    (multiplesUpTo q₁ m) (multiplesUpTo q₂ m) (multiplesUpTo q₃ m)
    (multiplesUpTo q₄ m) (multiplesUpTo q₅ m)
  have hsupp := support5_eq_union_multiples q₁ q₂ q₃ q₄ q₅ m
  rw [← hsupp] at h
  simp only [card_multiplesUpTo] at h
  simpa [countMultiples5, M] using h

/-- Floor union bound compared with reciprocal density: `F(m) ≤ mS`. -/
theorem count_cast_le_mul_S
    {q₁ q₂ q₃ q₄ q₅ m : ℕ}
    (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂)
    (hq₃ : 0 < q₃)
    (hq₄ : 0 < q₄)
    (hq₅ : 0 < q₅) :
    (countMultiples5 q₁ q₂ q₃ q₄ q₅ m : ℚ) ≤
      (m : ℚ) * S q₁ q₂ q₃ q₄ q₅ := by
  have hcountNat := count_le_M q₁ q₂ q₃ q₄ q₅ m
  have hcountQ :
      (countMultiples5 q₁ q₂ q₃ q₄ q₅ m : ℚ) ≤
        (M q₁ q₂ q₃ q₄ q₅ m : ℚ) := by
    exact_mod_cast hcountNat
  have h1 := nat_div_cast_le_div m q₁ hq₁
  have h2 := nat_div_cast_le_div m q₂ hq₂
  have h3 := nat_div_cast_le_div m q₃ hq₃
  have h4 := nat_div_cast_le_div m q₄ hq₄
  have h5 := nat_div_cast_le_div m q₅ hq₅
  have hM :
      (M q₁ q₂ q₃ q₄ q₅ m : ℚ) ≤ (m : ℚ) * S q₁ q₂ q₃ q₄ q₅ := by
    calc
      (M q₁ q₂ q₃ q₄ q₅ m : ℚ) =
          ((m / q₁ : ℕ) : ℚ) + ((m / q₂ : ℕ) : ℚ) + ((m / q₃ : ℕ) : ℚ) +
            ((m / q₄ : ℕ) : ℚ) + ((m / q₅ : ℕ) : ℚ) := by
              simp [M]
      _ ≤ (m : ℚ) / q₁ + (m : ℚ) / q₂ + (m : ℚ) / q₃ +
            (m : ℚ) / q₄ + (m : ℚ) / q₅ := by
              linarith
      _ = (m : ℚ) * S q₁ q₂ q₃ q₄ q₅ := by
            simp [S]
            ring
  exact hcountQ.trans hM

/-- Full target in the nontrivial `q₁ ≥ 3` branch. -/
theorem target_of_ge_three
    {q₁ q₂ q₃ q₄ q₅ m n : ℕ}
    (hm : 0 < m)
    (h3 : 3 ≤ q₁)
    (h12 : q₁ < q₂)
    (h23 : q₂ < q₃)
    (h34 : q₃ < q₄)
    (h45 : q₄ < q₅)
    (h5n : q₅ ≤ n)
    (hc12 : Nat.Coprime q₁ q₂)
    (hc13 : Nat.Coprime q₁ q₃)
    (hc14 : Nat.Coprime q₁ q₄)
    (hc15 : Nat.Coprime q₁ q₅)
    (hc23 : Nat.Coprime q₂ q₃)
    (hc24 : Nat.Coprime q₂ q₄)
    (hc25 : Nat.Coprime q₂ q₅)
    (hc34 : Nat.Coprime q₃ q₄)
    (hc35 : Nat.Coprime q₃ q₅)
    (hc45 : Nat.Coprime q₄ q₅) :
    n * countMultiples5 q₁ q₂ q₃ q₄ q₅ m <
      2 * m * countMultiples5 q₁ q₂ q₃ q₄ q₅ n := by
  have hq₁ : 0 < q₁ := by omega
  have hq₂ : 0 < q₂ := by omega
  have hq₃ : 0 < q₃ := by omega
  have hq₄ : 0 < q₄ := by omega
  have hq₅ : 0 < q₅ := by omega
  have hn : 0 < n := by omega
  have hupper := count_cast_le_mul_S (m := m) hq₁ hq₂ hq₃ hq₄ hq₅
  have hlower := n_mul_S_lt_two_count
    h3 h12 h23 h34 h45 h5n hc12 hc13 hc14 hc15 hc23 hc24 hc25 hc34 hc35 hc45
  have hnq : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hrat :
      (n : ℚ) * (countMultiples5 q₁ q₂ q₃ q₄ q₅ m : ℚ) <
        2 * (m : ℚ) * (countMultiples5 q₁ q₂ q₃ q₄ q₅ n : ℚ) := by
    calc
      (n : ℚ) * (countMultiples5 q₁ q₂ q₃ q₄ q₅ m : ℚ)
          ≤ (n : ℚ) * ((m : ℚ) * S q₁ q₂ q₃ q₄ q₅) :=
            mul_le_mul_of_nonneg_left hupper hnq
      _ = (m : ℚ) * ((n : ℚ) * S q₁ q₂ q₃ q₄ q₅) := by ring
      _ < (m : ℚ) * (2 * (countMultiples5 q₁ q₂ q₃ q₄ q₅ n : ℚ)) :=
            mul_lt_mul_of_pos_left hlower hmq
      _ = 2 * (m : ℚ) * (countMultiples5 q₁ q₂ q₃ q₄ q₅ n : ℚ) := by ring
  exact_mod_cast hrat

/-- Complete strengthened PC5-488 theorem: `m > n` is not needed; positivity of `m`
suffices once `n ≥ q₅`. -/
theorem pc5_488
    {q₁ q₂ q₃ q₄ q₅ m n : ℕ}
    (hm : 0 < m)
    (h2 : 2 ≤ q₁)
    (h12 : q₁ < q₂)
    (h23 : q₂ < q₃)
    (h34 : q₃ < q₄)
    (h45 : q₄ < q₅)
    (h5n : q₅ ≤ n)
    (hc12 : Nat.Coprime q₁ q₂)
    (hc13 : Nat.Coprime q₁ q₃)
    (hc14 : Nat.Coprime q₁ q₄)
    (hc15 : Nat.Coprime q₁ q₅)
    (hc23 : Nat.Coprime q₂ q₃)
    (hc24 : Nat.Coprime q₂ q₄)
    (hc25 : Nat.Coprime q₂ q₅)
    (hc34 : Nat.Coprime q₃ q₄)
    (hc35 : Nat.Coprime q₃ q₅)
    (hc45 : Nat.Coprime q₄ q₅) :
    n * countMultiples5 q₁ q₂ q₃ q₄ q₅ m <
      2 * m * countMultiples5 q₁ q₂ q₃ q₄ q₅ n := by
  by_cases hfirst : q₁ = 2
  · subst q₁
    have hq₂pos : 0 < q₂ := by omega
    have hq₂n : q₂ ≤ n := by omega
    exact target_of_two hm hq₂pos hq₂n hc12
  · have h3 : 3 ≤ q₁ := by omega
    exact target_of_ge_three hm h3 h12 h23 h34 h45 h5n
      hc12 hc13 hc14 hc15 hc23 hc24 hc25 hc34 hc35 hc45

end PC5488
