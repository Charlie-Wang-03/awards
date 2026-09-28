import PC5488.Basic

namespace PC5488

/-- Casting a natural quotient to `ℚ` is bounded by the corresponding rational quotient. -/
theorem nat_div_cast_le_div
    (k r : ℕ) (hr : 0 < r) :
    ((k / r : ℕ) : ℚ) ≤ (k : ℚ) / (r : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hr)).2
  exact_mod_cast (Nat.div_mul_le_self k r)

/-- Integer version of the four-reciprocal estimate: the four quotient terms fit
strictly below `k`, hence at most `k - 1`. -/
theorem four_div_sum_le_sub_one
    {k r₁ r₂ r₃ r₄ : ℕ}
    (hk : 0 < k)
    (h3 : 3 ≤ r₁)
    (h12 : r₁ < r₂)
    (h23 : r₂ < r₃)
    (h34 : r₃ < r₄) :
    k / r₁ + k / r₂ + k / r₃ + k / r₄ ≤ k - 1 := by
  have hr₁ : 0 < r₁ := by omega
  have hr₂ : 0 < r₂ := by omega
  have hr₃ : 0 < r₃ := by omega
  have hr₄ : 0 < r₄ := by omega
  have h1 := nat_div_cast_le_div k r₁ hr₁
  have h2 := nat_div_cast_le_div k r₂ hr₂
  have h3' := nat_div_cast_le_div k r₃ hr₃
  have h4 := nat_div_cast_le_div k r₄ hr₄
  have hrec := four_reciprocal_lt_one h3 h12 h23 h34
  have hkq : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hrat :
      (k : ℚ) / (r₁ : ℚ) + (k : ℚ) / (r₂ : ℚ) +
          (k : ℚ) / (r₃ : ℚ) + (k : ℚ) / (r₄ : ℚ) < (k : ℚ) := by
    calc
      (k : ℚ) / (r₁ : ℚ) + (k : ℚ) / (r₂ : ℚ) +
          (k : ℚ) / (r₃ : ℚ) + (k : ℚ) / (r₄ : ℚ)
          = (k : ℚ) *
              (1 / (r₁ : ℚ) + 1 / (r₂ : ℚ) + 1 / (r₃ : ℚ) + 1 / (r₄ : ℚ)) := by
                ring
      _ < (k : ℚ) * 1 := mul_lt_mul_of_pos_left hrec hkq
      _ = (k : ℚ) := by ring
  have hcast :
      ((k / r₁ + k / r₂ + k / r₃ + k / r₄ : ℕ) : ℚ) < (k : ℚ) := by
    push_cast
    linarith
  have hnat : k / r₁ + k / r₂ + k / r₃ + k / r₄ < k := by
    exact_mod_cast hcast
  omega

/-- Per-generator overlap estimate used by the Bonferroni proof. -/
theorem overlap_row_le
    {qi r₁ r₂ r₃ r₄ n : ℕ}
    (hqi : 0 < qi)
    (hqin : qi ≤ n)
    (h3 : 3 ≤ r₁)
    (h12 : r₁ < r₂)
    (h23 : r₂ < r₃)
    (h34 : r₃ < r₄) :
    n / (qi * r₁) + n / (qi * r₂) + n / (qi * r₃) + n / (qi * r₄)
      ≤ n / qi - 1 := by
  have hk : 0 < n / qi := by
    have hk1 : 1 ≤ n / qi := (Nat.one_le_div_iff hqi).2 hqin
    omega
  rw [← nested_div n qi r₁, ← nested_div n qi r₂,
      ← nested_div n qi r₃, ← nested_div n qi r₄]
  exact four_div_sum_le_sub_one hk h3 h12 h23 h34

end PC5488
