import PC5488.Overlap

namespace PC5488

/-- Sum of the five single-generator counts `⌊n/qᵢ⌋`. -/
def M (q₁ q₂ q₃ q₄ q₅ n : ℕ) : ℕ :=
  n / q₁ + n / q₂ + n / q₃ + n / q₄ + n / q₅

/-- Sum of the ten pair-overlap counts `⌊n/(qᵢqⱼ)⌋`, with `i < j`. -/
def D (q₁ q₂ q₃ q₄ q₅ n : ℕ) : ℕ :=
  n / (q₁ * q₂) + n / (q₁ * q₃) + n / (q₁ * q₄) + n / (q₁ * q₅) +
  n / (q₂ * q₃) + n / (q₂ * q₄) + n / (q₂ * q₅) +
  n / (q₃ * q₄) + n / (q₃ * q₅) +
  n / (q₄ * q₅)

/-- Summing the five one-row overlap estimates counts every pair twice.

The statement is written as `2D + 5 ≤ M` rather than `2D ≤ M - 5` to avoid
truncated subtraction in `ℕ`. -/
theorem two_D_add_five_le_M
    {q₁ q₂ q₃ q₄ q₅ n : ℕ}
    (h3 : 3 ≤ q₁)
    (h12 : q₁ < q₂)
    (h23 : q₂ < q₃)
    (h34 : q₃ < q₄)
    (h45 : q₄ < q₅)
    (h5n : q₅ ≤ n) :
    2 * D q₁ q₂ q₃ q₄ q₅ n + 5 ≤ M q₁ q₂ q₃ q₄ q₅ n := by
  have hq₁ : 0 < q₁ := by omega
  have hq₂ : 0 < q₂ := by omega
  have hq₃ : 0 < q₃ := by omega
  have hq₄ : 0 < q₄ := by omega
  have hq₅ : 0 < q₅ := by omega
  have h1n : q₁ ≤ n := by omega
  have h2n : q₂ ≤ n := by omega
  have h3n : q₃ ≤ n := by omega
  have h4n : q₄ ≤ n := by omega

  have hk1 : 1 ≤ n / q₁ := (Nat.one_le_div_iff hq₁).2 h1n
  have hk2 : 1 ≤ n / q₂ := (Nat.one_le_div_iff hq₂).2 h2n
  have hk3 : 1 ≤ n / q₃ := (Nat.one_le_div_iff hq₃).2 h3n
  have hk4 : 1 ≤ n / q₄ := (Nat.one_le_div_iff hq₄).2 h4n
  have hk5 : 1 ≤ n / q₅ := (Nat.one_le_div_iff hq₅).2 h5n

  have row1 :
      n / (q₁ * q₂) + n / (q₁ * q₃) + n / (q₁ * q₄) + n / (q₁ * q₅)
        ≤ n / q₁ - 1 := by
    exact overlap_row_le hq₁ h1n (by omega) h23 h34 h45
  have row1plus :
      n / (q₁ * q₂) + n / (q₁ * q₃) + n / (q₁ * q₄) + n / (q₁ * q₅) + 1
        ≤ n / q₁ := by
    omega

  have row2raw := overlap_row_le
    (qi := q₂) (r₁ := q₁) (r₂ := q₃) (r₃ := q₄) (r₄ := q₅) (n := n)
    hq₂ h2n h3 (by omega) h34 h45
  rw [Nat.mul_comm q₂ q₁] at row2raw
  have row2 :
      n / (q₁ * q₂) + n / (q₂ * q₃) + n / (q₂ * q₄) + n / (q₂ * q₅)
        ≤ n / q₂ - 1 := row2raw
  have row2plus :
      n / (q₁ * q₂) + n / (q₂ * q₃) + n / (q₂ * q₄) + n / (q₂ * q₅) + 1
        ≤ n / q₂ := by
    omega

  have row3raw := overlap_row_le
    (qi := q₃) (r₁ := q₁) (r₂ := q₂) (r₃ := q₄) (r₄ := q₅) (n := n)
    hq₃ h3n h3 h12 (by omega) h45
  rw [Nat.mul_comm q₃ q₁, Nat.mul_comm q₃ q₂] at row3raw
  have row3 :
      n / (q₁ * q₃) + n / (q₂ * q₃) + n / (q₃ * q₄) + n / (q₃ * q₅)
        ≤ n / q₃ - 1 := row3raw
  have row3plus :
      n / (q₁ * q₃) + n / (q₂ * q₃) + n / (q₃ * q₄) + n / (q₃ * q₅) + 1
        ≤ n / q₃ := by
    omega

  have row4raw := overlap_row_le
    (qi := q₄) (r₁ := q₁) (r₂ := q₂) (r₃ := q₃) (r₄ := q₅) (n := n)
    hq₄ h4n h3 h12 h23 (by omega)
  rw [Nat.mul_comm q₄ q₁, Nat.mul_comm q₄ q₂, Nat.mul_comm q₄ q₃] at row4raw
  have row4 :
      n / (q₁ * q₄) + n / (q₂ * q₄) + n / (q₃ * q₄) + n / (q₄ * q₅)
        ≤ n / q₄ - 1 := row4raw
  have row4plus :
      n / (q₁ * q₄) + n / (q₂ * q₄) + n / (q₃ * q₄) + n / (q₄ * q₅) + 1
        ≤ n / q₄ := by
    omega

  have row5raw := overlap_row_le
    (qi := q₅) (r₁ := q₁) (r₂ := q₂) (r₃ := q₃) (r₄ := q₄) (n := n)
    hq₅ h5n h3 h12 h23 h34
  rw [Nat.mul_comm q₅ q₁, Nat.mul_comm q₅ q₂,
      Nat.mul_comm q₅ q₃, Nat.mul_comm q₅ q₄] at row5raw
  have row5 :
      n / (q₁ * q₅) + n / (q₂ * q₅) + n / (q₃ * q₅) + n / (q₄ * q₅)
        ≤ n / q₅ - 1 := row5raw
  have row5plus :
      n / (q₁ * q₅) + n / (q₂ * q₅) + n / (q₃ * q₅) + n / (q₄ * q₅) + 1
        ≤ n / q₅ := by
    omega

  unfold D M
  omega

end PC5488
