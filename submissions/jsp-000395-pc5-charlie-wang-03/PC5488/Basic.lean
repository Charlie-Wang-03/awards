import Mathlib

namespace PC5488

/-- Positive multiples of `q` up to `x`, encoded by their zero-based index `e = t - 1`. -/
def multiplesUpTo (q x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun e => q ∣ e + 1

/-- Support of the five-generator union, again encoded by `e = t - 1`. -/
def support5
    (q₁ q₂ q₃ q₄ q₅ x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun e =>
    q₁ ∣ e + 1 ∨ q₂ ∣ e + 1 ∨ q₃ ∣ e + 1 ∨ q₄ ∣ e + 1 ∨ q₅ ∣ e + 1

/-- Count positive integers up to `x` divisible by at least one of five generators. -/
def countMultiples5
    (q₁ q₂ q₃ q₄ q₅ x : ℕ) : ℕ :=
  (support5 q₁ q₂ q₃ q₄ q₅ x).card

@[simp]
theorem mem_multiplesUpTo {q x e : ℕ} :
    e ∈ multiplesUpTo q x ↔ e < x ∧ q ∣ e + 1 := by
  simp [multiplesUpTo]

@[simp]
theorem mem_support5 {q₁ q₂ q₃ q₄ q₅ x e : ℕ} :
    e ∈ support5 q₁ q₂ q₃ q₄ q₅ x ↔
      e < x ∧
        (q₁ ∣ e + 1 ∨ q₂ ∣ e + 1 ∨ q₃ ∣ e + 1 ∨ q₄ ∣ e + 1 ∨ q₅ ∣ e + 1) := by
  simp [support5]

/-- Mathlib's standard cardinality formula for positive multiples up to `x`. -/
theorem card_multiplesUpTo (q x : ℕ) :
    (multiplesUpTo q x).card = x / q := by
  simpa [multiplesUpTo] using (Nat.card_multiples x q)

/-- The counting function never exceeds the size of `{1, ..., x}`. -/
theorem countMultiples5_le
    (q₁ q₂ q₃ q₄ q₅ x : ℕ) :
    countMultiples5 q₁ q₂ q₃ q₄ q₅ x ≤ x := by
  unfold countMultiples5 support5
  calc
    ((Finset.range x).filter fun e =>
      q₁ ∣ e + 1 ∨ q₂ ∣ e + 1 ∨ q₃ ∣ e + 1 ∨ q₄ ∣ e + 1 ∨ q₅ ∣ e + 1).card
        ≤ (Finset.range x).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
    _ = x := Finset.card_range x

/-- Nested natural-number division is division by the product. -/
theorem nested_div (n a b : ℕ) :
    (n / a) / b = n / (a * b) := by
  simpa using (Nat.div_div_eq_div_mul n a b)

/-- Arithmetic core of the `q₁ = 2` density branch. -/
theorem half_plus_one_strict (n : ℕ) :
    n < 2 * (n / 2 + 1) := by
  omega

/-- If the first generator is `2`, any positive coprime second generator up to `n`
contributes one point outside the even multiples. -/
theorem half_plus_one_le_count_of_two
    {q₂ q₃ q₄ q₅ n : ℕ}
    (hq₂pos : 0 < q₂)
    (hq₂n : q₂ ≤ n)
    (hcop : Nat.Coprime 2 q₂) :
    n / 2 + 1 ≤ countMultiples5 2 q₂ q₃ q₄ q₅ n := by
  have hq₂one : 1 ≤ q₂ := by omega
  have hsum : q₂ - 1 + 1 = q₂ := Nat.sub_add_cancel hq₂one
  have hnot : q₂ - 1 ∉ multiplesUpTo 2 n := by
    intro hmem
    have hdvd' : 2 ∣ q₂ - 1 + 1 := (mem_multiplesUpTo.mp hmem).2
    have hdvd : 2 ∣ q₂ := by simpa [hsum] using hdvd'
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) hdvd
  have hextra : q₂ - 1 ∈ support5 2 q₂ q₃ q₄ q₅ n := by
    rw [mem_support5]
    constructor
    · omega
    · exact Or.inr (Or.inl (by simpa [hsum]))
  have hsub :
      insert (q₂ - 1) (multiplesUpTo 2 n) ⊆ support5 2 q₂ q₃ q₄ q₅ n := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hextra
    · rw [mem_support5]
      have hm := mem_multiplesUpTo.mp he
      exact ⟨hm.1, Or.inl hm.2⟩
  calc
    n / 2 + 1 = (insert (q₂ - 1) (multiplesUpTo 2 n)).card := by
      rw [Finset.card_insert_of_notMem hnot, card_multiplesUpTo]
    _ ≤ (support5 2 q₂ q₃ q₄ q₅ n).card := Finset.card_le_card hsub
    _ = countMultiples5 2 q₂ q₃ q₄ q₅ n := rfl

/-- Formal density conclusion for the `q₁ = 2` branch. -/
theorem count_gt_half_of_two
    {q₂ q₃ q₄ q₅ n : ℕ}
    (hq₂pos : 0 < q₂)
    (hq₂n : q₂ ≤ n)
    (hcop : Nat.Coprime 2 q₂) :
    n < 2 * countMultiples5 2 q₂ q₃ q₄ q₅ n := by
  have hle := half_plus_one_le_count_of_two
    (q₃ := q₃) (q₄ := q₄) (q₅ := q₅) hq₂pos hq₂n hcop
  have hstrict := half_plus_one_strict n
  omega

/-- The complete target inequality in the `q₁ = 2` branch. -/
theorem target_of_two
    {q₂ q₃ q₄ q₅ m n : ℕ}
    (hm : 0 < m)
    (hq₂pos : 0 < q₂)
    (hq₂n : q₂ ≤ n)
    (hcop : Nat.Coprime 2 q₂) :
    n * countMultiples5 2 q₂ q₃ q₄ q₅ m <
      2 * m * countMultiples5 2 q₂ q₃ q₄ q₅ n := by
  have hmcount := countMultiples5_le 2 q₂ q₃ q₄ q₅ m
  have hncount := count_gt_half_of_two
    (q₃ := q₃) (q₄ := q₄) (q₅ := q₅) hq₂pos hq₂n hcop
  calc
    n * countMultiples5 2 q₂ q₃ q₄ q₅ m ≤ n * m := Nat.mul_le_mul_left n hmcount
    _ < (2 * countMultiples5 2 q₂ q₃ q₄ q₅ n) * m :=
      Nat.mul_lt_mul_of_pos_right hncount hm
    _ = 2 * m * countMultiples5 2 q₂ q₃ q₄ q₅ n := by ac_rfl

/-- Four strictly increasing naturals starting at at least `3` dominate `3,4,5,6`. -/
theorem ordered_four_lower_bounds
    {r₁ r₂ r₃ r₄ : ℕ}
    (h3 : 3 ≤ r₁)
    (h12 : r₁ < r₂)
    (h23 : r₂ < r₃)
    (h34 : r₃ < r₄) :
    4 ≤ r₂ ∧ 5 ≤ r₃ ∧ 6 ≤ r₄ := by
  omega

/-- The reciprocal sum of four strictly increasing naturals starting at at least `3` is less than `1`. -/
theorem four_reciprocal_lt_one
    {r₁ r₂ r₃ r₄ : ℕ}
    (h3 : 3 ≤ r₁)
    (h12 : r₁ < r₂)
    (h23 : r₂ < r₃)
    (h34 : r₃ < r₄) :
    (1 / (r₁ : ℚ) + 1 / (r₂ : ℚ) + 1 / (r₃ : ℚ) + 1 / (r₄ : ℚ)) < 1 := by
  have hb := ordered_four_lower_bounds h3 h12 h23 h34
  rcases hb with ⟨h4, h5, h6⟩
  have h3q : (3 : ℚ) ≤ (r₁ : ℚ) := by exact_mod_cast h3
  have h4q : (4 : ℚ) ≤ (r₂ : ℚ) := by exact_mod_cast h4
  have h5q : (5 : ℚ) ≤ (r₃ : ℚ) := by exact_mod_cast h5
  have h6q : (6 : ℚ) ≤ (r₄ : ℚ) := by exact_mod_cast h6
  have hrec1 : (1 : ℚ) / (r₁ : ℚ) ≤ 1 / 3 := by
    exact one_div_le_one_div_of_le (by norm_num) h3q
  have hrec2 : (1 : ℚ) / (r₂ : ℚ) ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) h4q
  have hrec3 : (1 : ℚ) / (r₃ : ℚ) ≤ 1 / 5 := by
    exact one_div_le_one_div_of_le (by norm_num) h5q
  have hrec4 : (1 : ℚ) / (r₄ : ℚ) ≤ 1 / 6 := by
    exact one_div_le_one_div_of_le (by norm_num) h6q
  norm_num at hrec1 hrec2 hrec3 hrec4 ⊢
  linarith

end PC5488
