import Mathlib.Tactic

/-!
# Binary fractional carry for merged gaps

Write two normalized gap lengths as

  x = a + r,   y = b + s,

where a,b are natural quotients and 0 <= r,s < 1.  Their sum has quotient
a+b+c with a binary carry c in {0,1}.  These lemmas isolate that elementary
floor arithmetic without committing to a particular floor API.
-/

namespace JSP000404Research

/-- Carry created by adding two fractional remainders. -/
noncomputable def binaryCarry (r s : ℝ) : ℕ :=
  if 1 ≤ r + s then 1 else 0

theorem binaryCarry_le_one (r s : ℝ) :
    binaryCarry r s ≤ 1 := by
  unfold binaryCarry
  split <;> omega

theorem binaryCarry_eq_zero_of_lt
    {r s : ℝ} (h : r + s < 1) :
    binaryCarry r s = 0 := by
  unfold binaryCarry
  simp [not_le.mpr h]

theorem binaryCarry_eq_one_of_ge
    {r s : ℝ} (h : 1 ≤ r + s) :
    binaryCarry r s = 1 := by
  unfold binaryCarry
  simp [h]

/-- After subtracting the binary carry, the merged fractional remainder again
lies in the half-open unit interval. -/
theorem merged_remainder_bounds
    {r s : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ r + s - binaryCarry r s ∧
      r + s - binaryCarry r s < 1 := by
  by_cases hcarry : 1 ≤ r + s
  · rw [binaryCarry_eq_one_of_ge hcarry]
    constructor <;> norm_num <;> linarith
  · have hlt : r + s < 1 := lt_of_not_ge hcarry
    rw [binaryCarry_eq_zero_of_lt hlt]
    constructor <;> norm_num <;> linarith

/-- The integer part `a+b+carry` brackets the merged normalized gap. -/
theorem merged_quotient_window
    {a b : ℕ} {r s x y : ℝ}
    (hx : x = (a : ℝ) + r)
    (hy : y = (b : ℝ) + s)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ((a + b + binaryCarry r s : ℕ) : ℝ) ≤ x + y ∧
      x + y < ((a + b + binaryCarry r s : ℕ) : ℝ) + 1 := by
  have hrem := merged_remainder_bounds hr0 hr1 hs0 hs1
  have heq :
      x + y =
        ((a + b + binaryCarry r s : ℕ) : ℝ) +
          (r + s - binaryCarry r s) := by
    rw [hx, hy]
    push_cast
    ring
  rw [heq]
  constructor <;> linarith

/-- Uniqueness of the natural quotient in a half-open unit interval. -/
theorem nat_quotient_unique
    {q m : ℕ} {x : ℝ}
    (hqlo : (q : ℝ) ≤ x)
    (hqhi : x < (q : ℝ) + 1)
    (hmlo : (m : ℝ) ≤ x)
    (hmhi : x < (m : ℝ) + 1) :
    q = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hqm | hmq
  · have hcast : (q : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast hqm
    linarith
  · have hcast : (m : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast hmq
    linarith

/-- Hence any natural quotient assigned to the merged gap by the usual
half-open unit-window rule is exactly a+b+carry. -/
theorem merged_quotient_eq
    {a b q : ℕ} {r s x y : ℝ}
    (hx : x = (a : ℝ) + r)
    (hy : y = (b : ℝ) + s)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hqlo : (q : ℝ) ≤ x + y)
    (hqhi : x + y < (q : ℝ) + 1) :
    q = a + b + binaryCarry r s := by
  obtain ⟨hmlo, hmhi⟩ :=
    merged_quotient_window hx hy hr0 hr1 hs0 hs1
  exact nat_quotient_unique hqlo hqhi hmlo hmhi

#print axioms binaryCarry_le_one
#print axioms merged_remainder_bounds
#print axioms merged_quotient_window
#print axioms nat_quotient_unique
#print axioms merged_quotient_eq

end JSP000404Research
