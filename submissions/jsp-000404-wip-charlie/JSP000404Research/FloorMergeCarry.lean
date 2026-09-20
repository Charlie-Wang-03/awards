import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Exact carry in the floor of a merged gap

When one ray is deleted, two adjacent nonnegative projective gaps merge.
At fixed scale t, write

  qx = floor x,
  qy = floor y,

for the two scaled old gaps.  Then

  floor(x+y) = qx + qy + carry

with carry in {0,1}.

This file proves that carry statement directly from the defining floor
inequalities.  It removes the last arithmetic assumption from the geometric
gap-merge model: after geometry proves that the child gap is the sum of the
two parent gaps, the quotient update automatically has exactly the form used
by MergeGain and SupportTwoDeletion.
-/

namespace JSP000404Research

/-- The floor of a sum of two nonnegative reals differs from the sum of the
floors by at most one. -/
theorem natFloor_add_eq_add_add_carry
    {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      Nat.floor (x + y) =
        Nat.floor x + Nat.floor y + carry := by
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hxlo : ((Nat.floor x : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx
  have hylo : ((Nat.floor y : ℕ) : ℝ) ≤ y :=
    Nat.floor_le hy
  have hxhi : x < ((Nat.floor x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hyhi : y < ((Nat.floor y : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one y
  have hlowerR :
      (((Nat.floor x + Nat.floor y : ℕ) : ℕ) : ℝ) ≤ x + y := by
    push_cast
    linarith
  have hlower :
      Nat.floor x + Nat.floor y ≤ Nat.floor (x + y) := by
    exact Nat.le_floor hlowerR
  have hupperR :
      x + y <
        (((Nat.floor x + Nat.floor y + 2 : ℕ) : ℕ) : ℝ) := by
    push_cast
    linarith
  have hupper :
      Nat.floor (x + y) <
        Nat.floor x + Nat.floor y + 2 := by
    exact (Nat.floor_lt hxy).2 (by simpa using hupperR)
  let carry :=
    Nat.floor (x + y) -
      (Nat.floor x + Nat.floor y)
  have hcarry : carry ≤ 1 := by
    dsimp [carry]
    omega
  have heq :
      Nat.floor (x + y) =
        Nat.floor x + Nat.floor y + carry := by
    dsimp [carry]
    omega
  exact ⟨carry, hcarry, heq⟩

/-- Fixed-scale gap form. -/
theorem natFloor_scaled_gap_merge
    {t g₁ g₂ : ℝ}
    (ht : 0 ≤ t)
    (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      Nat.floor (t * (g₁ + g₂)) =
        Nat.floor (t * g₁) +
          Nat.floor (t * g₂) + carry := by
  have hx : 0 ≤ t * g₁ := mul_nonneg ht hg₁
  have hy : 0 ≤ t * g₂ := mul_nonneg ht hg₂
  obtain ⟨carry, hc, heq⟩ :=
    natFloor_add_eq_add_add_carry hx hy
  refine ⟨carry, hc, ?_⟩
  have hdist :
      t * (g₁ + g₂) = t * g₁ + t * g₂ := by ring
  rw [hdist]
  exact heq

/-- Quotient-name form convenient for merge certificates. -/
theorem exists_binary_carry_for_gap_merge
    {t g₁ g₂ : ℝ} {q₁ q₂ qnew : ℕ}
    (ht : 0 ≤ t)
    (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂)
    (hq₁ : q₁ = Nat.floor (t * g₁))
    (hq₂ : q₂ = Nat.floor (t * g₂))
    (hqnew : qnew = Nat.floor (t * (g₁ + g₂))) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      qnew = q₁ + q₂ + carry := by
  subst q₁
  subst q₂
  subst qnew
  exact natFloor_scaled_gap_merge ht hg₁ hg₂

#print axioms natFloor_add_eq_add_add_carry
#print axioms natFloor_scaled_gap_merge
#print axioms exists_binary_carry_for_gap_merge

end JSP000404Research
