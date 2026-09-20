import JSP000404Research.BoundaryDominance
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# One-long-spacing boundary certificates

Unwrap a rotating n-boundary partition at its unique long spacing.

A ray gap containing b phase boundaries is covered by b+1 consecutive pieces
of boundary cells.

* If it does not meet the long cell, its total normalized length is < b+1.
  Therefore floor(length) <= b.

* If it meets the unique long cell of length 1+delta, its total length is
  < b+1+delta.  Under delta<1 this is < b+2, so
  floor(length) <= b+1.

This file packages exactly that arithmetic.  The remaining circular geometry
only has to provide the cell-span inequalities; all quotient and local-palette
consequences then follow automatically through BoundaryDominance.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A nonnegative real below b+1 has natural floor at most b. -/
theorem natFloor_le_of_lt_nat_succ
    {x : ℝ} {b : ℕ}
    (hx0 : 0 ≤ x)
    (hx : x < (b : ℝ) + 1) :
    Nat.floor x ≤ b := by
  exact (Nat.floor_lt hx0).mp (by
    simpa [Nat.cast_add, Nat.cast_one] using hx)

/-- Exceptional form: x < b+1+delta and delta<1 imply floor x <= b+1. -/
theorem natFloor_le_add_one_of_lt_long_span
    {x delta : ℝ} {b : ℕ}
    (hx0 : 0 ≤ x)
    (hdelta : delta < 1)
    (hx : x < (b : ℝ) + 1 + delta) :
    Nat.floor x ≤ b + 1 := by
  apply natFloor_le_of_lt_nat_succ hx0
  push_cast
  linarith

/-- Abstract certificate supplied by the unwrapped phase geometry. -/
structure OneLongSpacingBoundaryCertificate
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (boundaryCount : I → ℕ)
    (exceptional : I) (delta : ℝ) : Prop where
  gap_nonneg : ∀ i, 0 ≤ gap i
  regular_span :
    ∀ i, i ≠ exceptional →
      gap i < (boundaryCount i : ℝ) + 1
  exceptional_span :
    gap exceptional <
      (boundaryCount exceptional : ℝ) + 1 + delta

namespace OneLongSpacingBoundaryCertificate

/-- Natural floor quotients satisfy exact one-exception domination. -/
theorem floor_domination
    {I : Type*} [Fintype I]
    {gap : I → ℝ} {boundaryCount : I → ℕ}
    {exceptional : I} {delta : ℝ}
    (C : OneLongSpacingBoundaryCertificate
      gap boundaryCount exceptional delta)
    (hdelta : delta < 1) :
    (∀ i, i ≠ exceptional →
      Nat.floor (gap i) ≤ boundaryCount i) ∧
    Nat.floor (gap exceptional) ≤
      boundaryCount exceptional + 1 := by
  constructor
  · intro i hi
    exact natFloor_le_of_lt_nat_succ
      (C.gap_nonneg i) (C.regular_span i hi)
  · exact natFloor_le_add_one_of_lt_long_span
      (C.gap_nonneg exceptional)
      hdelta C.exceptional_span

/-- Direct local palette bound after identifying the geometric quotient with
the floor of the normalized ray-gap length. -/
theorem support_le_deficit_add_one
    {I : Type*} [Fintype I]
    {gap : I → ℝ} {boundaryCount : I → ℕ}
    {exceptional : I} {delta : ℝ}
    (C : OneLongSpacingBoundaryCertificate
      gap boundaryCount exceptional delta)
    (n : ℕ)
    (hdelta : delta < 1)
    (hsum : (∑ i, boundaryCount i) = n) :
    positiveSupport boundaryCount ≤
      n - floorExcess (fun i => Nat.floor (gap i)) + 1 := by
  obtain ⟨hreg, hexc⟩ := C.floor_domination hdelta
  exact support_le_deficit_add_one_of_one_exception
    (fun i => Nat.floor (gap i))
    boundaryCount exceptional n hsum hreg hexc

/-- If the exceptional gap also obeys an ordinary-cell span bound, the exact
deficit palette budget follows. -/
theorem support_le_deficit_of_no_long_loss
    {I : Type*} [Fintype I]
    {gap : I → ℝ} {boundaryCount : I → ℕ}
    {exceptional : I} {delta : ℝ}
    (C : OneLongSpacingBoundaryCertificate
      gap boundaryCount exceptional delta)
    (n : ℕ)
    (hsum : (∑ i, boundaryCount i) = n)
    (hexact :
      gap exceptional <
        (boundaryCount exceptional : ℝ) + 1) :
    positiveSupport boundaryCount ≤
      n - floorExcess (fun i => Nat.floor (gap i)) := by
  apply support_le_deficit_of_full_domination
    (fun i => Nat.floor (gap i))
    boundaryCount n hsum
  intro i
  by_cases hi : i = exceptional
  · subst i
    exact natFloor_le_of_lt_nat_succ
      (C.gap_nonneg exceptional) hexact
  · exact natFloor_le_of_lt_nat_succ
      (C.gap_nonneg i) (C.regular_span i hi)

#print axioms natFloor_le_of_lt_nat_succ
#print axioms natFloor_le_add_one_of_lt_long_span
#print axioms OneLongSpacingBoundaryCertificate.floor_domination
#print axioms OneLongSpacingBoundaryCertificate.support_le_deficit_add_one
#print axioms OneLongSpacingBoundaryCertificate.support_le_deficit_of_no_long_loss

end OneLongSpacingBoundaryCertificate

end JSP000404Research
