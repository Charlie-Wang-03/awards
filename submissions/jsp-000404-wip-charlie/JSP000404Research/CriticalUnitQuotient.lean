
import JSP000404Research.CriticalPhaseInterval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Terminal critical transitions have unit quotient

In the lower Sendov branch delta < 1/2, every terminal critical transition
gap has normalized width

  1 <= s <= 1+delta < 3/2 < 2.

Therefore its natural floor quotient is exactly one.

This is the discrete form needed for any final slot assignment: terminal
phase obstructions are not arbitrary positive quotient gaps; they are actual
adjacent sign transitions carried by quotient 1.
-/

namespace JSP000404Research

theorem critical_gap_floor_eq_one
    {s delta : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (hs1 : 1 ≤ s)
    (hsTop : s ≤ 1 + delta) :
    Nat.floor s = 1 := by
  have hs0 : 0 ≤ s := by linarith
  apply (Nat.floor_eq_iff hs0).2
  constructor
  · norm_num
    exact hs1
  · norm_num
    linarith

theorem critical_gap_quotient_eq_one
    {s delta : ℝ} {q : ℕ}
    (hdelta : delta < (1 : ℝ) / 2)
    (hs1 : 1 ≤ s)
    (hsTop : s ≤ 1 + delta)
    (hq : q = Nat.floor s) :
    q = 1 := by
  rw [hq]
  exact critical_gap_floor_eq_one hdelta hs1 hsTop

/-- The terminal gap has one whole normalized unit plus a remainder in
[0,delta]. -/
theorem critical_gap_eq_one_add_remainder
    {s delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hs1 : 1 ≤ s)
    (hsTop : s ≤ 1 + delta) :
    ∃ r : ℝ,
      0 ≤ r ∧ r ≤ delta ∧ s = 1 + r := by
  refine ⟨s - 1, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · ring

/-- Its bad-phase width is exactly the complementary part of the same delta
remainder budget. -/
theorem critical_gap_remainder_add_badWidth
    {s delta : ℝ} :
    (s - 1) + criticalBadWidth delta s = delta := by
  unfold criticalBadWidth
  ring

#print axioms critical_gap_floor_eq_one
#print axioms critical_gap_quotient_eq_one
#print axioms critical_gap_eq_one_add_remainder
#print axioms critical_gap_remainder_add_badWidth

end JSP000404Research
