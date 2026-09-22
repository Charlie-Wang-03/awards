import JSP000404Research.CriticalMinimalCover
import Mathlib.Tactic

/-!
# Order preservation inside an irredundant critical cover

A critical interval attached to a terminal transition (alpha,s) is

  [alpha+s-1, alpha+delta].

Thus its right endpoint remembers the transition anchor alpha, while its left
endpoint remembers the terminal endpoint beta=alpha+s.

MinimalPhaseCover proves that an irredundant interval family has no nesting:
strict order of one endpoint forces strict order of the other endpoint.

For critical intervals this gives a stronger geometric statement than merely
"distinct anchors":

  alpha_i < alpha_j  ->  alpha_i+s_i < alpha_j+s_j.

So the selected terminal turns are order-preserving on the unwrapped
projective direction line.  In particular, two selected turns cannot reverse
their endpoint order.

This is the correct combinatorial input for any later attempt to concatenate
minimum-cover turns into global turning chains.
-/

namespace JSP000404Research

/-- In an irredundant critical cover, strict anchor order forces strict order
of the terminal transition endpoints. -/
theorem critical_terminal_endpoint_strict_of_anchor_strict
    {I : Type*} [DecidableEq I]
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCover (CriticalBadAt alpha s delta) S)
    {i j : I}
    (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j)
    (halpha : alpha i < alpha j) :
    alpha i + s i < alpha j + s j := by
  let L : I → ℝ :=
    fun q => criticalBadLeft (alpha q) (s q)
  let R : I → ℝ :=
    fun q => criticalBadRight (alpha q) delta
  have hmin' :
      IrredundantCover (InClosedInterval L R) S := by
    simpa [CriticalBadAt, InClosedInterval, L, R] using hmin
  have hRij : R i < R j := by
    dsimp [R, criticalBadRight]
    linarith
  have hLij : L i < L j := by
    by_contra hnot
    have hLji : L j ≤ L i := le_of_not_gt hnot
    have hRji :=
      irredundant_interval_right_strict
        L R S hmin' hj hi hij.symm hLji
    linarith
  dsimp [L, criticalBadLeft] at hLij
  linarith

/-- Conversely, terminal-endpoint order forces the same anchor order. -/
theorem critical_anchor_strict_of_terminal_endpoint_strict
    {I : Type*} [DecidableEq I]
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCover (CriticalBadAt alpha s delta) S)
    {i j : I}
    (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j)
    (hend : alpha i + s i < alpha j + s j) :
    alpha i < alpha j := by
  by_contra hnot
  have haji : alpha j ≤ alpha i := le_of_not_gt hnot
  rcases lt_or_eq_of_le haji with hstrict | heq
  · have hrev :=
      critical_terminal_endpoint_strict_of_anchor_strict
        alpha s delta S hmin hj hi hij.symm hstrict
    linarith
  · have hanchorEq : alpha i = alpha j := heq.symm
    exact (critical_anchor_ne_of_irredundant
      alpha s delta S hmin hi hj hij) hanchorEq

/-- Exact order equivalence between anchors and terminal endpoints. -/
theorem critical_anchor_lt_iff_terminal_endpoint_lt
    {I : Type*} [DecidableEq I]
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCover (CriticalBadAt alpha s delta) S)
    {i j : I}
    (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    alpha i < alpha j ↔
      alpha i + s i < alpha j + s j := by
  constructor
  · exact critical_terminal_endpoint_strict_of_anchor_strict
      alpha s delta S hmin hi hj hij
  · exact critical_anchor_strict_of_terminal_endpoint_strict
      alpha s delta S hmin hi hj hij

/-- Widths of selected terminal turns cannot drop faster than their anchors
advance.  This is a useful quantitative corollary of order preservation. -/
theorem critical_width_drop_lt_anchor_advance
    {I : Type*} [DecidableEq I]
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCover (CriticalBadAt alpha s delta) S)
    {i j : I}
    (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j)
    (halpha : alpha i < alpha j) :
    s i - s j < alpha j - alpha i := by
  have hend :=
    critical_terminal_endpoint_strict_of_anchor_strict
      alpha s delta S hmin hi hj hij halpha
  linarith

#print axioms critical_terminal_endpoint_strict_of_anchor_strict
#print axioms critical_anchor_strict_of_terminal_endpoint_strict
#print axioms critical_anchor_lt_iff_terminal_endpoint_lt
#print axioms critical_width_drop_lt_anchor_advance

end JSP000404Research
