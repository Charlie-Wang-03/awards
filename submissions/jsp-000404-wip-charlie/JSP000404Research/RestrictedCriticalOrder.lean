import JSP000404Research.RestrictedIntervalMultiplicity
import Mathlib.Tactic

/-!
# Critical transition order on a real, restricted phase-domain

Unlike CriticalIrredundantOrder, this result does NOT require
finitely many bounded intervals to cover the entire real line.
Domain can be a bounded interval or the actual fundamental phase window.

Selected irredundant critical intervals preserve the strict order of
their start (alpha) and end (alpha+s) anchors, and hence constrain
the rate at which the terminal gap length may decrease.

The AngleCap realization of the phase-domain coverage and
non-reused global debt payment are still genuine gaps.
-/

namespace JSP000404Research

theorem restricted_critical_terminal_strict_of_anchor_strict
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCoverOn Domain
      (fun i x => criticalBadLeft (alpha i) (s i) ≤ x ∧
        x ≤ criticalBadRight (alpha i) delta) S)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j)
    (halpha : alpha i < alpha j) :
    alpha i + s i < alpha j + s j := by
  let L : I → ℝ := fun q => criticalBadLeft (alpha q) (s q)
  let R : I → ℝ := fun q => criticalBadRight (alpha q) delta
  have hmin' : IrredundantCoverOn Domain (InClosedInterval L R) S := by
    change IrredundantCoverOn Domain (InClosedInterval L R) S at hmin
    exact hmin
  have hRij : R i < R j := by
    dsimp [R, criticalBadRight]
    linarith
  have hLij : L i < L j := by
    by_contra hnot
    have hLji : L j ≤ L i := le_of_not_gt hnot
    have hRji :=
      irredundant_on_right_strict
        Domain L R S hmin' hj hi hij.symm hLji
    linarith
  dsimp [L, criticalBadLeft] at hLij
  linarith

theorem restricted_critical_anchor_strict_of_terminal_strict
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCoverOn Domain
      (fun i x => criticalBadLeft (alpha i) (s i) ≤ x ∧
        x ≤ criticalBadRight (alpha i) delta) S)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j)
    (hend : alpha i + s i < alpha j + s j) :
    alpha i < alpha j := by
  by_contra hnot
  have haji : alpha j ≤ alpha i := le_of_not_gt hnot
  rcases lt_or_eq_of_le haji with hstrict | heq
  · have hrev :=
      restricted_critical_terminal_strict_of_anchor_strict
        Domain alpha s delta S hmin hj hi hij.symm hstrict
    linarith
  · have hanchorEq : alpha i = alpha j := heq.symm
    exact hij (critical_anchor_injective_of_irredundant_on
      Domain alpha s delta S hmin hi hj hanchorEq)

theorem restricted_critical_anchor_lt_iff_terminal_lt
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCoverOn Domain
      (fun i x => criticalBadLeft (alpha i) (s i) ≤ x ∧
        x ≤ criticalBadRight (alpha i) delta) S)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    alpha i < alpha j ↔
      alpha i + s i < alpha j + s j := by
  constructor
  · exact restricted_critical_terminal_strict_of_anchor_strict
      Domain alpha s delta S hmin hi hj hij
  · exact restricted_critical_anchor_strict_of_terminal_strict
      Domain alpha s delta S hmin hi hj hij

theorem restricted_critical_width_drop_lt_anchor_advance
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCoverOn Domain
      (fun i x => criticalBadLeft (alpha i) (s i) ≤ x ∧
        x ≤ criticalBadRight (alpha i) delta) S)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j)
    (halpha : alpha i < alpha j) :
    s i - s j < alpha j - alpha i := by
  have hend := restricted_critical_terminal_strict_of_anchor_strict
    Domain alpha s delta S hmin hi hj hij halpha
  linarith

#print axioms restricted_critical_terminal_strict_of_anchor_strict
#print axioms restricted_critical_anchor_strict_of_terminal_strict
#print axioms restricted_critical_anchor_lt_iff_terminal_lt
#print axioms restricted_critical_width_drop_lt_anchor_advance

end JSP000404Research
