import JSP000404Research.CriticalPhaseInterval
import Mathlib.Tactic

/-!
# Refinement of critical transition obstructions

Let a critical transition gap [alpha, alpha+s] be split by an intermediate ray
at alpha+r, with 0<r<s.

The intermediate Boolean sign agrees with exactly one endpoint, so exactly one
of the two subgaps remains a sign-transition gap.

If the surviving transition subgap has normalized length at least one (as
forced by the global angle cap in the geometric application), then its
bad-phase interval contains the bad interval of the original gap.

* left transition:
    parent = [alpha+s-1, alpha+delta]
    child  = [alpha+r-1, alpha+delta]

* right transition:
    parent = [alpha+s-1, alpha+delta]
    child  = [alpha+s-1, alpha+r+delta].

Thus refining a transition gap monotonically enlarges its obstruction
interval.  Repeated refinement naturally yields nested fibres indexed by a
terminal adjacent transition gap.
-/

namespace JSP000404Research

/-- A Boolean between two opposite endpoint signs agrees with exactly one
endpoint. -/
theorem bool_between_opposite_agrees_exactly_one
    {a b c : Bool}
    (hac : a ≠ c) :
    (b = a ∧ b ≠ c) ∨ (b ≠ a ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- If the left subgap carries the transition, its bad interval contains the
parent bad interval. -/
theorem critical_bad_interval_contained_in_left_refinement
    {alpha r s delta x : ℝ}
    (hr0 : 0 ≤ r)
    (hrs : r ≤ s)
    (hx :
      criticalBadLeft alpha s ≤ x ∧
      x ≤ criticalBadRight alpha delta) :
    criticalBadLeft alpha r ≤ x ∧
      x ≤ criticalBadRight alpha delta := by
  constructor
  · unfold criticalBadLeft at *
    linarith
  · exact hx.2

/-- If the right subgap carries the transition, its bad interval contains the
parent bad interval.  The right subgap starts at alpha+r and has length s-r. -/
theorem critical_bad_interval_contained_in_right_refinement
    {alpha r s delta x : ℝ}
    (hr0 : 0 ≤ r)
    (hrs : r ≤ s)
    (hx :
      criticalBadLeft alpha s ≤ x ∧
      x ≤ criticalBadRight alpha delta) :
    criticalBadLeft (alpha + r) (s - r) ≤ x ∧
      x ≤ criticalBadRight (alpha + r) delta := by
  constructor
  · unfold criticalBadLeft at *
    ring_nf at *
    exact hx.1
  · unfold criticalBadRight at *
    linarith

/-- Interval-level containment for the left refinement. -/
theorem left_refinement_contains_parent
    {alpha r s delta : ℝ}
    (hr0 : 0 ≤ r)
    (hrs : r ≤ s) :
    criticalBadLeft alpha r ≤ criticalBadLeft alpha s ∧
      criticalBadRight alpha delta ≤
        criticalBadRight alpha delta := by
  constructor
  · unfold criticalBadLeft
    linarith
  · rfl

/-- Interval-level containment for the right refinement. -/
theorem right_refinement_contains_parent
    {alpha r s delta : ℝ}
    (hr0 : 0 ≤ r)
    (hrs : r ≤ s) :
    criticalBadLeft (alpha + r) (s - r) ≤
        criticalBadLeft alpha s ∧
      criticalBadRight alpha delta ≤
        criticalBadRight (alpha + r) delta := by
  constructor
  · unfold criticalBadLeft
    ring
  · unfold criticalBadRight
    linarith

/-- The surviving transition subgap is always the unique side on which the
intermediate sign differs from the preceding endpoint. -/
theorem exactly_one_transition_after_split
    (left mid right : Bool)
    (htransition : left ≠ right) :
    (left ≠ mid ∧ mid = right) ∨
      (left = mid ∧ mid ≠ right) := by
  rcases bool_between_opposite_agrees_exactly_one
      (a := left) (b := mid) (c := right) htransition with h | h
  · right
    exact ⟨h.1.symm, h.2⟩
  · left
    exact ⟨h.1, h.2⟩

#print axioms bool_between_opposite_agrees_exactly_one
#print axioms critical_bad_interval_contained_in_left_refinement
#print axioms critical_bad_interval_contained_in_right_refinement
#print axioms left_refinement_contains_parent
#print axioms right_refinement_contains_parent
#print axioms exactly_one_transition_after_split

end JSP000404Research
