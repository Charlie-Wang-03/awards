import JSP000404Research.CriticalPhaseInterval
import Mathlib.Tactic

/-!
# A critical subgap dominates the parent triangle obstruction

Let a wrap triangle have a complementary projective arc

  [L, L+S].

Its bad-phase interval is

  [L+S-1, L+delta].

Suppose a critical adjacent sign-transition gap

  [alpha, alpha+s]

lies inside that complementary arc.  Then its own bad-phase interval

  [alpha+s-1, alpha+delta]

contains the triangle bad interval.

This is the key one-dimensional domination needed after the short-arc
unique-transition reduction: arbitrary wrap-triangle obstructions can be
replaced by adjacent critical-transition obstructions.
-/

namespace JSP000404Research

/-- Generic bad-left endpoint attached to an arc [L,L+S]. -/
def arcBadLeft (L S : ℝ) : ℝ :=
  L + S - 1

/-- Generic bad-right endpoint attached to an arc starting at L. -/
def arcBadRight (L delta : ℝ) : ℝ :=
  L + delta

/-- A subgap nested in a parent arc has a no-later bad left endpoint and a
no-earlier bad right endpoint. -/
theorem nested_gap_bad_endpoint_order
    {L S alpha s delta : ℝ}
    (hleft : L ≤ alpha)
    (hright : alpha + s ≤ L + S) :
    criticalBadLeft alpha s ≤ arcBadLeft L S ∧
      arcBadRight L delta ≤ criticalBadRight alpha delta := by
  simp [criticalBadLeft, criticalBadRight, arcBadLeft, arcBadRight]
  constructor <;> linarith

/-- Hence every bad phase for the parent triangle arc is bad for the nested
critical transition gap. -/
theorem parent_bad_interval_subset_critical
    {L S alpha s delta x : ℝ}
    (hleft : L ≤ alpha)
    (hright : alpha + s ≤ L + S)
    (hx :
      arcBadLeft L S ≤ x ∧
      x ≤ arcBadRight L delta) :
    criticalBadLeft alpha s ≤ x ∧
      x ≤ criticalBadRight alpha delta := by
  have horder :=
    nested_gap_bad_endpoint_order
      (L := L) (S := S) (alpha := alpha) (s := s) (delta := delta)
      hleft hright
  exact ⟨horder.1.trans hx.1, hx.2.trans horder.2⟩

/-- If the parent complement itself is critical-sized, every phase obstruction
of the wrap triangle is therefore covered by the unique adjacent critical
transition obstruction inside it. -/
theorem wrap_obstruction_dominated_by_nested_critical
    {L S alpha s delta x : ℝ}
    (hparent : 1 ≤ S ∧ S ≤ 1 + delta)
    (hcritical : 1 ≤ s)
    (hnested : L ≤ alpha ∧ alpha + s ≤ L + S)
    (hx :
      L + S - 1 ≤ x ∧
      x ≤ L + delta) :
    criticalBadLeft alpha s ≤ x ∧
      x ≤ criticalBadRight alpha delta := by
  exact parent_bad_interval_subset_critical
    hnested.1 hnested.2
    (by simpa [arcBadLeft, arcBadRight] using hx)

#print axioms nested_gap_bad_endpoint_order
#print axioms parent_bad_interval_subset_critical
#print axioms wrap_obstruction_dominated_by_nested_critical

end JSP000404Research
