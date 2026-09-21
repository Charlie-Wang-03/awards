import JSP000404Research.CriticalPhaseDomination
import JSP000404Research.ShortArcTransition
import Mathlib.Tactic

/-!
# Terminal adjacent transition dominators

A wrap-triangle obstruction is naturally attached to a lifted finite ray arc,
not necessarily to one adjacent ray gap. The endpoint signs of the relevant
short arc are opposite. Every genuine sign change costs at least one
normalized unit by the global angle cap.

This file closes the finite-refinement part of the phase route.

We record explicitly when a pair (alpha,s) occurs as an actual adjacent
sign-changing gap in the lifted sign/gap path. If the two endpoint signs of
the whole path are opposite, some adjacent transition occurs. Its gap is
nested inside the parent arc and has length at least one, so its critical
bad-phase interval contains the full parent bad-phase interval.

If the parent arc has length at most 1+delta, the terminal adjacent gap is
itself critical-sized:

  1 <= s <= 1+delta.

Thus every finite short-arc obstruction has an actual adjacent critical
transition as a common dominator. No convex-hull or global turn argument is
used here; that remains the separate final geometric obligation.
-/

namespace JSP000404Research

/-- (alpha,s) is one of the actual adjacent sign-changing gaps in a lifted
sign/gap path starting at parameter L with initial sign a. -/
def OccursAdjacentTransitionGap
    (L : ℝ) (a : Bool) :
    List Bool → List ℝ → ℝ → ℝ → Prop
  | b :: bs, g :: gs, alpha, s =>
      (alpha = L ∧ s = g ∧ a ≠ b) ∨
        OccursAdjacentTransitionGap (L + g) b bs gs alpha s
  | _, _, _, _ => False

/-- All gap lengths in a TransitionGapLowerBound path sum to a nonnegative
number. -/
theorem transitionGapLowerBound_sum_nonneg
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (h : TransitionGapLowerBound a signs gaps) :
    0 ≤ gaps.sum := by
  induction signs generalizing a gaps with
  | nil =>
      cases gaps with
      | nil => simp
      | cons g gs =>
          simp [TransitionGapLowerBound] at h
  | cons b bs ih =>
      cases gaps with
      | nil =>
          simp [TransitionGapLowerBound] at h
      | cons g gs =>
          rcases h with ⟨hg0, _hchange, hrest⟩
          have htail := ih b gs hrest
          simp only [List.sum_cons]
          linarith

/-- Any actual adjacent transition extracted from a short opposite-sign arc
dominates the parent phase obstruction. -/
theorem exists_adjacent_transition_dominator
    (L delta : ℝ)
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (hgap : TransitionGapLowerBound a signs gaps)
    (hlast : boolLastFrom a signs = !a)
    (hparentTop : gaps.sum ≤ 1 + delta) :
    ∃ alpha s : ℝ,
      OccursAdjacentTransitionGap L a signs gaps alpha s ∧
      1 ≤ s ∧
      s ≤ 1 + delta ∧
      L ≤ alpha ∧
      alpha + s ≤ L + gaps.sum ∧
      ∀ x,
        arcBadLeft L gaps.sum ≤ x ∧
          x ≤ arcBadRight L delta →
        criticalBadLeft alpha s ≤ x ∧
          x ≤ criticalBadRight alpha delta := by
  induction signs generalizing L a gaps with
  | nil =>
      cases gaps with
      | nil =>
          cases a <;> simp [boolLastFrom] at hlast
      | cons g gs =>
          simp [TransitionGapLowerBound] at hgap
  | cons b bs ih =>
      cases gaps with
      | nil =>
          simp [TransitionGapLowerBound] at hgap
      | cons g gs =>
          rcases hgap with ⟨hg0, hchange, hrest⟩
          have hgs0 :
              0 ≤ gs.sum :=
            transitionGapLowerBound_sum_nonneg b bs gs hrest
          by_cases hab : a = b
          · subst b
            have hlastTail :
                boolLastFrom a bs = !a := by
              simpa [boolLastFrom] using hlast
            have htailTop :
                gs.sum ≤ 1 + delta := by
              simp only [List.sum_cons] at hparentTop
              linarith
            obtain ⟨alpha, s, hocc, hs1, hsTop,
                hLtail, hRtail, _hdomTail⟩ :=
              ih (L + g) a gs hrest hlastTail htailTop
            have hL : L ≤ alpha := by
              linarith
            have hR :
                alpha + s ≤ L + (g :: gs).sum := by
              simp only [List.sum_cons]
              linarith
            refine ⟨alpha, s, ?_, hs1, hsTop, hL, hR, ?_⟩
            · exact Or.inr hocc
            · intro x hx
              exact parent_bad_interval_subset_critical
                hL hR (by
                  simpa [List.sum_cons] using hx)
          · have hg1 : 1 ≤ g := hchange hab
            have hgTop : g ≤ 1 + delta := by
              simp only [List.sum_cons] at hparentTop
              linarith
            have hR :
                L + g ≤ L + (g :: gs).sum := by
              simp only [List.sum_cons]
              linarith
            refine ⟨L, g, ?_, hg1, hgTop, le_rfl, hR, ?_⟩
            · exact Or.inl ⟨rfl, rfl, hab⟩
            · intro x hx
              exact parent_bad_interval_subset_critical
                (L := L) (S := (g :: gs).sum)
                (alpha := L) (s := g) le_rfl hR hx

/-- Lower-branch specialization: every opposite-sign parent arc of length at
most 1+delta has an actual adjacent critical transition whose obstruction
contains the parent obstruction. -/
theorem lower_branch_parent_has_terminal_critical_dominator
    (L delta : ℝ)
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (hgap : TransitionGapLowerBound a signs gaps)
    (hlast : boolLastFrom a signs = !a)
    (hlen : gaps.sum ≤ 1 + delta) :
    ∃ alpha s : ℝ,
      OccursAdjacentTransitionGap L a signs gaps alpha s ∧
      1 ≤ s ∧ s ≤ 1 + delta ∧
      ∀ x,
        arcBadLeft L gaps.sum ≤ x ∧
          x ≤ arcBadRight L delta →
        criticalBadLeft alpha s ≤ x ∧
          x ≤ criticalBadRight alpha delta := by
  obtain ⟨alpha, s, hocc, hs1, hsTop,
      _hleft, _hright, hdom⟩ :=
    exists_adjacent_transition_dominator
      L delta a signs gaps hgap hlast hlen
  exact ⟨alpha, s, hocc, hs1, hsTop, hdom⟩

#print axioms OccursAdjacentTransitionGap
#print axioms transitionGapLowerBound_sum_nonneg
#print axioms exists_adjacent_transition_dominator
#print axioms lower_branch_parent_has_terminal_critical_dominator

end JSP000404Research
