import JSP000404Research.SixPointNFourDirectNoCover
import Mathlib.Tactic

/-!
# No full transition-only unit-slot phase cover in the n=4 six-point terminal

The ten-slot equality terminal has one top centre and five minima.

Assume a full phase cover by critical unit-gap obstructions, with the natural
geometric condition that a same-sign unit gap cannot generate such a
transition obstruction.

The certified unconditional same-sign-slot theorem finds a genuine indexed
unusable unit-gap at a strictly exposed non-top centre, without an exact-angle
witness or all-five-minima three-transition classification.

The existing conditional phase-cover bound then rules out a full cover.
Neither the phase-cover lower-bound premise nor same-sign unavailability is
claimed to follow from AngleCap alone.
-/

namespace JSP000404Research

theorem no_six_point_n_four_transition_only_unit_slot_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hSameUnusable :
      ∀ u : GlobalUnitGapSlot C t,
        GlobalUnitGapSameSign C t u →
        ∀ x : ℝ, ¬ A u x)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  exact
    six_point_n_four_equality_no_transition_only_phase_cover_direct
      hp hcap hdelta0 hdeltaHalf ht hlam
      C hcard top hTop hMin hunitTotal
      A S hSameUnusable hcoverLower

#print axioms no_six_point_n_four_transition_only_unit_slot_cover

end JSP000404Research
