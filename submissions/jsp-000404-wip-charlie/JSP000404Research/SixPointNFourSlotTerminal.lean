import JSP000404Research.SixPointNFourSameSignUnit
import JSP000404Research.SameSignUnitGapSlot
import JSP000404Research.SixPointNFourPhaseCover
import Mathlib.Tactic

/-!
# n=4 phase cover forces the three-transition exact-witness branch

The n=4 equality terminal has ten unit-gap slots.  In the one-transition
exact-witness branch, duplicate unit quotients produce a concrete same-sign
unit-gap slot.  A genuine critical transition obstruction cannot be assigned
to such a slot.

Therefore, for any obstruction family whose same-sign unit slots are unusable,
a full phase cover rules out the one-transition branch.  The exact-witness
centre must have exactly three sign transitions.

This isolates the final n=4 geometric terminal to one sharply specified local
configuration.
-/

namespace JSP000404Research

theorem six_point_n_four_exactWitness_sameSign_slot_or_three_transitions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10) :
    (
      StrictlyExposedAt p W.b ∧
      ∃ u : GlobalUnitGapSlot C t,
        u.1 = W.b ∧
        GlobalUnitGapSameSign C t u
    )
    ∨
    (
      ∃ first : OtherVertex W.b,
        ∃ rest : List (OtherVertex W.b),
          (C W.b).rays = first :: rest ∧
          TransitionQuotientOccurs 1
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest)
            (quotientList t (C W.b).gaps) ∧
          boolTransitionCountFrom
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest) = 3
    ) := by
  rcases
    six_point_n_four_exactWitness_sameSign_unit_or_three_transitions
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
    with hOne | hThree
  · left
    rcases hOne with
      ⟨hexposed, first, rest, pre, post,
        hrays, hq, hsigns, hsame⟩
    obtain ⟨u, hui, husame⟩ :=
      exists_globalUnitGap_sameSign_of_occurs
        C t W.b first rest hrays hsame
    exact ⟨hexposed, u, hui, husame⟩
  · exact Or.inr hThree

/-- Any full obstruction cover whose critical obstructions are transition-only
forces the exact-witness centre into the three-transition branch. -/
theorem six_point_n_four_cover_forces_exactWitness_three_transitions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
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
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta)
    (hcover : PredicateCovers A S) :
    ∃ first : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
        (C W.b).rays = first :: rest ∧
        TransitionQuotientOccurs 1
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
          (quotientList t (C W.b).gaps) ∧
        boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) = 3 := by
  rcases
    six_point_n_four_exactWitness_sameSign_slot_or_three_transitions
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
    with hOne | hThree
  · rcases hOne with ⟨_hexposed, u, _hui, husame⟩
    have hno :=
      no_six_point_n_four_globalUnitGapSlot_cover_of_unusable
        C hdelta0 hdeltaHalf ht hcard
        top hTop hMin A S u
        (hSameUnusable u husame)
        hcoverLower
    exact False.elim (hno hcover)
  · exact hThree

#print axioms six_point_n_four_exactWitness_sameSign_slot_or_three_transitions
#print axioms six_point_n_four_cover_forces_exactWitness_three_transitions

end JSP000404Research
