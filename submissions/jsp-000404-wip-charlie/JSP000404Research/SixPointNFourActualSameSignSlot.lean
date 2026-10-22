import JSP000404Research.SixPointNFourSameSignUnit
import JSP000404Research.SameSignUnitGapSlot
import Mathlib.Tactic

/-!
# The real, indexed same-sign unit slot at an n=4 equality witness

The n=4 six-point ten-slot equality terminal has two unit quotients
at every minimum. At an exact angle witness with one sign transition,
the existing equality-terminal theorem gives an additional unit on
a constant-sign step.

This theorem lifts that same-sign occurrence to a GENUINE dependent
original-centre unit slot (centre ID plus real gap index). It does not
identify the indexed unit slot with a Boolean true hole and does not
charge any hard source to that slot.
-/

namespace JSP000404Research

theorem six_point_n_four_exactWitness_one_transition_actual_sameSign_unit_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10)
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (pre post : List ℕ)
    (hrays : (C W.b).rays = first :: rest)
    (hq : quotientList t (C W.b).gaps = pre ++ 1 :: post)
    (hsigns :
      liftedCentreSignPath hp W.b first rest =
        List.replicate pre.length (raySignAt hp W.b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp W.b first)) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = W.b ∧ GlobalUnitGapSameSign C t u := by
  have hocc :=
    six_point_n_four_exactWitness_one_transition_has_sameSign_unit
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
      first rest pre post hrays hq hsigns
  exact exists_globalUnitGap_sameSign_of_occurs
    C t W.b first rest hrays hocc

/-- Under equality of the ten real unit-gap slots, the exact-witness
centre either exposes a genuine indexed same-sign unit slot in the strictly
exposed one-transition branch, or has three sign transitions.

This is a local geometric disjunction. It does not turn a unit-gap slot into a
Boolean true hole and does not prove any global non-reusing payment. -/
theorem six_point_n_four_exactWitness_actual_sameSign_slot_or_three_transitions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10) :
    (StrictlyExposedAt p W.b ∧
      ∃ u : GlobalUnitGapSlot C t,
        u.1 = W.b ∧ GlobalUnitGapSameSign C t u)
    ∨
    (∃ first : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
        (C W.b).rays = first :: rest ∧
        TransitionQuotientOccurs 1
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
          (quotientList t (C W.b).gaps) ∧
        boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) = 3) := by
  rcases
    six_point_n_four_exactWitness_terminal_dichotomy
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
    with hOne | hThree
  · obtain ⟨hexposed, first, rest, pre, post,
        hrays, hq, hsigns⟩ := hOne
    left
    refine ⟨hexposed, ?_⟩
    exact
      six_point_n_four_exactWitness_one_transition_actual_sameSign_unit_slot
        hp hcap hdelta0 hdeltaHalf ht hlam
        W C hcard top hTop hMin hunitTotal
        first rest pre post hrays hq hsigns
  · exact Or.inr hThree

#print axioms six_point_n_four_exactWitness_one_transition_actual_sameSign_unit_slot
#print axioms six_point_n_four_exactWitness_actual_sameSign_slot_or_three_transitions

end JSP000404Research
