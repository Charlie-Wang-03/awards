import JSP000404Research.SixPointNFourExactWitness
import JSP000404Research.UnitSameSignOccurrence
import Mathlib.Tactic

/-!
# Same-sign unit forced in the n=4 one-transition exact-witness branch

In the n=4 ten-slot equality terminal every minimum has exactly two unit
quotients.  The exact-witness centre is one of those minima.

If its support-three sign path is in the one-transition branch, the exact
witness transition quotient is 1.  Hence the second unit quotient lies in one
of the constant-sign blocks and is a same-sign occurrence.

This is the local certificate needed to remove at least one unit slot from the
critical-transition phase-cover universe.
-/

namespace JSP000404Research

theorem six_point_n_four_exactWitness_one_transition_has_sameSign_unit
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
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (pre post : List ℕ)
    (hrays : (C W.b).rays = first :: rest)
    (hq :
      quotientList t (C W.b).gaps =
        pre ++ 1 :: post)
    (hsigns :
      liftedCentreSignPath hp W.b first rest =
        List.replicate pre.length (raySignAt hp W.b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp W.b first)) :
    SameSignQuotientOccurs 1
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t (C W.b).gaps) := by
  have hshape :=
    six_point_n_four_exactWitness_forced_11200
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
  have hunitFn :
      unitSupport (centreQuotient (C W.b) t) = 2 :=
    hshape.1
  have hunitList :
      listUnitCount (quotientList t (C W.b).gaps) = 2 := by
    rw [centre_listUnitCount_eq_unitSupport]
    exact hunitFn
  rw [hq] at hunitList
  rw [hq, hsigns]
  exact sameSign_unit_occurs_of_two_units_one_transition
    (raySignAt hp W.b first) pre post hunitList

/-- Strengthened n=4 exact-witness terminal:
either the one-transition branch contains an explicit same-sign unit, or the
witness centre has exactly three sign transitions. -/
theorem six_point_n_four_exactWitness_sameSign_unit_or_three_transitions
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
      ∃ first : OtherVertex W.b,
        ∃ rest : List (OtherVertex W.b),
        ∃ pre post : List ℕ,
          (C W.b).rays = first :: rest ∧
          quotientList t (C W.b).gaps = pre ++ 1 :: post ∧
          liftedCentreSignPath hp W.b first rest =
            List.replicate pre.length (raySignAt hp W.b first) ++
              List.replicate (post.length + 1)
                (!raySignAt hp W.b first) ∧
          SameSignQuotientOccurs 1
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest)
            (quotientList t (C W.b).gaps)
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
    six_point_n_four_exactWitness_terminal_dichotomy
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
    with hOne | hThree
  · left
    rcases hOne with
      ⟨hexposed, first, rest, pre, post,
        hrays, hq, hsigns⟩
    have hsame :=
      six_point_n_four_exactWitness_one_transition_has_sameSign_unit
        hp hcap hdelta0 hdeltaHalf ht hlam
        W C hcard top hTop hMin hunitTotal
        first rest pre post hrays hq hsigns
    exact ⟨hexposed, first, rest, pre, post,
      hrays, hq, hsigns, hsame⟩
  · exact Or.inr hThree

#print axioms six_point_n_four_exactWitness_one_transition_has_sameSign_unit
#print axioms six_point_n_four_exactWitness_sameSign_unit_or_three_transitions

end JSP000404Research
