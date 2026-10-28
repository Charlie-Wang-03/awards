import JSP000404Research.NonExposedSupportThreeExactTransitions
import Mathlib.Tactic

/-!
# Original support-three with three sign transitions uses EVERY positive gap

A genuine support-three projective cycle has three positive integer
quotient gaps. Under AngleCap, sign changes occur only at a positive
quotient. Therefore, when the ORIGINAL canonical ray sign path
undergoes exactly three transitions, all positive quotient gap
positions must be used as sign transitions.

The result does NOT assume non-exposure: triple-transition is a
separately verifiable actual geometric hypothesis. In the top+next
large-centre branch it can be supplied for at least three centres
by PlanarTopNextTripleTransitionsMultiplicity, once that separate
proof is kernel certified.

No artificial Boolean-hole credit or global matching is asserted.
-/

namespace JSP000404Research

theorem support_three_triple_transition_changes_exactly_on_positive
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (hsupport : positiveSupport (centreQuotient C t) = 3)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hthree :
      boolTransitionCountFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest) = 3) :
    ChangesExactlyOnPositive
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps) := by
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam i C first rest hrays
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 3 := by
    rw [← centreQuotient_ofFn C t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hsat :
      boolTransitionCountFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest) =
          listPositiveCount (quotientList t C.gaps) := by
    rw [hthree, hsupportList]
  exact changesExactlyOnPositive_of_saturated_count
    (raySignAt hp i first)
    (liftedCentreSignPath hp i first rest)
    (quotientList t C.gaps) hchanges hsat

#print axioms support_three_triple_transition_changes_exactly_on_positive

end JSP000404Research
