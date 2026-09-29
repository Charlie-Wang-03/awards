import JSP000404Research.SupportThreeTransitionDichotomy
import JSP000404Research.SaturatedTransitionSupport
import Mathlib.Tactic

/-!
# Exact transition support at a non-exposed support-three centre

A support-three centre has exactly three positive quotient positions.  If it is
not strictly exposed, the existing transition dichotomy forces exactly three
sign changes.  Since sign changes can occur only on positive quotient
positions, the count is saturated and therefore every positive quotient is
itself a sign transition.

This retains more information than the bare statement
`boolTransitionCountFrom = 3`.
-/

namespace JSP000404Research

theorem nonexposed_support_three_changes_exactly_on_positive
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hnot : ¬ StrictlyExposedAt p i) :
    ∃ first : OtherVertex i,
      ∃ rest : List (OtherVertex i),
        C.rays = first :: rest ∧
        ChangesExactlyOnPositive
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
          (quotientList t C.gaps) := by
  obtain ⟨first,rest,hrays,htrans⟩ :=
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap ht htone hlam i C hsupport hnot
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap ht htone hlam i C first rest hrays
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 3 := by
    rw [← centreQuotient_ofFn C t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hsat :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
        =
      listPositiveCount (quotientList t C.gaps) := by
    rw [htrans, hsupportList]
  exact ⟨first,rest,hrays,
    changesExactlyOnPositive_of_saturated_count
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges hsat⟩

#print axioms nonexposed_support_three_changes_exactly_on_positive

end JSP000404Research
