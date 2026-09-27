import JSP000404Research.CentreSignPath
import JSP000404Research.BoolSignPath
import Mathlib.Tactic

/-!
# Transition count bounded by positive quotient support

ChangesOnlyOnPositive says every sign-changing step is carried by a nonzero
quotient.  Therefore the number of sign transitions is at most the number of
positive quotient entries.

For a concrete centre the lifted cyclic sign path is antiperiodic.  Hence if
the quotient support is exactly two, transition parity is odd and the count is
at most two, so it is exactly one.
-/

namespace JSP000404Research

theorem transitionCount_le_positiveCount_of_changesOnlyOnPositive
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (h : ChangesOnlyOnPositive a signs qs) :
    boolTransitionCountFrom a signs ≤ listPositiveCount qs := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          simp [boolTransitionCountFrom, listPositiveCount]
      | cons q qs =>
          simp [ChangesOnlyOnPositive] at h
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at h
      | cons q qs =>
          rcases h with ⟨hchange,hrest⟩
          have hi := ih b qs hrest
          by_cases hab : a = b
          · subst b
            simp [boolTransitionCountFrom]
            exact hi
          · have hq : q ≠ 0 := hchange hab
            simp [boolTransitionCountFrom, hab,
              listPositiveCount, hq]
            omega

/-- Concrete canonical centre with support two has exactly one lifted sign
transition. -/
theorem centre_support_two_transitionCount_eq_one
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
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    boolTransitionCountFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
      = 1 := by
  have hchanges :=
    centre_changesOnlyOnPositive
      hp hcap ht htone hlam i C first rest hrays
  have hle0 :=
    transitionCount_le_positiveCount_of_changesOnlyOnPositive
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges
  have hqSupport :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn C t,
      listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  rw [hqSupport] at hle0
  have hlast :=
    liftedCentreSignPath_last_not hp i first rest
  exact boolTransitionCountFrom_eq_one_of_last_not_of_le_two
    (raySignAt hp i first)
    (liftedCentreSignPath hp i first rest)
    hlast hle0

#print axioms transitionCount_le_positiveCount_of_changesOnlyOnPositive
#print axioms centre_support_two_transitionCount_eq_one

end JSP000404Research
