import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.TransitionCertificateFromDecomposition
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Support-three transition dichotomy

For a concrete centre with exactly three positive quotient gaps, sign changes
can occur only on those positive gaps.  The lifted canonical sign path is
antiperiodic, so its transition count is odd.

Hence the transition count is exactly one or exactly three.

If it is one, the unique transition decomposition reconstructs the same
common-signed strict-support interval used in the support<=2 theory, so the
centre is strictly exposed.

Therefore every non-exposed support-three centre is forced into the single
extreme combinatorial shape: all three available positive-gap transition
slots are used.
-/

namespace JSP000404Research

theorem support_three_transition_count_one_or_three
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
      positiveSupport (centreQuotient C t) = 3) :
    ∃ first : OtherVertex i,
      ∃ rest : List (OtherVertex i),
        C.rays = first :: rest ∧
        (
          boolTransitionCountFrom
              (raySignAt hp i first)
              (liftedCentreSignPath hp i first rest) = 1
          ∨
          boolTransitionCountFrom
              (raySignAt hp i first)
              (liftedCentreSignPath hp i first rest) = 3
        ) := by
  obtain ⟨first, rest, hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases h : C.rays with
    | nil =>
        exact False.elim (C.nonempty h)
    | cons first rest =>
        exact ⟨first, rest, h⟩
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap ht htone hlam i C first rest hrays
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 3 := by
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hle :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) ≤ 3 := by
    exact (boolTransitionCount_le_listPositiveCount
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges).trans_eq hsupportList
  have hlast :
      boolLastFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
        =
      !raySignAt hp i first :=
    liftedCentreSignPath_last_not hp i first rest
  have hmod :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) % 2 = 1 :=
    boolTransitionCountFrom_mod_two_eq_one_of_last_not
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      hlast
  refine ⟨first, rest, hrays, ?_⟩
  omega

/-- A support-three centre with only one sign transition is strictly exposed. -/
theorem strictlyExposedAt_of_support_three_one_transition
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
    (htrans :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 1) :
    StrictlyExposedAt p i := by
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap ht htone hlam i C first rest hrays
  obtain ⟨pre, post, qe, hqe, hq, hsign⟩ :=
    one_transition_positive_gap_decomposition
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges htrans
  obtain ⟨H, _⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp ht i C first rest pre post qe
      hrays hqe hq hsign
  exact strictlyExposedAt_of_common_signed_interval
    H.width_nonneg H.width_lt_pi H.sigma H.repr

/-- Main dichotomy: support three is either exposed or uses all three transition
slots. -/
theorem support_three_strictlyExposed_or_three_transitions
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
      positiveSupport (centreQuotient C t) = 3) :
    StrictlyExposedAt p i ∨
      ∃ first : OtherVertex i,
        ∃ rest : List (OtherVertex i),
          C.rays = first :: rest ∧
          boolTransitionCountFrom
              (raySignAt hp i first)
              (liftedCentreSignPath hp i first rest) = 3 := by
  obtain ⟨first, rest, hrays, hcase⟩ :=
    support_three_transition_count_one_or_three
      hp hcap ht htone hlam i C hsupport
  rcases hcase with hone | hthree
  · left
    exact strictlyExposedAt_of_support_three_one_transition
      hp hcap ht htone hlam i C first rest hrays hone
  · right
    exact ⟨first, rest, hrays, hthree⟩

/-- A non-exposed support-three centre must use all three positive transition
slots. -/
theorem three_transitions_of_support_three_not_strictlyExposed
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
        boolTransitionCountFrom
            (raySignAt hp i first)
            (liftedCentreSignPath hp i first rest) = 3 := by
  rcases support_three_strictlyExposed_or_three_transitions
      hp hcap ht htone hlam i C hsupport with hexp | hthree
  · exact False.elim (hnot hexp)
  · exact hthree

#print axioms support_three_transition_count_one_or_three
#print axioms strictlyExposedAt_of_support_three_one_transition
#print axioms support_three_strictlyExposed_or_three_transitions
#print axioms three_transitions_of_support_three_not_strictlyExposed

end JSP000404Research
