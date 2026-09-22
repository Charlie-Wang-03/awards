import JSP000404Research.TransitionCertificateFromDecomposition
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Transition interval certificate from support at most two

The existing automatic constructor for HighExponentTransitionIntervalCertificate
uses the sufficient hypothesis k >= n-2 only to deduce positiveSupport <= 2.

The actual geometric input is weaker: any concrete centre whose quotient
support is at most two has, by antiperiodicity, exactly one sign transition.
That transition is carried by a positive quotient and reconstructs the same
quantitative support interval certificate.

This extension is essential at deficit three: support-one and support-two
centres with exponent n-3 are no longer in the old k>=n-2 range, but they
still have the identical one-transition geometry.
-/

namespace JSP000404Research

theorem exists_transition_decomposition_of_support_le_two
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
      positiveSupport (centreQuotient C t) ≤ 2) :
    ∃ first : OtherVertex i,
      ∃ rest : List (OtherVertex i),
      ∃ pre post : List ℕ, ∃ qe : ℕ,
        C.rays = first :: rest ∧
        qe ≠ 0 ∧
        quotientList t C.gaps =
          pre ++ qe :: post ∧
        liftedCentreSignPath hp i first rest =
          List.replicate pre.length (raySignAt hp i first) ++
            List.replicate (post.length + 1)
              (!raySignAt hp i first) := by
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
  have hlast :
      boolLastFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
        =
      !raySignAt hp i first :=
    liftedCentreSignPath_last_not hp i first rest
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) ≤ 2 := by
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  obtain ⟨pre, post, qe, hqe, hq, hsign⟩ :=
    antiperiodic_positive_transition_gap_of_support_le_two
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges hlast hsupportList
  exact ⟨first, rest, pre, post, qe,
    hrays, hqe, hq, hsign⟩

/-- Quantitative support-arc certificate for every support<=2 concrete centre,
with the actual transition quotient preserved. -/
theorem exists_transitionIntervalCertificate_of_support_le_two
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
      positiveSupport (centreQuotient C t) ≤ 2) :
    ∃ H : HighExponentTransitionIntervalCertificate hp t i C,
      H.qe ≠ 0 := by
  obtain ⟨first, rest, pre, post, qe,
      hrays, hqe, hq, hsign⟩ :=
    exists_transition_decomposition_of_support_le_two
      hp hcap ht htone hlam i C hsupport
  obtain ⟨H, hHqe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp ht i C first rest pre post qe
      hrays hqe hq hsign
  refine ⟨H, ?_⟩
  rw [hHqe]
  exact hqe

/-- Exact support one gives the usual transition quotient exponent+1 even
outside the old high-exponent constructor range. -/
theorem support_one_transitionInterval_qe_eq_exponent_add_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {t : ℝ}
    (C : CentreProjectiveCycle hp i)
    (H : HighExponentTransitionIntervalCertificate hp t i C)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    H.qe = centreExponent C t + 1 :=
  highTransition_qe_eq_exponent_add_one_of_support_one
    C H hsupport

#print axioms exists_transition_decomposition_of_support_le_two
#print axioms exists_transitionIntervalCertificate_of_support_le_two
#print axioms support_one_transitionInterval_qe_eq_exponent_add_one

end JSP000404Research
