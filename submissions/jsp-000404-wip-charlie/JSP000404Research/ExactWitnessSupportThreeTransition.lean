import JSP000404Research.ExactWitnessTransitionOccurrence
import JSP000404Research.SupportThreeTransitionDichotomy
import Mathlib.Tactic

/-!
# Exact-witness support-three transition dichotomy

For an exact maximum-angle witness centre with quotient support three, use the
ray display supplied by the exact unit-transition occurrence.

On that very same lifted sign path:

* sign changes occur only on positive quotients;
* antiperiodicity makes the transition count odd;
* support three bounds it by three.

Hence the transition count is one or three.

In the one-transition branch, the exact witness occurrence of quotient one
identifies the unique transition quotient as one.  The usual one-transition
support interval then proves strict exposure.

In the three-transition branch, quotient one remains explicitly certified as
one of the transition positions on that same displayed path.
-/

namespace JSP000404Research

/-- Exact-witness support-three dichotomy on one common ray display. -/
theorem exactWitness_support_three_exposed_unit_transition_or_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    (
      StrictlyExposedAt p W.b ∧
      ∃ first : OtherVertex W.b,
        ∃ rest : List (OtherVertex W.b),
        ∃ pre post : List ℕ,
          C.rays = first :: rest ∧
          quotientList t C.gaps = pre ++ 1 :: post ∧
          liftedCentreSignPath hp W.b first rest =
            List.replicate pre.length (raySignAt hp W.b first) ++
              List.replicate (post.length + 1)
                (!raySignAt hp W.b first)
    )
    ∨
    (
      ∃ first : OtherVertex W.b,
        ∃ rest : List (OtherVertex W.b),
          C.rays = first :: rest ∧
          TransitionQuotientOccurs 1
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest)
            (quotientList t C.gaps) ∧
          boolTransitionCountFrom
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest) = 3
    ) := by
  obtain ⟨first, rest, hrays, hocc⟩ :=
    exactWitness_unit_transition_occurs
      hp hcap hn hdelta0 ht hlam W C
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp W.b first)
        (liftedCentreSignPath hp W.b first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam
      W.b C first rest hrays
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 3 := by
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hle :
      boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
        ≤ 3 := by
    exact
      (boolTransitionCount_le_listPositiveCount
        (raySignAt hp W.b first)
        (liftedCentreSignPath hp W.b first rest)
        (quotientList t C.gaps)
        hchanges).trans_eq hsupportList
  have hlast :
      boolLastFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
        =
      !raySignAt hp W.b first :=
    liftedCentreSignPath_last_not hp W.b first rest
  have hmod :
      boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) % 2 = 1 :=
    boolTransitionCountFrom_mod_two_eq_one_of_last_not
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      hlast
  have hcases :
      boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) = 1
      ∨
      boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) = 3 := by
    omega
  rcases hcases with hOne | hThree
  · left
    obtain ⟨pre, post, qe, hqe0, hq, hsign⟩ :=
      one_transition_positive_gap_decomposition
        (raySignAt hp W.b first)
        (liftedCentreSignPath hp W.b first rest)
        (quotientList t C.gaps)
        hchanges hOne
    have hqe :
        qe = 1 :=
      unique_transition_quotient_eq_of_occurs
        (raySignAt hp W.b first)
        (liftedCentreSignPath hp W.b first rest)
        (quotientList t C.gaps)
        pre post qe 1 hq hsign hocc
    have hexposed :
        StrictlyExposedAt p W.b := by
      obtain ⟨H, _hHqe⟩ :=
        exists_highExponentTransitionIntervalCertificate_of_decomposition
          hp htpos W.b C first rest pre post qe
          hrays hqe0 hq hsign
      exact strictlyExposedAt_of_common_signed_interval
        H.width_nonneg H.width_lt_pi H.sigma H.repr
    subst qe
    exact Or.inl
      ⟨hexposed, first, rest, pre, post,
        hrays, hq, hsign⟩
  · right
    exact Or.inr
      ⟨first, rest, hrays, hocc, hThree⟩

/-- Non-exposed exact-witness support-three centres necessarily lie in the
three-transition branch, and quotient one is one of those transition slots. -/
theorem exactWitness_support_three_three_transitions_of_not_exposed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hnot : ¬ StrictlyExposedAt p W.b) :
    ∃ first : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
        C.rays = first :: rest ∧
        TransitionQuotientOccurs 1
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
          (quotientList t C.gaps) ∧
        boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) = 3 := by
  rcases
    exactWitness_support_three_exposed_unit_transition_or_three
      hp hcap hn hdelta0 ht hlam W C hsupport
    with hOne | hThree
  · exact False.elim (hnot hOne.1)
  · exact hThree

#print axioms exactWitness_support_three_exposed_unit_transition_or_three
#print axioms exactWitness_support_three_three_transitions_of_not_exposed

end JSP000404Research
