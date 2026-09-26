import JSP000404Research.ExactWitnessTransitionOccurrence
import JSP000404Research.DeficitThreeSupportTwoHidden
import JSP000404Research.SixPointExactWitnessTerminal
import Mathlib.Tactic

/-!
# The support-two exact-witness transition quotient is one

At an exact maximum-angle witness centre, quotient one occurs on a genuine
sign-transition step.

If the centre quotient support is at most two, antiperiodicity forces exactly
one sign transition.  Therefore the unique-transition decomposition must use
qe=1.

For an n-3/support-two exact-witness centre, the total quotient mass is n-1.
Hence the unique other positive quotient is n-2 and lies on a same-sign step,
paying a genuine Euclidean angle of at least (n-2)*lambda.
-/

namespace JSP000404Research

/-- Exact-witness support<=2 transition decomposition with distinguished
transition quotient exactly one. -/
theorem exists_exactWitness_unit_transition_decomposition_of_support_le_two
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
      positiveSupport (centreQuotient C t) ≤ 2) :
    ∃ first : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
      ∃ pre post : List ℕ,
        C.rays = first :: rest ∧
        quotientList t C.gaps = pre ++ 1 :: post ∧
        liftedCentreSignPath hp W.b first rest =
          List.replicate pre.length (raySignAt hp W.b first) ++
            List.replicate (post.length + 1)
              (!raySignAt hp W.b first) := by
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
  have hlast :
      boolLastFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
        =
      !raySignAt hp W.b first :=
    liftedCentreSignPath_last_not hp W.b first rest
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) ≤ 2 := by
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have htrans :
      boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
        = 1 :=
    one_sign_transition_of_support_le_two
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps)
      hchanges hlast hsupportList
  obtain ⟨pre, post, qe, hqe0, hq, hsign⟩ :=
    one_transition_positive_gap_decomposition
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps)
      hchanges htrans
  have hqe :
      qe = 1 :=
    unique_transition_quotient_eq_of_occurs
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps)
      pre post qe 1
      hq hsign hocc
  subst qe
  exact ⟨first, rest, pre, post,
    hrays, hq, hsign⟩

/-- Exact-witness n-3/support-two branch has a hidden same-sign quotient n-2
and hence a genuine angle at least (n-2)*lambda. -/
theorem exactWitness_deficitThree_support_two_hidden_large_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ x y : OtherVertex W.b,
      x ≠ y ∧
      (((n - 2 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p W.b) (p y.1) := by
  obtain ⟨first, rest, pre, post,
      hrays, hq, hsign⟩ :=
    exists_exactWitness_unit_transition_decomposition_of_support_le_two
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
      (by rw [hsupport])
  have hsupportList :
      listPositiveCount (pre ++ 1 :: post) = 2 := by
    rw [← hq, ← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hdelta1 : delta < 1 := by linarith
  have hsumFn :=
    deficit_three_support_two_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hsumList :
      (pre ++ 1 :: post).sum = n - 1 := by
    rw [← hq, ← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  exact
    deficit_three_support_two_unit_transition_hidden_angle
      hp htpos hlam W.b C hn
      first rest pre post
      hrays hq hsign hsupportList hsumList

#print axioms exists_exactWitness_unit_transition_decomposition_of_support_le_two
#print axioms exactWitness_deficitThree_support_two_hidden_large_angle

end JSP000404Research
