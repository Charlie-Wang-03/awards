import JSP000404Research.ExactWitnessTransitionQuotient
import JSP000404Research.SixPointExactWitnessTerminal
import JSP000404Research.HiddenSameSignQuotient
import JSP000404Research.GeneralNontransitionPayment
import Mathlib.Tactic

/-!
# Unique unit transition at an exact-witness support-two centre

The exact witness unit gap is a genuine sign transition.  Therefore any
one-transition two-block decomposition of the witness-centre sign path has
distinguished quotient exactly one.

For an n-3/support-two witness centre the total quotient sum is n-1.  Hence
the only other positive quotient equals n-2; since the unique transition is
the unit quotient, this n-2 quotient occurs on a same-sign step and therefore
pays a genuine Euclidean angle of at least (n-2)*lambda.
-/

namespace JSP000404Research

/-- Any displayed one-transition decomposition at the exact-witness centre has
distinguished quotient one. -/
theorem exactWitness_transition_decomposition_qe_eq_one
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
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsign :
      liftedCentreSignPath hp W.b first rest =
        List.replicate pre.length (raySignAt hp W.b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp W.b first)) :
    qe = 1 := by
  have hocc :=
    exactWitness_unit_transition_occurs
      hp hcap hn hdelta0 ht hlam W C
      first rest hrays
  exact unique_transition_quotient_eq_of_occurs
    (raySignAt hp W.b first)
    (liftedCentreSignPath hp W.b first rest)
    (quotientList t C.gaps)
    pre post qe 1 hq hsign hocc

/-- Support two plus antiperiodicity produces an exact two-block decomposition
whose unique transition quotient is one. -/
theorem exists_exactWitness_unit_transition_decomposition_of_support_two
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
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (hrays : C.rays = first :: rest)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ pre post : List ℕ,
      quotientList t C.gaps =
        pre ++ 1 :: post
      ∧
      liftedCentreSignPath hp W.b first rest =
        List.replicate pre.length (raySignAt hp W.b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp W.b first) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hchanges :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam
      W.b C first rest hrays
  have hlast :=
    liftedCentreSignPath_last_not
      hp W.b first rest
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) ≤ 2 := by
    have heq :
        listPositiveCount (quotientList t C.gaps) = 2 := by
      rw [← centreQuotient_ofFn C t]
      rw [listPositiveCount_ofFn_eq_positiveSupport]
      exact hsupport
    omega
  obtain ⟨pre, post, qe, hqe0, hq, hsign⟩ :=
    antiperiodic_positive_transition_gap_of_support_le_two
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps)
      hchanges hlast hsupportList
  have hqeOne :=
    exactWitness_transition_decomposition_qe_eq_one
      hp hcap hn hdelta0 ht hlam W C
      first rest pre post qe hrays hq hsign
  subst qe
  exact ⟨pre, post, hq, hsign⟩

/-- In the n-3/support-two exact-witness branch, the hidden n-2 quotient occurs
on a same-sign step. -/
theorem exactWitness_deficitThree_support_two_hidden_sameSign
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
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (hrays : C.rays = first :: rest) :
    SameSignQuotientOccurs (n - 2)
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps) := by
  have hdelta1 : delta < 1 := by linarith
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hsumFn :=
    deficit_three_support_two_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hsumList :
      (quotientList t C.gaps).sum = n - 1 := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have hone :
      1 ∈ quotientList t C.gaps :=
    one_mem_witnessCentre_quotientList
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
  have hhidden0 :=
    n_sub_one_mem_of_positiveCount_two_and_one_mem
      (quotientList t C.gaps) (n - 1)
      (by omega : 3 ≤ n - 1)
      hsupportList hsumList hone
  have hhidden :
      n - 2 ∈ quotientList t C.gaps := by
    simpa using hhidden0
  obtain ⟨pre, post, hq, hsign⟩ :=
    exists_exactWitness_unit_transition_decomposition_of_support_two
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
      first rest hrays hsupport
  rw [hq, hsign]
  apply sameSignQuotientOccurs_of_two_blocks
      (raySignAt hp W.b first)
      pre post 1 (n - 2)
  · omega
  · rw [← hq]
    exact hhidden

/-- Genuine hidden large-angle witness in the n-3/support-two exact-witness
branch. -/
theorem exactWitness_deficitThree_support_two_hidden_angle
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
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (hrays : C.rays = first :: rest) :
    ∃ x y : OtherVertex W.b,
      x ≠ y ∧
      (((n - 2 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle
          (p x.1) (p W.b) (p y.1) := by
  have hocc :=
    exactWitness_deficitThree_support_two_hidden_sameSign
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      W C hexp hsupport first rest hrays
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  exact sameSignQuotient_pays_angle
    hp htpos hlam W.b C first rest hrays
    (n - 2) hocc

#print axioms exactWitness_transition_decomposition_qe_eq_one
#print axioms exists_exactWitness_unit_transition_decomposition_of_support_two
#print axioms exactWitness_deficitThree_support_two_hidden_sameSign
#print axioms exactWitness_deficitThree_support_two_hidden_angle

end JSP000404Research
