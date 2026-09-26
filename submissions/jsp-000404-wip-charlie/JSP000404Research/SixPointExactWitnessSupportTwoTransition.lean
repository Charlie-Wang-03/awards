import JSP000404Research.ExactWitnessTransitionQuotient
import JSP000404Research.HiddenSameSignQuotient
import JSP000404Research.SixPointExactWitnessTerminal
import JSP000404Research.FourCentreTransitionCases
import Mathlib.Tactic

/-!
# Exact-witness support-two third-layer transition shape

For an exact-witness centre with exponent n-3 and quotient support two:

* exact-witness geometry forces a transition quotient exactly equal to 1;
* deficit-three arithmetic gives total quotient mass n-1;
* therefore the second positive quotient is n-2;
* the transition is unique, so the n-2 quotient lies on a same-sign step.

This is stronger than the previous membership-only support-two classification:
it records the sign type of each positive quotient.
-/

namespace JSP000404Research

theorem exactWitness_deficitThree_support_two_hidden_n_sub_two_mem
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
    n - 2 ∈ quotientList t C.gaps := by
  have hdelta1 : delta < 1 := by linarith
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn]
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
  have hhidden :=
    n_sub_one_mem_of_positiveCount_two_and_one_mem
      (quotientList t C.gaps) (n - 1)
      (by omega)
      hsupportList hsumList hone
  have hsub : (n - 1) - 1 = n - 2 := by omega
  rwa [hsub] at hhidden

/-- Full sign-sensitive support-two classification.

For any displayed head/tail ray representation, the quotient list has a unique
transition cut carrying quotient 1, and the hidden quotient n-2 occurs on a
same-sign step.
-/
theorem exactWitness_deficitThree_support_two_transition_and_hidden_sameSign
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
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (hrays : C.rays = first :: rest)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ pre post : List ℕ,
      quotientList t C.gaps = pre ++ 1 :: post ∧
      liftedCentreSignPath hp W.b first rest =
        List.replicate pre.length (raySignAt hp W.b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp W.b first) ∧
      SameSignQuotientOccurs (n - 2)
        (raySignAt hp W.b first)
        (liftedCentreSignPath hp W.b first rest)
        (quotientList t C.gaps) := by
  obtain ⟨pre, post, hq, hsign⟩ :=
    exactWitness_unique_transition_decomposition_unit
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C first rest hrays
      (by omega)
  have hhidden :
      n - 2 ∈ quotientList t C.gaps :=
    exactWitness_deficitThree_support_two_hidden_n_sub_two_mem
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      W C hexp hsupport
  have hne : n - 2 ≠ 1 := by omega
  have hsame :
      SameSignQuotientOccurs (n - 2)
        (raySignAt hp W.b first)
        (liftedCentreSignPath hp W.b first rest)
        (quotientList t C.gaps) := by
    rw [hq, hsign]
    exact sameSignQuotientOccurs_of_two_blocks
      (raySignAt hp W.b first)
      pre post 1 (n - 2) hne
      (by
        rw [← hq]
        exact hhidden)
  exact ⟨pre, post, hq, hsign, hsame⟩

#print axioms exactWitness_deficitThree_support_two_hidden_n_sub_two_mem
#print axioms exactWitness_deficitThree_support_two_transition_and_hidden_sameSign

end JSP000404Research
