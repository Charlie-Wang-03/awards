import JSP000404Research.CutMixedSupportOneTwoBoundarySwapReduction
import JSP000404Research.ExactWitnessUniqueTransition
import JSP000404Research.SixPointExactWitnessTerminal
import Mathlib.Tactic

/-!
# Exact-witness reduction in the mixed support-(1,2) boundary-swap branch

In the support-one/support-two boundary-swap terminal, every transition
certificate at the support-two bad minimum has quotient two.

If that same minimum were the centre of an exact maximum-angle witness, its
support-two sign path would have a unique transition and exact-witness
geometry would force that transition quotient to be one.

Constructing the compact transition certificate from this exact decomposition
therefore gives the contradiction 1=2.

Consequently the exact-witness centre must lie among the remaining
support-three / three-transition minima.
-/

namespace JSP000404Research

theorem exactWitness_centre_ne_support_two_bad_of_one_two_span
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1)
    (W : ExactAngleWitness p lam) :
    W.b ≠ b := by
  intro hW
  subst b
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨first, rest, pre, post, qe,
      hrays, hqe0, hq, hsign⟩ :=
    exists_transition_decomposition_of_support_le_two
      hp hcap htpos htone hlam
      W.b (C W.b) (by rw [hsupB]; omega)

  have hqeOne :
      qe = 1 :=
    exactWitness_transition_decomposition_qe_eq_one
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W (C W.b)
      first rest pre post qe
      hrays hq hsign

  obtain ⟨H, hHqe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos W.b (C W.b)
      first rest pre post qe
      hrays hqe0 hq hsign

  have hqeTwo :
      H.qe = 2 :=
    cut_span_n_sub_one_support_two_any_transition_qe_eq_two
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hc0 hcpi hta htb hab
      hTop hA hsupA hB hsupB
      hBadB R hvalues hspan H

  rw [hHqe, hqeOne] at hqeTwo
  omega

/-- In the same branch, once the exact-witness centre is known to belong to
the n-3 layer and hence differs from top/support-one/support-two, it is forced
into the support-three, non-exposed, three-transition shape. -/
theorem exactWitness_forced_support_three_three_transitions_of_one_two_span
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1)
    (W : ExactAngleWitness p lam)
    (hWexp : centreExponent (C W.b) t = n - 3) :
    positiveSupport (centreQuotient (C W.b) t) = 3 ∧
    ¬ StrictlyExposedAt p W.b ∧
    ∃ first : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
        (C W.b).rays = first :: rest ∧
        TransitionQuotientOccurs 1
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
          (quotientList t (C W.b).gaps) ∧
        boolTransitionCountFrom
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest) = 3 := by
  have hWt : W.b ≠ top := by
    intro h
    subst W.b
    rw [hTop] at hWexp
    omega
  have hWa : W.b ≠ a := by
    intro h
    subst W.b
    have hnot :=
      exactWitness_deficitThree_not_support_one
        hp hcap (by omega : 4 ≤ n)
        hdelta0 hdeltaHalf ht hlam
        W (C a) hWexp
    exact hnot hsupA
  have hWb :
      W.b ≠ b :=
    exactWitness_centre_ne_support_two_bad_of_one_two_span
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hc0 hcpi hta htb hab
      hTop hA hsupA hB hsupB
      hBadB R hvalues hspan W

  obtain ⟨hsupW, hnotW, first, rest, hrays, hthree⟩ :=
    fourth_minimum_support_three_three_transitions_of_support_one_two_span
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hc0 hcpi
      hta htb hWt hab hWa hWb
      hTop hA hsupA hB hsupB hWexp
      hBadB R hvalues hspan

  obtain ⟨first', rest', hrays', hocc, hthree'⟩ :=
    exactWitness_support_three_three_transitions_of_not_exposed
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W (C W.b) hsupW hnotW

  exact ⟨hsupW, hnotW,
    first', rest', hrays', hocc, hthree'⟩

#print axioms exactWitness_centre_ne_support_two_bad_of_one_two_span
#print axioms exactWitness_forced_support_three_three_transitions_of_one_two_span

end JSP000404Research
