import JSP000404Research.ExactWitnessUnitQuotient
import JSP000404Research.ExactWitnessTransitionOccurrence
import JSP000404Research.CentreAdjacentTransitionOccurrence
import JSP000404Research.TransitionQuotientOccurrence
import Mathlib.Tactic

/-!
# The exact-witness unit quotient is a sign transition

ExactWitnessUnitQuotient proves that the witness centre contains a quotient
equal to one.  Here we retain the position and the sign change.

For W=(a,b,c), the short projective arc between the two witness rays is empty
and has normalized scaled width exactly one.

* In the ordinary case, the two boundary direction classes occur at adjacent
  sorted ray indices.  Equal theta implies equal canonical sign within a
  direction class, while the two witness endpoint signs are opposite.
* In the wrap case, emptiness pins the first and last direction classes to the
  witness endpoints, and the lifted endpoint signs are opposite.

Thus, for any displayed ray-list head/tail representation of C, quotient 1
occurs on an actual sign-changing step.
-/

namespace JSP000404Research

open Real

theorem exactWitness_unit_transition_occurs_of_ordered
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (hrays : C.rays = first :: rest)
    (horder :
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b)
        ≤
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)) :
    TransitionQuotientOccurs 1
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps) := by
  -- This theorem is already certified existentially in the earlier
  -- position-to-occurrence module.  The ray-list head/tail representation
  -- is unique; use it instead of duplicating the angle case analysis.
  obtain ⟨wfirst, wrest, hwRays, hwOcc⟩ :=
    exists_exactWitness_unit_transition_occurs
      hp hcap hn hdelta0 ht hlam W C
  have hcons : wfirst :: wrest = first :: rest :=
    hwRays.symm.trans hrays
  injection hcons with hfirstEq hrestEq
  subst wfirst
  subst wrest
  exact hwOcc

/-- Cut-independent exact-witness transition occurrence. -/
theorem exactWitness_unit_transition_occurs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (first : OtherVertex W.b)
    (rest : List (OtherVertex W.b))
    (hrays : C.rays = first :: rest) :
    TransitionQuotientOccurs 1
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps) := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  by_cases horder :
      rayThetaAt hp W.b ja ≤ rayThetaAt hp W.b kc
  · exact exactWitness_unit_transition_occurs_of_ordered
      hp hcap hn hdelta0 ht hlam W C
      first rest hrays
      (by simpa [ja, kc] using horder)
  · have hrev :
        rayThetaAt hp W.b kc ≤
          rayThetaAt hp W.b ja :=
      le_of_not_ge horder
    have hswap :=
      exactWitness_unit_transition_occurs_of_ordered
        hp hcap hn hdelta0 ht hlam W.swapEnds C
        first rest hrays
        (by simpa [ExactAngleWitness.swapEnds, ja, kc] using hrev)
    simpa [ExactAngleWitness.swapEnds] using hswap

/-- If the exact-witness centre has quotient support at most two, then its
unique sign-transition quotient is exactly one.  This is intrinsic to the exact
witness and does not use any global transition-packing argument. -/
theorem exactWitness_unique_transition_decomposition_unit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
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
      positiveSupport (centreQuotient C t) ≤ 2) :
    ∃ pre post : List ℕ,
      quotientList t C.gaps = pre ++ 1 :: post ∧
      liftedCentreSignPath hp W.b first rest =
        List.replicate pre.length (raySignAt hp W.b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp W.b first) := by
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hchanges :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam W.b
      C first rest hrays
  have hlast :=
    liftedCentreSignPath_last_not
      hp W.b first rest
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) ≤ 2 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  obtain ⟨pre, post, qe, hqe, hq, hsign⟩ :=
    antiperiodic_positive_transition_gap_of_support_le_two
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps)
      hchanges hlast hsupportList
  have hocc :=
    exactWitness_unit_transition_occurs
      hp hcap hn hdelta0 ht hlam W C
      first rest hrays
  have hqeOne :
      qe = 1 :=
    unique_transition_quotient_eq_of_occurs
      (raySignAt hp W.b first)
      (liftedCentreSignPath hp W.b first rest)
      (quotientList t C.gaps)
      pre post qe 1 hq hsign hocc
  subst qe
  exact ⟨pre, post, hq, hsign⟩

#print axioms exactWitness_unit_transition_occurs_of_ordered
#print axioms exactWitness_unit_transition_occurs

end JSP000404Research
