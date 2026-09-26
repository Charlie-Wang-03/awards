import JSP000404Research.ExactWitnessUnitQuotient
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
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hscale :
      t * (lam / Real.pi) = 1 := by
    rw [hlam]
    field_simp [ne_of_gt htpos, Real.pi_ne_zero]

  rcases exactWitness_ordered_short_gap_or_wrap_eq_lam
      hp hn hdelta0 ht hlam W horder with hordinary | hwrap
  · have hjk :
        rayThetaAt hp W.b ja <
          rayThetaAt hp W.b kc := by
      dsimp [ja, kc]
      linarith
    have hno :
        ∀ x : OtherVertex W.b,
          ¬ (rayThetaAt hp W.b ja <
                rayThetaAt hp W.b x ∧
             rayThetaAt hp W.b x <
                rayThetaAt hp W.b kc) := by
      intro x hins
      exact no_ray_strictly_inside_exactWitness_ordinary_short_arc
        hp hcap hn hdelta0 ht hlam W x
        (by simpa [ja] using hins.1)
        (by simpa [kc] using hins.2)
        (by simpa [ja, kc] using hordinary)
    obtain ⟨m, hm, hmLow, hmHigh⟩ :=
      C.exists_adjacent_angles_of_no_strict_between
        hjk hno
    have hmRays : m + 1 < C.rays.length := by
      rw [← C.angles_length]
      exact hm
    have hthetaLeft :
        rayThetaAt hp W.b (C.rays[m]) =
          rayThetaAt hp W.b ja := by
      have h := hmLow
      simpa [CentreProjectiveCycle.angles] using h
    have hthetaRight :
        rayThetaAt hp W.b (C.rays[m + 1]) =
          rayThetaAt hp W.b kc := by
      have h := hmHigh
      simpa [CentreProjectiveCycle.angles] using h
    have hsignLeft :
        raySignAt hp W.b (C.rays[m]) =
          raySignAt hp W.b ja :=
      raySignAt_eq_of_rayThetaAt_eq
        hp hcap htpos hlam W.b
        (C.rays[m]) ja hthetaLeft
    have hsignRight :
        raySignAt hp W.b (C.rays[m + 1]) =
          raySignAt hp W.b kc :=
      raySignAt_eq_of_rayThetaAt_eq
        hp hcap htpos hlam W.b
        (C.rays[m + 1]) kc hthetaRight
    have hendNe :
        raySignAt hp W.b ja ≠
          raySignAt hp W.b kc :=
      exactWitness_ordinary_short_endpoint_sign_ne
        hp hn hdelta0 ht hlam W horder
        (by simpa [ja, kc] using hordinary)
    have hchange :
        raySignAt hp W.b (C.rays[m]) ≠
          raySignAt hp W.b (C.rays[m + 1]) := by
      rw [hsignLeft, hsignRight]
      exact hendNe
    have hocc :=
      centre_transitionQuotientOccurs_at_adjacent_index
        hp C t first rest hrays m hmRays hchange
    have hqOne :
        (quotientList t C.gaps)[m] = 1 := by
      rw [centre_adjacent_quotient_getElem_eq C t m hm]
      rw [hmLow, hmHigh]
      dsimp [ja, kc] at hordinary
      rw [hordinary, hscale]
      norm_num
    rw [hqOne] at hocc
    exact hocc

  · have hsorted :
        (first :: rest).Pairwise
          (fun x y =>
            rayThetaAt hp W.b x ≤ rayThetaAt hp W.b y) := by
      simpa [hrays] using C.theta_sorted
    have hjaMem :
        ja ∈ first :: rest := by
      simpa [hrays] using C.mem_rays_iff ja
    have hkcMem :
        kc ∈ first :: rest := by
      simpa [hrays] using C.mem_rays_iff kc
    have hfirstLeA :
        rayThetaAt hp W.b first ≤
          rayThetaAt hp W.b ja := by
      rcases hjaMem with hEq | htail
      · simpa [hEq]
      · rw [List.pairwise_cons] at hsorted
        exact hsorted.1 ja htail
    have hfirstGeA :
        rayThetaAt hp W.b ja ≤
          rayThetaAt hp W.b first := by
      by_contra hnot
      have hlt :
          rayThetaAt hp W.b first <
            rayThetaAt hp W.b ja :=
        lt_of_not_ge hnot
      exact no_ray_strictly_inside_exactWitness_wrap_short_arc
        hp hcap hn hdelta0 ht hlam W first
        horder
        (Or.inr (by simpa [ja] using hlt))
        (by simpa [ja, kc] using hwrap)
    have hfirstEq :
        rayThetaAt hp W.b first =
          rayThetaAt hp W.b ja :=
      le_antisymm hfirstLeA hfirstGeA

    let last : OtherVertex W.b :=
      (first :: rest).getLast (by simp)
    have hkcLeLast :
        rayThetaAt hp W.b kc ≤
          rayThetaAt hp W.b last := by
      have h :=
        hsorted.rel_getLast hkcMem
      simpa [last] using h
    have hlastLeK :
        rayThetaAt hp W.b last ≤
          rayThetaAt hp W.b kc := by
      by_contra hnot
      have hlt :
          rayThetaAt hp W.b kc <
            rayThetaAt hp W.b last :=
        lt_of_not_ge hnot
      exact no_ray_strictly_inside_exactWitness_wrap_short_arc
        hp hcap hn hdelta0 ht hlam W last
        horder
        (Or.inl (by simpa [kc] using hlt))
        (by simpa [ja, kc] using hwrap)
    have hlastEq :
        rayThetaAt hp W.b last =
          rayThetaAt hp W.b kc :=
      le_antisymm hlastLeK hkcLeLast
    have hlastD :
        rest.getLastD first = last := by
      dsimp [last]
      cases rest with
      | nil =>
          simp
      | cons r rs =>
          simp [List.getLastD_cons]

    have hsignFirst :
        raySignAt hp W.b first =
          raySignAt hp W.b ja :=
      raySignAt_eq_of_rayThetaAt_eq
        hp hcap htpos hlam W.b
        first ja hfirstEq
    have hsignLast :
        raySignAt hp W.b (rest.getLastD first) =
          raySignAt hp W.b kc := by
      rw [hlastD]
      exact raySignAt_eq_of_rayThetaAt_eq
        hp hcap htpos hlam W.b
        last kc hlastEq
    have hendNe :
        raySignAt hp W.b kc ≠
          !raySignAt hp W.b ja :=
      exactWitness_wrap_short_endpoint_lifted_sign_ne
        hp hn hdelta0 ht hlam W horder
        (by simpa [ja, kc] using hwrap)
    have hchange :
        raySignAt hp W.b (rest.getLastD first) ≠
          !raySignAt hp W.b first := by
      rw [hsignLast, hsignFirst]
      exact hendNe
    have hocc :=
      centre_transitionQuotientOccurs_at_wrap
        hp C t first rest hrays hchange
    have hqOne :
        wrapRayQuotient hp W.b t first
            (rest.getLastD first) = 1 := by
      unfold wrapRayQuotient
      rw [hfirstEq, hlastD, hlastEq]
      dsimp [ja, kc] at hwrap
      rw [hwrap, hscale]
      norm_num
    rw [hqOne] at hocc
    exact hocc

/-- Cut-independent exact-witness transition occurrence. -/
theorem exactWitness_unit_transition_occurs
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

#print axioms exactWitness_unit_transition_occurs_of_ordered
#print axioms exactWitness_unit_transition_occurs

end JSP000404Research
