import JSP000404Research.ExactWitnessTransitionPosition
import JSP000404Research.SixPointExactWitnessSupportThree
import JSP000404Research.ProjectiveGapScaling
import Mathlib.Tactic

/-!
# Exact unit-gap mass at an exact-witness support-three centre

The exact maximum-angle witness does more than produce quotient one.

Its empty short projective arc has physical projective width exactly lambda,
so after Sendov normalization its scaled projective gap is exactly one.

For a six-point n-3/support-three witness centre the three positive quotient
entries have total integer mass n.  Removing the exact unit transition leaves
integer mass n-1 on the other two positive positions.

At the real-valued gap level, the five scaled projective gaps have total t =
n+delta.  Therefore, after removing the exact gap of scaled width one and the
integer parts n-1 of the other positive gaps, *all* remaining fractional mass
is exactly delta.  In particular each remaining positive-gap fractional part
and the total scaled mass of the two zero-quotient gaps is at most delta.

This is the sharp arithmetic remainder behind the final support-three branch.
-/

namespace JSP000404Research

open Real

/-- Refined exact-witness positional certificate retaining the exact scaled
projective gap value one. -/
def ExactUnitTransitionGapPosition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) : Prop :=
  (∃ m : ℕ, ∃ hm : m + 1 < C.rays.length,
    let u : OtherVertex i :=
      C.rays.get ⟨m, by omega⟩
    let v : OtherVertex i :=
      C.rays.get ⟨m + 1, hm⟩
    t * ((rayThetaAt hp i v -
      rayThetaAt hp i u) / Real.pi) = 1
      ∧
    raySignAt hp i u ≠ raySignAt hp i v)
  ∨
  (∃ first : OtherVertex i,
    ∃ rest : List (OtherVertex i),
      C.rays = first :: rest
      ∧
      t * (((rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i (rest.getLastD first)) /
        Real.pi)) = 1
      ∧
      raySignAt hp i (rest.getLastD first) ≠
        !raySignAt hp i first)

/-- Every exact witness supplies an exact scaled unit transition gap. -/
theorem exactWitness_unit_transition_gap_position
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
    (C : CentreProjectiveCycle hp W.b) :
    ExactUnitTransitionGapPosition C t := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hscale :
      t * (lam / Real.pi) = 1 := by
    rw [hlam]
    field_simp [ne_of_gt htpos, Real.pi_ne_zero]
  by_cases horder :
      rayThetaAt hp W.b ja ≤ rayThetaAt hp W.b kc
  · rcases exactWitness_ordered_short_gap_or_wrap_eq_lam
        hp hn hdelta0 ht hlam W horder with hord | hwrap
    · left
      have hjk :
          rayThetaAt hp W.b ja <
            rayThetaAt hp W.b kc := by
        have hlamPos : 0 < lam := by
          rw [hlam]
          exact div_pos Real.pi_pos htpos
        dsimp [ja, kc] at hord ⊢
        linarith
      have hno :
          ∀ x : OtherVertex W.b,
            ¬ (rayThetaAt hp W.b ja <
                rayThetaAt hp W.b x ∧
               rayThetaAt hp W.b x <
                rayThetaAt hp W.b kc) := by
        intro x hx
        exact no_ray_strictly_inside_exactWitness_ordinary_short_arc
          hp hcap hn hdelta0 ht hlam W x
          (by simpa [ja] using hx.1)
          (by simpa [kc] using hx.2)
          (by simpa [ja, kc] using hord)
      obtain ⟨m, hm, hmLow, hmHigh⟩ :=
        C.exists_adjacent_angles_of_no_strict_between
          hjk hno
      have hmRays : m + 1 < C.rays.length := by
        rw [← C.angles_length]
        exact hm
      let u : OtherVertex W.b :=
        C.rays.get ⟨m, by omega⟩
      let v : OtherVertex W.b :=
        C.rays.get ⟨m + 1, hmRays⟩
      have huTheta :
          rayThetaAt hp W.b u =
            rayThetaAt hp W.b ja := by
        dsimp [u]
        simpa [CentreProjectiveCycle.angles] using hmLow
      have hvTheta :
          rayThetaAt hp W.b v =
            rayThetaAt hp W.b kc := by
        dsimp [v]
        simpa [CentreProjectiveCycle.angles] using hmHigh
      have huSign :
          raySignAt hp W.b u =
            raySignAt hp W.b ja :=
        raySignAt_eq_of_rayThetaAt_eq
          hp hcap htpos hlam W.b u ja huTheta
      have hvSign :
          raySignAt hp W.b v =
            raySignAt hp W.b kc :=
        raySignAt_eq_of_rayThetaAt_eq
          hp hcap htpos hlam W.b v kc hvTheta
      have hsign :
          raySignAt hp W.b u ≠
            raySignAt hp W.b v := by
        rw [huSign, hvSign]
        exact exactWitness_ordinary_short_endpoint_sign_ne
          hp hn hdelta0 ht hlam W horder
          (by simpa [ja, kc] using hord)
      refine Or.inl ⟨m, hmRays, ?_, hsign⟩
      rw [huTheta, hvTheta]
      dsimp [ja, kc] at hord
      rw [hord, hscale]
    · right
      obtain ⟨first, rest, hrays⟩ :
          ∃ first rest, C.rays = first :: rest := by
        cases hR : C.rays with
        | nil => exact False.elim (C.nonempty hR)
        | cons first rest => exact ⟨first, rest, hR⟩
      have hsorted :
          (first :: rest).Pairwise
            (fun x y =>
              rayThetaAt hp W.b x ≤
                rayThetaAt hp W.b y) := by
        simpa [hrays] using C.theta_sorted
      have hjaMem : ja ∈ first :: rest := by
        simpa [hrays] using C.mem_rays_iff ja
      have hkcMem : kc ∈ first :: rest := by
        simpa [hrays] using C.mem_rays_iff kc
      have hfirstLeA :
          rayThetaAt hp W.b first ≤
            rayThetaAt hp W.b ja := by
        rcases hjaMem with rfl | htail
        · rfl
        · exact (List.pairwise_cons.mp hsorted).1 ja htail
      have hfirstGeA :
          rayThetaAt hp W.b ja ≤
            rayThetaAt hp W.b first := by
        by_contra hnot
        have hlt :
            rayThetaAt hp W.b first <
              rayThetaAt hp W.b ja :=
          lt_of_not_ge hnot
        exact no_ray_strictly_inside_exactWitness_wrap_short_arc
          hp hcap hn hdelta0 ht hlam W first horder
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
        simpa [last] using hsorted.rel_getLast hkcMem
      have hlastLeK :
          rayThetaAt hp W.b last ≤
            rayThetaAt hp W.b kc := by
        by_contra hnot
        have hlt :
            rayThetaAt hp W.b kc <
              rayThetaAt hp W.b last :=
          lt_of_not_ge hnot
        exact no_ray_strictly_inside_exactWitness_wrap_short_arc
          hp hcap hn hdelta0 ht hlam W last horder
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
        | nil => simp
        | cons r rs => simp [List.getLastD_cons]
      have hfirstSign :
          raySignAt hp W.b first =
            raySignAt hp W.b ja :=
        raySignAt_eq_of_rayThetaAt_eq
          hp hcap htpos hlam W.b first ja hfirstEq
      have hlastSign :
          raySignAt hp W.b last =
            raySignAt hp W.b kc :=
        raySignAt_eq_of_rayThetaAt_eq
          hp hcap htpos hlam W.b last kc hlastEq
      have hsign :
          raySignAt hp W.b (rest.getLastD first) ≠
            !raySignAt hp W.b first := by
        rw [hlastD, hlastSign, hfirstSign]
        exact exactWitness_wrap_short_endpoint_lifted_sign_ne
          hp hn hdelta0 ht hlam W horder
          (by simpa [ja, kc] using hwrap)
      refine Or.inr ⟨first, rest, hrays, ?_, hsign⟩
      rw [hlastD, hfirstEq, hlastEq]
      dsimp [ja, kc] at hwrap
      rw [hwrap, hscale]
  · have hrev :
        rayThetaAt hp W.b kc ≤
          rayThetaAt hp W.b ja :=
      le_of_not_ge horder
    have hswap :=
      exactWitness_unit_transition_gap_position
        hp hcap hn hdelta0 ht hlam W.swapEnds C
    simpa [ExactAngleWitness.swapEnds, ja, kc] using hswap

#print axioms exactWitness_unit_transition_gap_position

end JSP000404Research
