import JSP000404Research.ExactWitnessUnitQuotient
import JSP000404Research.TransitionQuotientOccurrence
import Mathlib.Tactic

/-!
# The exact witness unit quotient is a genuine sign transition

ExactWitnessUnitQuotient proves that the quotient value 1 occurs at the centre
of an exact maximum-angle witness.  Here we retain the positional information.

The empty exact short projective arc is either:

* an ordinary adjacent cut in the sorted ray list, or
* the cyclic wrap cut.

In the ordinary case the witness endpoint canonical signs are opposite.  In
the wrap case the lifted endpoint signs are opposite.  Rays sharing the same
projective theta also share the same canonical sign, so this remains true for
the actual boundary representatives selected from the sorted cycle.

Thus quotient 1 occurs on an actual sign-transition step.
-/

namespace JSP000404Research

open Real

/-- Positional certificate that quotient one is carried by a sign transition
of a concrete centre cycle. -/
def ExactUnitTransitionPosition
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
    Nat.floor
        (t * ((rayThetaAt hp i v -
          rayThetaAt hp i u) / Real.pi)) = 1
      ∧
    raySignAt hp i u ≠ raySignAt hp i v)
  ∨
  (∃ first : OtherVertex i,
    ∃ rest : List (OtherVertex i),
      C.rays = first :: rest
      ∧
      wrapRayQuotient hp i t first
          (rest.getLastD first) = 1
      ∧
      raySignAt hp i (rest.getLastD first) ≠
        !raySignAt hp i first)

/-- Ordered endpoint version. -/
theorem exactWitness_ordered_unit_transition_position
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
    (horder :
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b)
        ≤
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)) :
    ExactUnitTransitionPosition C t := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hscale :
      t * (lam / Real.pi) = 1 := by
    rw [hlam]
    field_simp [ne_of_gt htpos, Real.pi_ne_zero]
  rcases exactWitness_ordered_short_gap_or_wrap_eq_lam
      hp hn hdelta0 ht hlam W horder with hordinary | hwrap
  · left
    have hjk :
        rayThetaAt hp W.b ja <
          rayThetaAt hp W.b kc := by
      dsimp [ja, kc]
      have hlamPos : 0 < lam := by
        rw [hlam]
        exact div_pos Real.pi_pos htpos
      linarith
    have hno :
        ∀ x : OtherVertex W.b,
          ¬ (rayThetaAt hp W.b ja < rayThetaAt hp W.b x ∧
             rayThetaAt hp W.b x < rayThetaAt hp W.b kc) := by
      intro x hins
      exact no_ray_strictly_inside_exactWitness_ordinary_short_arc
        hp hcap hn hdelta0 ht hlam W x
        (by simpa [ja, kc] using hins.1)
        (by simpa [ja, kc] using hins.2)
        (by simpa [ja, kc] using hordinary)
    obtain ⟨m, hmA, hmLow, hmHigh⟩ :=
      C.exists_adjacent_angles_of_no_strict_between
        hjk hno
    have hmR : m + 1 < C.rays.length := by
      simpa [CentreProjectiveCycle.angles_length C] using hmA
    let u : OtherVertex W.b :=
      C.rays.get ⟨m, by omega⟩
    let v : OtherVertex W.b :=
      C.rays.get ⟨m + 1, hmR⟩
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
    have hWitnessSign :
        raySignAt hp W.b ja ≠ raySignAt hp W.b kc := by
      exact exactWitness_ordinary_short_endpoint_sign_ne
        hp hn hdelta0 ht hlam W horder
          (by simpa [ja, kc] using hordinary)
    have huvSign :
        raySignAt hp W.b u ≠ raySignAt hp W.b v := by
      rw [huSign, hvSign]
      exact hWitnessSign
    have hfloor :
        Nat.floor
          (t * ((rayThetaAt hp W.b v -
            rayThetaAt hp W.b u) / Real.pi)) = 1 := by
      rw [huTheta, hvTheta]
      dsimp [ja, kc] at hordinary
      rw [hordinary, hscale]
      norm_num
    exact ⟨m, hmR, hfloor, huvSign⟩
  · right
    obtain ⟨first, rest, hrays⟩ :
        ∃ first rest, C.rays = first :: rest := by
      cases hR : C.rays with
      | nil =>
          exact False.elim (C.nonempty hR)
      | cons first rest =>
          exact ⟨first, rest, hR⟩
    have hsorted :
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
        hwrap
    have hfirstTheta :
        rayThetaAt hp W.b first =
          rayThetaAt hp W.b ja :=
      le_antisymm hfirstLeA hfirstGeA
    let last : OtherVertex W.b :=
      (first :: rest).getLast (by simp)
    have hkcLeLast :
        rayThetaAt hp W.b kc ≤
          rayThetaAt hp W.b last := by
      have h := hsorted.rel_getLast hkcMem
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
        hwrap
    have hlastTheta :
        rayThetaAt hp W.b last =
          rayThetaAt hp W.b kc :=
      le_antisymm hlastLeK hkcLeLast
    have hfirstSign :
        raySignAt hp W.b first =
          raySignAt hp W.b ja :=
      raySignAt_eq_of_rayThetaAt_eq
        hp hcap htpos hlam W.b first ja hfirstTheta
    have hlastSign :
        raySignAt hp W.b last =
          raySignAt hp W.b kc :=
      raySignAt_eq_of_rayThetaAt_eq
        hp hcap htpos hlam W.b last kc hlastTheta
    have hWitnessLift :
        raySignAt hp W.b kc ≠
          !raySignAt hp W.b ja :=
      exactWitness_wrap_short_endpoint_lifted_sign_ne
        hp hn hdelta0 ht hlam W horder
        (by simpa [ja, kc] using hwrap)
    have hLift :
        raySignAt hp W.b last ≠
          !raySignAt hp W.b first := by
      rw [hlastSign, hfirstSign]
      exact hWitnessLift
    have hlastRest :
        rest.getLastD first = last := by
      dsimp [last]
      cases rest with
      | nil =>
          simp
      | cons r rs =>
          simp [List.getLast_cons]
    have hfloor :
        wrapRayQuotient hp W.b t first
            (rest.getLastD first) = 1 := by
      unfold wrapRayQuotient
      rw [hlastRest, hfirstTheta, hlastTheta]
      dsimp [ja, kc] at hwrap
      rw [hwrap, hscale]
      norm_num
    refine ⟨first, rest, hrays, hfloor, ?_⟩
    rw [hlastRest]
    exact hLift

/-- Cut-independent exact witness transition-position theorem. -/
theorem exactWitness_unit_transition_position
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
    ExactUnitTransitionPosition C t := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  by_cases horder :
      rayThetaAt hp W.b ja ≤ rayThetaAt hp W.b kc
  · exact exactWitness_ordered_unit_transition_position
      hp hcap hn hdelta0 ht hlam W C horder
  · have hrev :
        rayThetaAt hp W.b kc ≤
          rayThetaAt hp W.b ja :=
      le_of_not_ge horder
    have hswap :=
      exactWitness_ordered_unit_transition_position
        hp hcap hn hdelta0 ht hlam W.swapEnds C
        (by
          simpa [ExactAngleWitness.swapEnds, ja, kc] using hrev)
    simpa [ExactAngleWitness.swapEnds] using hswap

#print axioms exactWitness_ordered_unit_transition_position
#print axioms exactWitness_unit_transition_position

end JSP000404Research
