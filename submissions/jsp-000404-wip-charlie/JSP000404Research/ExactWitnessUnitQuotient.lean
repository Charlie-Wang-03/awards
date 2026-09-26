
import JSP000404Research.ExactWitnessShortArc
import JSP000404Research.CentreAdjacentDirectionBoundary
import JSP000404Research.AdjacentProjectiveGapIndex
import Mathlib.Tactic

/-!
# Exact maximum-angle witnesses force a unit quotient at the witness centre

For an exact witness W=(a,b,c) in the n>=3 Sendov range, the short projective
arc between rays b--a and b--c has width exactly lambda=pi/t and contains no
strictly intermediate ray direction.

If the short arc does not cross the canonical 0/pi cut, the empty-interval
boundary theorem produces an adjacent gap of width lambda.

If it crosses the cut, short-arc emptiness forces the first sorted ray
direction to equal the low endpoint and the last sorted ray direction to equal
the high endpoint, so the cyclic wrap gap has width lambda.

In both cases its scaled width is exactly one, hence the natural quotient list
at the exact-witness centre contains quotient 1.
-/

namespace JSP000404Research

open Real

theorem map_getLastD_eq_getLast_map
    {α β : Type*}
    (f : α → β)
    (a : α) (xs : List α) :
    (xs.map f).getLastD (f a) =
      f ((a :: xs).getLast (by simp)) := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp
      | cons y ys =>
          simp [List.getLastD_cons, ih]

/-- Ordered endpoint form. -/
theorem one_mem_witnessCentre_quotientList_of_ordered
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
    1 ∈ quotientList t C.gaps := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlamPos : 0 < lam := by
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
          ¬ (rayThetaAt hp W.b ja < rayThetaAt hp W.b x ∧
             rayThetaAt hp W.b x < rayThetaAt hp W.b kc) := by
      intro x hins
      exact no_ray_strictly_inside_exactWitness_ordinary_short_arc
        hp hcap hn hdelta0 ht hlam W x
        (by simpa [ja, kc] using hins.1)
        (by simpa [ja, kc] using hins.2)
        hordinary
    exact C.one_mem_quotientList_of_empty_exact_interval
      t hjk
      (by simpa [ja, kc] using hordinary)
      hscale hno
  · obtain ⟨first, rest, hrays⟩ :
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
        hwrap
    have hlastEq :
        rayThetaAt hp W.b last =
          rayThetaAt hp W.b kc :=
      le_antisymm hlastLeK hkcLeLast
    have hangles :
        C.angles =
          rayThetaAt hp W.b first ::
            rest.map (rayThetaAt hp W.b) := by
      simp [CentreProjectiveCycle.angles, hrays]
    have hlastMap :
        (rest.map (rayThetaAt hp W.b)).getLastD
            (rayThetaAt hp W.b first)
          =
        rayThetaAt hp W.b last := by
      simpa [last] using
        map_getLastD_eq_getLast_map
          (rayThetaAt hp W.b) first rest
    have hmem :=
      centre_wrap_quotient_mem
        C t (rayThetaAt hp W.b first)
        (rest.map (rayThetaAt hp W.b)) hangles
    have hfloor :
        Nat.floor
          (t * ((rayThetaAt hp W.b first + Real.pi -
            (rest.map (rayThetaAt hp W.b)).getLastD
              (rayThetaAt hp W.b first)) / Real.pi))
          = 1 := by
      rw [hlastMap, hfirstEq, hlastEq]
      dsimp [ja, kc] at hwrap
      rw [hwrap, hscale]
      norm_num
    rw [hfloor] at hmem
    exact hmem

/-- Cut-independent exact-witness unit quotient theorem. -/
theorem one_mem_witnessCentre_quotientList
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
    1 ∈ quotientList t C.gaps := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  by_cases horder :
      rayThetaAt hp W.b ja ≤ rayThetaAt hp W.b kc
  · exact one_mem_witnessCentre_quotientList_of_ordered
      hp hcap hn hdelta0 ht hlam W C horder
  · have hrev :
        rayThetaAt hp W.b kc ≤ rayThetaAt hp W.b ja :=
      le_of_not_ge horder
    have hswap :
        one_mem_witnessCentre_quotientList_of_ordered
          hp hcap hn hdelta0 ht hlam W.swapEnds C
          (by simpa [ExactAngleWitness.swapEnds, ja, kc] using hrev) :=
      one_mem_witnessCentre_quotientList_of_ordered
        hp hcap hn hdelta0 ht hlam W.swapEnds C
        (by simpa [ExactAngleWitness.swapEnds, ja, kc] using hrev)
    simpa [ExactAngleWitness.swapEnds] using hswap

#print axioms ExactAngleWitness.swapEnds
#print axioms one_mem_witnessCentre_quotientList_of_ordered
#print axioms one_mem_witnessCentre_quotientList

end JSP000404Research
