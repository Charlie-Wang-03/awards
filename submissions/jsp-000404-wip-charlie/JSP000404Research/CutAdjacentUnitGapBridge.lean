import JSP000404Research.CutCentreTransitionRefinement
import JSP000404Research.CyclicTransitionUnitGapBridge
import JSP000404Research.CentreAdjacentDirectionBoundary
import JSP000404Research.CriticalUnitQuotient
import Mathlib.Tactic

/-!
# Returning a cut-adjacent critical gap to a canonical cyclic q=1 slot

A CentreCutRayCycle is only a cyclic rotation of the canonical centre ray
cycle.  Hence two adjacent rays in the cut order determine either

* an ordinary canonical direction gap, or
* the canonical wrap gap.

This file avoids brittle rotate-index arithmetic.  Instead, cut adjacency
gives a no-intermediate-ray statement.  In the ordinary canonical-order
branch, CentreAdjacentDirectionBoundary reconstructs the corresponding
ordinary adjacent gap.  In the reversed canonical-order branch, the same
no-intermediate statement forces the endpoints to be the maximal and minimal
canonical direction classes, so the gap is the final wrap coordinate.

Therefore every cut-adjacent critical gap of normalized size in [1,1+delta],
with delta<1/2, produces a genuine CentreUnitGap in the canonical cyclic
quotient list.
-/

namespace JSP000404Research

open Real

theorem exists_centreUnitGap_of_adjacent_cut_critical
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    {t delta : ℝ}
    (ht : 0 < t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {q r : Fin R.rays.length}
    (hsucc : r.val = q.val + 1)
    (hs1 :
      1 ≤
        t * ((cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)) / Real.pi))
    (hsTop :
      t * ((cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)) / Real.pi)
        ≤ 1 + delta) :
    ∃ u : CentreUnitGap C t, ∃ k : ℤ,
      centreUnitGapStart C t u + (k : ℝ) * t =
        t * c / Real.pi +
          cutNormalizedRayTheta hp t c i (R.rays.get q) := by
  let a : OtherVertex i := R.rays.get q
  let b : OtherVertex i := R.rays.get r
  have hfloorCut :
      Nat.floor
        (t * ((cutRayTheta hp c i b -
          cutRayTheta hp c i a) / Real.pi)) = 1 := by
    exact critical_gap_floor_eq_one
      hdeltaHalf hs1 hsTop

  have hdiffPos :
      0 < cutRayTheta hp c i b -
        cutRayTheta hp c i a := by
    by_contra hnot
    have hdiffNonpos :
        cutRayTheta hp c i b -
            cutRayTheta hp c i a ≤ 0 :=
      le_of_not_gt hnot
    have hdivNonpos :
        (cutRayTheta hp c i b -
            cutRayTheta hp c i a) / Real.pi ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        hdiffNonpos Real.pi_pos.le
    have hmulNonpos :
        t * ((cutRayTheta hp c i b -
            cutRayTheta hp c i a) / Real.pi) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht.le hdivNonpos
    linarith
  have hcutStrict :
      cutRayTheta hp c i a <
        cutRayTheta hp c i b := by
    linarith

  have hnoCut :
      ∀ x : OtherVertex i,
        ¬ (cutRayTheta hp c i a <
              cutRayTheta hp c i x ∧
           cutRayTheta hp c i x <
              cutRayTheta hp c i b) := by
    simpa [a, b] using
      R.no_cutTheta_strict_between_adjacent hsucc

  have hthetaNe :
      rayThetaAt hp i a ≠ rayThetaAt hp i b := by
    intro heq
    have hcutEq :
        cutRayTheta hp c i a =
          cutRayTheta hp c i b := by
      unfold cutRayTheta
      rw [heq]
    exact (ne_of_lt hcutStrict) hcutEq

  rcases lt_or_gt_of_ne hthetaNe with hab | hba
  · -- Ordinary canonical-order branch.
    have hside :
        (rayThetaAt hp i a < c ∧
          rayThetaAt hp i b < c) ∨
        (c ≤ rayThetaAt hp i a ∧
          c ≤ rayThetaAt hp i b) := by
      by_cases ha : rayThetaAt hp i a < c
      · have hb : rayThetaAt hp i b < c := by
          by_contra hnot
          have hcb : c ≤ rayThetaAt hp i b :=
            le_of_not_gt hnot
          have hbPi := rayThetaAt_lt_pi hp i b
          have ha0 := rayThetaAt_nonneg hp i a
          have hrev :
              cutRayTheta hp c i b <
                cutRayTheta hp c i a := by
            rw [cutRayTheta_eq_sub_of_ge hp hcb,
                cutRayTheta_eq_add_pi_sub_of_lt hp ha]
            linarith
          exact (not_lt_of_ge hcutStrict.le) hrev
        exact Or.inl ⟨ha, hb⟩
      · have hca : c ≤ rayThetaAt hp i a :=
          le_of_not_gt ha
        exact Or.inr ⟨hca, hca.trans hab.le⟩

    have hgapEq :
        cutRayTheta hp c i b -
            cutRayTheta hp c i a
          =
        rayThetaAt hp i b -
            rayThetaAt hp i a := by
      rcases hside with hlow | hhigh
      · rw [cutRayTheta_eq_add_pi_sub_of_lt hp hlow.1,
            cutRayTheta_eq_add_pi_sub_of_lt hp hlow.2]
        ring
      · rw [cutRayTheta_eq_sub_of_ge hp hhigh.1,
            cutRayTheta_eq_sub_of_ge hp hhigh.2]
        ring

    have hnoCanonical :
        ∀ x : OtherVertex i,
          ¬ (rayThetaAt hp i a <
                rayThetaAt hp i x ∧
             rayThetaAt hp i x <
                rayThetaAt hp i b) := by
      intro x hx
      apply hnoCut x
      rcases hside with hlow | hhigh
      · have hxLow : rayThetaAt hp i x < c :=
          hx.2.trans hlow.2
        rw [cutRayTheta_eq_add_pi_sub_of_lt hp hlow.1,
            cutRayTheta_eq_add_pi_sub_of_lt hp hxLow,
            cutRayTheta_eq_add_pi_sub_of_lt hp hlow.2]
        constructor <;> linarith
      · have hxHigh : c ≤ rayThetaAt hp i x :=
          hhigh.1.trans hx.1.le
        rw [cutRayTheta_eq_sub_of_ge hp hhigh.1,
            cutRayTheta_eq_sub_of_ge hp hxHigh,
            cutRayTheta_eq_sub_of_ge hp hhigh.2]
        constructor <;> linarith

    obtain ⟨m, hm, hmLow, hmHigh⟩ :=
      C.exists_adjacent_angles_of_no_strict_between
        hab hnoCanonical
    have hmRays : m + 1 < C.rays.length := by
      simpa [C.angles_length] using hm
    have hfloor :
        Nat.floor
          (t * ((rayThetaAt hp i
              (C.rays.get ⟨m + 1, hmRays⟩) -
            rayThetaAt hp i
              (C.rays.get ⟨m, by omega⟩)) / Real.pi)) = 1 := by
      have hangleLow :
          rayThetaAt hp i
              (C.rays.get ⟨m, by omega⟩) =
            rayThetaAt hp i a := by
        simpa [CentreProjectiveCycle.angles] using hmLow
      have hangleHigh :
          rayThetaAt hp i
              (C.rays.get ⟨m + 1, hmRays⟩) =
            rayThetaAt hp i b := by
        simpa [CentreProjectiveCycle.angles] using hmHigh
      rw [hangleLow, hangleHigh, ← hgapEq]
      exact hfloorCut
    obtain ⟨u, hu⟩ :=
      exists_centreUnitGap_of_adjacent_floor_one
        C t m hmRays hfloor
    have hstartTheta :
        rayThetaAt hp i
            (C.rays.get (gapToRayIndex C u.1)) =
          rayThetaAt hp i a := by
      have hidx :
          gapToRayIndex C u.1 =
            (⟨m, by omega⟩ : Fin C.rays.length) := by
        apply Fin.ext
        simpa using hu
      rw [hidx]
      simpa [CentreProjectiveCycle.angles] using hmLow
    have hstart :
        centreUnitGapStart C t u =
          normalizedRayTheta hp t i a := by
      unfold centreUnitGapStart
      rw [hstartTheta]
    obtain ⟨k, hk⟩ :=
      exists_period_shift_eq_cut_lift hp t c i a
    refine ⟨u, k, ?_⟩
    rw [hstart]
    simpa [a] using hk

  · -- Canonical wrap branch: b is the minimal direction class and a the
    -- maximal direction class.
    have haHigh : c ≤ rayThetaAt hp i a := by
      by_contra hnot
      have haLow : rayThetaAt hp i a < c :=
        lt_of_not_ge hnot
      have hbLow : rayThetaAt hp i b < c :=
        hba.trans haLow
      have hrev :
          cutRayTheta hp c i b <
            cutRayTheta hp c i a := by
        rw [cutRayTheta_eq_add_pi_sub_of_lt hp hbLow,
            cutRayTheta_eq_add_pi_sub_of_lt hp haLow]
        linarith
      exact (not_lt_of_ge hcutStrict.le) hrev
    have hbLow : rayThetaAt hp i b < c := by
      by_contra hnot
      have hbHigh : c ≤ rayThetaAt hp i b :=
        le_of_not_gt hnot
      have haHigh' : c ≤ rayThetaAt hp i a :=
        hbHigh.trans hba.le
      have hrev :
          cutRayTheta hp c i b <
            cutRayTheta hp c i a := by
        rw [cutRayTheta_eq_sub_of_ge hp hbHigh,
            cutRayTheta_eq_sub_of_ge hp haHigh']
        linarith
      exact (not_lt_of_ge hcutStrict.le) hrev

    have hgapEq :
        cutRayTheta hp c i b -
            cutRayTheta hp c i a
          =
        rayThetaAt hp i b + Real.pi -
            rayThetaAt hp i a := by
      rw [cutRayTheta_eq_sub_of_ge hp haHigh,
          cutRayTheta_eq_add_pi_sub_of_lt hp hbLow]
      ring

    have hnoAbove :
        ∀ x : OtherVertex i,
          ¬ (rayThetaAt hp i a <
              rayThetaAt hp i x) := by
      intro x hx
      apply hnoCut x
      have hxHigh : c ≤ rayThetaAt hp i x :=
        haHigh.trans hx.le
      rw [cutRayTheta_eq_sub_of_ge hp haHigh,
          cutRayTheta_eq_sub_of_ge hp hxHigh,
          cutRayTheta_eq_add_pi_sub_of_lt hp hbLow]
      have hxPi := rayThetaAt_lt_pi hp i x
      have hb0 := rayThetaAt_nonneg hp i b
      constructor <;> linarith

    have hnoBelow :
        ∀ x : OtherVertex i,
          ¬ (rayThetaAt hp i x <
              rayThetaAt hp i b) := by
      intro x hx
      apply hnoCut x
      have hxLow : rayThetaAt hp i x < c :=
        hx.trans hbLow
      rw [cutRayTheta_eq_sub_of_ge hp haHigh,
          cutRayTheta_eq_add_pi_sub_of_lt hp hxLow,
          cutRayTheta_eq_add_pi_sub_of_lt hp hbLow]
      have haPi := rayThetaAt_lt_pi hp i a
      have hx0 := rayThetaAt_nonneg hp i x
      constructor <;> linarith

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
            rayThetaAt hp i x ≤ rayThetaAt hp i y) := by
      simpa [hrays] using C.theta_sorted

    have hbMem : b ∈ first :: rest := by
      simpa [hrays] using C.mem_rays_iff b
    have hfirstLeB :
        rayThetaAt hp i first ≤ rayThetaAt hp i b := by
      rcases hbMem with rfl | hbTail
      · rfl
      · exact (List.pairwise_cons.mp hsorted).1 b hbTail
    have hbLeFirst :
        rayThetaAt hp i b ≤ rayThetaAt hp i first := by
      by_contra hnot
      have hlt :
          rayThetaAt hp i first <
            rayThetaAt hp i b :=
        lt_of_not_ge hnot
      exact hnoBelow first hlt
    have hfirstEq :
        rayThetaAt hp i first =
          rayThetaAt hp i b :=
      le_antisymm hfirstLeB hbLeFirst

    let last : OtherVertex i :=
      (first :: rest).getLast (by simp)
    have haMem : a ∈ first :: rest := by
      simpa [hrays] using C.mem_rays_iff a
    have haLeLast :
        rayThetaAt hp i a ≤ rayThetaAt hp i last := by
      have h := hsorted.rel_getLast haMem
      simpa [last] using h
    have hlastLeA :
        rayThetaAt hp i last ≤ rayThetaAt hp i a := by
      by_contra hnot
      have hlt :
          rayThetaAt hp i a <
            rayThetaAt hp i last :=
        lt_of_not_ge hnot
      exact hnoAbove last hlt
    have hlastEq :
        rayThetaAt hp i last =
          rayThetaAt hp i a :=
      le_antisymm hlastLeA haLeLast

    have hlastD :
        rest.getLastD first = last := by
      dsimp [last]
      cases rest with
      | nil => simp
      | cons x xs =>
          simp [List.getLastD_cons]

    have hfloorWrap :
        wrapRayQuotient hp i t first
            (rest.getLastD first) = 1 := by
      unfold wrapRayQuotient
      rw [hfirstEq, hlastD, hlastEq, ← hgapEq]
      exact hfloorCut

    obtain ⟨u, hu⟩ :=
      exists_centreUnitGap_of_wrap_floor_one
        C t first rest hrays hfloorWrap
    let g : OtherVertex i :=
      C.rays.get (gapToRayIndex C u.1)
    have hgapVal :
        (gapToRayIndex C u.1).val = rest.length := by
      simpa using hu
    have haIdxLe :
        C.rayIndex a ≤ gapToRayIndex C u.1 := by
      apply Fin.mk_le_mk.mpr
      have hai := (C.rayIndex a).isLt
      rw [hrays] at hai
      simp only [List.length_cons] at hai
      omega
    have haIdxLeG :
        C.rayIndex a ≤ C.rayIndex g := by
      dsimp [g]
      simpa using haIdxLe
    have haLeG :
        rayThetaAt hp i a ≤ rayThetaAt hp i g :=
      C.theta_le_of_rayIndex_le haIdxLeG
    have hgLeA :
        rayThetaAt hp i g ≤ rayThetaAt hp i a := by
      exact le_of_not_gt (hnoAbove g)
    have hgTheta :
        rayThetaAt hp i g = rayThetaAt hp i a :=
      le_antisymm hgLeA haLeG
    have hstart :
        centreUnitGapStart C t u =
          normalizedRayTheta hp t i a := by
      unfold centreUnitGapStart
      change
        normalizedRayTheta hp t i g =
          normalizedRayTheta hp t i a
      rw [hgTheta]
    obtain ⟨k, hk⟩ :=
      exists_period_shift_eq_cut_lift hp t c i a
    refine ⟨u, k, ?_⟩
    rw [hstart]
    simpa [a] using hk

#print axioms exists_centreUnitGap_of_adjacent_cut_critical

end JSP000404Research
