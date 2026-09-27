import JSP000404Research.CutLocalBandCycle
import JSP000404Research.ProjectiveCutRotation
import JSP000404Research.ProjectiveGapScaling
import JSP000404Research.CyclicGapRotationInvariant
import Mathlib.Tactic

/-!
# Full quotient-list invariance under an arbitrary projective cut

CutLocalBandCycle already proves exponent and positive-support invariance.
For mixed-support terminals we need the stronger statement: the entire
cut-sorted quotient list is a cyclic permutation of the canonical quotient
list.

The proof follows the same explicit low/high split as exponent invariance.

* If both blocks are nonempty, ProjectiveCutRotation gives an exact rotation
  of normalized projective gaps, hence of quotient lists.
* If one block is empty, the cut only translates every projective angle by a
  common real number, so cyclic gaps and quotient lists are unchanged.

This lets canonical transition certificates be transported into arbitrary-cut
quotient arithmetic by simple List.Perm membership.
-/

namespace JSP000404Research
namespace CentreCutRayCycle

/-- Quotient list of an explicit projective-cut angle list is a permutation of
the original quotient list, including empty-side degenerate cuts. -/
theorem quotientList_anglesAfterProjectiveCut_perm
    (t c : ℝ)
    (low high : List ℝ) :
    quotientList t
        (normalizedProjectiveGaps
          (anglesAfterProjectiveCut c low high))
      ~
    quotientList t
        (normalizedProjectiveGaps (low ++ high)) := by
  cases low with
  | nil =>
      cases high with
      | nil =>
          simp [anglesAfterProjectiveCut,
            normalizedProjectiveGaps, projectiveGaps,
            quotientList]
      | cons b bs =>
          have hgaps :
              normalizedProjectiveGaps
                  (anglesAfterProjectiveCut c [] (b :: bs))
                =
              normalizedProjectiveGaps (b :: bs) := by
            simp only [anglesAfterProjectiveCut,
              List.map_nil, List.nil_append,
              List.nil_append]
            simpa [sub_eq_add_neg] using
              normalizedProjectiveGaps_map_add b (-c) bs
          rw [hgaps]
  | cons a as =>
      cases high with
      | nil =>
          have hgaps :
              normalizedProjectiveGaps
                  (anglesAfterProjectiveCut c (a :: as) [])
                =
              normalizedProjectiveGaps (a :: as) := by
            simp only [anglesAfterProjectiveCut,
              List.map_nil, List.nil_append,
              List.append_nil]
            have h :=
              normalizedProjectiveGaps_map_add
                a (Real.pi - c) as
            simpa [sub_eq_add_neg, add_assoc] using h
          rw [hgaps]
      | cons b bs =>
          have hrot :=
            normalizedProjectiveGaps_after_cut_eq_rotate
              c a b as bs
          rw [hrot, quotientList_rotate]
          exact List.rotate_perm _ _

/-- The quotient list obtained from the cut-normalized real coordinates is a
permutation of the canonical centre quotient list. -/
theorem gapQuotients_perm_canonical
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t) :
    R.gapQuotients t ~ quotientList t C.gaps := by
  obtain ⟨low, high, hdecomp, hlow, hhigh⟩ :=
    exists_ray_split_at_cut hp C.rays C.theta_sorted c

  let explicitRays := high ++ low
  let explicitValues :=
    explicitRays.map (cutNormalizedRayTheta hp t c i)
  let lowAngles := low.map (rayThetaAt hp i)
  let highAngles := high.map (rayThetaAt hp i)
  let cutAngles :=
    anglesAfterProjectiveCut c lowAngles highAngles

  have hpermRays :
      R.rays.Perm explicitRays := by
    have hRC := R.rays_perm_canonical
    have hCE : C.rays.Perm explicitRays := by
      rw [hdecomp]
      exact List.Perm.append_comm low high
    exact hRC.trans hCE

  have hpermValues :
      (R.normalizedValues t).Perm explicitValues := by
    unfold normalizedValues explicitValues
    exact hpermRays.map (cutNormalizedRayTheta hp t c i)

  have hexplicitSorted :
      explicitRays.Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b) := by
    have hcanonPair :
        low.Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b)
        ∧
        high.Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
      have hpair :
          (low ++ high).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        rw [← hdecomp]
        exact C.theta_sorted
      have hh := List.pairwise_append.mp hpair
      exact ⟨hh.1, hh.2.1⟩
    have hhighPair :=
      pairwise_cutRayTheta_of_all_ge_cut
        hp c high hcanonPair.2 hhigh
    have hlowPair :=
      pairwise_cutRayTheta_of_all_lt_cut
        hp c low hcanonPair.1 hlow
    have hcross :
        ∀ a ∈ high, ∀ b ∈ low,
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b := by
      intro a ha b hb
      rw [cutRayTheta_eq_sub_of_ge hp (hhigh a ha),
          cutRayTheta_eq_add_pi_sub_of_lt hp (hlow b hb)]
      have haPi := rayThetaAt_lt_pi hp i a
      have hb0 := rayThetaAt_nonneg hp i b
      linarith
    dsimp [explicitRays]
    exact List.pairwise_append.mpr
      ⟨hhighPair, hlowPair, hcross⟩

  have hRSorted :
      (R.normalizedValues t).Pairwise (· ≤ ·) :=
    R.normalizedValues_pairwise ht.le
  have hESorted :
      explicitValues.Pairwise (· ≤ ·) := by
    unfold explicitValues
    rw [List.pairwise_map]
    intro a ha b hb hab
    unfold cutNormalizedRayTheta
    have hdiv :=
      div_le_div_of_nonneg_right hab Real.pi_pos.le
    exact mul_le_mul_of_nonneg_left hdiv ht.le

  have hvaluesEq :
      R.normalizedValues t = explicitValues := by
    exact List.Perm.eq_of_pairwise
      (fun a b _ha _hb hab hba => le_antisymm hab hba)
      hRSorted hESorted hpermValues

  have hexplicit :
      explicitValues =
        cutAngles.map (scaleProjectiveAngle t) := by
    dsimp [explicitValues, explicitRays, cutAngles,
      lowAngles, highAngles]
    exact normalizedValues_explicit_cut_rotation
      hp low high hlow hhigh

  have hcutNe : cutAngles ≠ [] := by
    intro hnil
    have hlen0 :
        explicitValues.length = 0 := by
      rw [hexplicit, hnil]
      rfl
    have hlenR :
        (R.normalizedValues t).length = 0 := by
      rw [hvaluesEq, hlen0]
    exact R.normalizedValues_nonempty t
      (List.length_eq_zero.mp hlenR)

  have hcutQuot :
      linearCyclicGapQuotients t
          (cutAngles.map (scaleProjectiveAngle t))
        =
      quotientList t
          (normalizedProjectiveGaps cutAngles) := by
    obtain ⟨a, as, hcut⟩ :
        ∃ a as, cutAngles = a :: as := by
      cases h : cutAngles with
      | nil => exact False.elim (hcutNe h)
      | cons a as => exact ⟨a, as, h⟩
    rw [hcut]
    rw [linearCyclicGapQuotients_eq_floor_cyclicGapsAt]
    exact floor_scaled_cyclicGaps_eq_quotientList t a as

  have hangleDecomp :
      lowAngles ++ highAngles = C.angles := by
    dsimp [lowAngles, highAngles]
    rw [← List.map_append, ← hdecomp]
    rfl

  have hpermCut :
      quotientList t
          (normalizedProjectiveGaps cutAngles)
        ~
      quotientList t C.gaps := by
    have h :=
      quotientList_anglesAfterProjectiveCut_perm
        t c lowAngles highAngles
    dsimp [cutAngles] at h
    rw [hangleDecomp] at h
    simpa [CentreProjectiveCycle.gaps] using h

  unfold CentreCutRayCycle.gapQuotients
  rw [hvaluesEq, hexplicit, hcutQuot]
  exact hpermCut

/-- Membership form convenient for transporting canonical transition
certificate quotients into cut-local arithmetic. -/
theorem canonical_quotient_mem_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t)
    {q : ℕ}
    (hq : q ∈ quotientList t C.gaps) :
    q ∈ R.gapQuotients t := by
  exact (R.gapQuotients_perm_canonical hp ht).mem_iff.mpr hq

#print axioms quotientList_anglesAfterProjectiveCut_perm
#print axioms CentreCutRayCycle.gapQuotients_perm_canonical
#print axioms CentreCutRayCycle.canonical_quotient_mem_cut

end CentreCutRayCycle
end JSP000404Research
