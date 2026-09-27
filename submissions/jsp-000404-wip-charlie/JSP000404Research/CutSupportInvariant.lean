import JSP000404Research.CutLocalBandCycle
import JSP000404Research.ListCyclicSupportBridge
import JSP000404Research.CyclicEdgeRotation
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Positive-support invariance for an arbitrary projective cut

CutLocalBandCycle already proves that the floor-excess exponent of a cut-sorted
centre cycle is canonical.  Here we retain the stronger list statement.

For the canonical ray split

  C.rays = low ++ high

at a projective cut c, the cut-sorted rays are

  high ++ low,

and their unwrapped cut angles are exactly

  anglesAfterProjectiveCut c lowAngles highAngles.

Changing the projective cut only cyclically rotates the projective-gap list.
After Sendov scaling and flooring, the entire quotient list is therefore a
rotation of the canonical quotient list.

Consequently its positive-support count is exactly the canonical
positiveSupport(centreQuotient C t), not merely bounded by three.
-/

namespace JSP000404Research
namespace CentreCutRayCycle

open Real

/-- The full arbitrary-cut quotient list is a cyclic rotation of the canonical
centre quotient list. -/
theorem exists_gapQuotients_rotation
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t) :
    ∃ k : ℕ,
      R.gapQuotients t =
        (quotientList t C.gaps).rotate k := by
  obtain ⟨low, high, hdecomp, hlow, hhigh⟩ :=
    exists_ray_split_at_cut hp C.rays C.theta_sorted c

  let explicitRays : List (OtherVertex i) := high ++ low
  let explicitValues : List ℝ :=
    explicitRays.map (cutNormalizedRayTheta hp t c i)

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

  have hexplicitSortedRays :
      explicitRays.Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b) := by
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

  let lowAngles : List ℝ :=
    low.map (rayThetaAt hp i)
  let highAngles : List ℝ :=
    high.map (rayThetaAt hp i)
  let cutAngles : List ℝ :=
    anglesAfterProjectiveCut c lowAngles highAngles

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

  have hqCut :
      R.gapQuotients t =
        quotientList t
          (normalizedProjectiveGaps cutAngles) := by
    unfold CentreCutRayCycle.gapQuotients
    rw [hvaluesEq, hexplicit]
    cases hca : cutAngles with
    | nil =>
        exact False.elim (hcutNe hca)
    | cons a as =>
        rw [linearCyclicGapQuotients_eq_floor_cyclicGapsAt]
        simpa [hca] using
          floor_scaled_cyclicGaps_eq_quotientList t a as

  have hangleDecomp :
      lowAngles ++ highAngles = C.angles := by
    dsimp [lowAngles, highAngles]
    rw [← List.map_append, ← hdecomp]
    rfl

  have hgapRot :
      ∃ k : ℕ,
        normalizedProjectiveGaps cutAngles =
          C.gaps.rotate k := by
    cases hlowList : lowAngles with
    | nil =>
        cases hhighList : highAngles with
        | nil =>
            have hcutNil : cutAngles = [] := by
              dsimp [cutAngles]
              rw [hlowList, hhighList]
              rfl
            exact False.elim (hcutNe hcutNil)
        | cons b bs =>
            refine ⟨0, ?_⟩
            unfold CentreProjectiveCycle.gaps
            dsimp [cutAngles]
            rw [hlowList, hhighList]
            simp only [anglesAfterProjectiveCut,
              List.map_nil, List.nil_append, List.nil_append,
              List.rotate_zero]
            have htrans :=
              normalizedProjectiveGaps_map_add
                b (-c) bs
            have hcanon :
                C.angles = b :: bs := by
              rw [← hangleDecomp, hlowList, hhighList]
              rfl
            rw [hcanon]
            simpa [sub_eq_add_neg] using htrans
    | cons a as =>
        cases hhighList : highAngles with
        | nil =>
            refine ⟨0, ?_⟩
            unfold CentreProjectiveCycle.gaps
            dsimp [cutAngles]
            rw [hlowList, hhighList]
            simp only [anglesAfterProjectiveCut,
              List.map_nil, List.nil_append, List.append_nil,
              List.rotate_zero]
            have htrans :=
              normalizedProjectiveGaps_map_add
                a (Real.pi - c) as
            have hcanon :
                C.angles = a :: as := by
              rw [← hangleDecomp, hlowList, hhighList]
              rfl
            rw [hcanon]
            simpa [sub_eq_add_neg, add_assoc] using htrans
        | cons b bs =>
            refine ⟨(a :: as).length, ?_⟩
            unfold CentreProjectiveCycle.gaps
            dsimp [cutAngles]
            rw [hlowList, hhighList]
            have hrot :=
              normalizedProjectiveGaps_after_cut_eq_rotate
                c a b as bs
            have hcanon :
                C.angles =
                  (a :: as) ++ (b :: bs) := by
              rw [← hangleDecomp, hlowList, hhighList]
            rw [hcanon]
            exact hrot

  obtain ⟨k, hk⟩ := hgapRot
  refine ⟨k, ?_⟩
  rw [hqCut, hk, quotientList_rotate]

/-- Positive support is fully cut-invariant. -/
theorem gapQuotients_positiveCount_eq_canonical
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t) :
    listPositiveCount (R.gapQuotients t) =
      positiveSupport (centreQuotient C t) := by
  obtain ⟨k, hk⟩ :=
    R.exists_gapQuotients_rotation hp ht
  rw [hk, listPositiveCount_rotate]
  exact listPositiveCount_centreQuotientList C t

#print axioms CentreCutRayCycle.exists_gapQuotients_rotation
#print axioms CentreCutRayCycle.gapQuotients_positiveCount_eq_canonical

end CentreCutRayCycle
end JSP000404Research
