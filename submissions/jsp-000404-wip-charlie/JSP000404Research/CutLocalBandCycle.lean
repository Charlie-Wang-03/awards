import JSP000404Research.CutCentreRayCycle
import JSP000404Research.CutProjectiveBandOccupancy
import JSP000404Research.ProjectiveGapScaling
import JSP000404Research.ProjectiveCutRotation
import JSP000404Research.LinearSaturatedEndpointDichotomy
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# One-dimensional local band cycle at an arbitrary projective cut

For a CentreCutRayCycle R at cut c, record the normalized cut coordinates

  x_j = t * cutRayTheta(c,j) / pi.

The list is sorted, lies in [0,t), and enumerates the same finite rays as the
canonical centre cycle.

Its cyclic floor-gap exponent is exactly the canonical centreExponent.  The
proof compares R with the explicit high++low cut rotation of the canonical
ray list.  Both normalized value lists are sorted permutations, hence equal.
For the explicit rotation, ProjectiveCutRotation and ProjectiveGapScaling
identify the cyclic quotient exponent with the canonical quotient exponent.

Thus arbitrary-cut local saturation can be studied directly with the pure
LinearBandGapEquality / SaturatedWrapDescent machinery.
-/

namespace JSP000404Research

namespace CentreCutRayCycle

def normalizedValues
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (t : ℝ) : List ℝ :=
  R.rays.map (cutNormalizedRayTheta hp t c i)

def gapQuotients
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (t : ℝ) : List ℕ :=
  linearCyclicGapQuotients t (R.normalizedValues t)

def exponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (t : ℝ) : ℕ :=
  listExponent (R.gapQuotients t)

theorem normalizedValues_nonempty
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (t : ℝ) :
    R.normalizedValues t ≠ [] := by
  simp [normalizedValues, R.nonempty]

theorem normalizedValues_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht0 : 0 ≤ t) :
    (R.normalizedValues t).Pairwise (· ≤ ·) := by
  unfold normalizedValues
  rw [List.pairwise_map]
  intro a ha b hb hab
  unfold cutNormalizedRayTheta
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiv :=
    div_le_div_of_nonneg_right hab hpi.le
  exact mul_le_mul_of_nonneg_left hdiv ht0

theorem normalizedValues_mem_bounds
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {x : ℝ}
    (hx : x ∈ R.normalizedValues t) :
    0 ≤ x ∧ x < t := by
  unfold normalizedValues at hx
  obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hx
  exact ⟨
    cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi i j,
    cutNormalizedRayTheta_lt_t hp ht hc0 hcpi i j⟩

/-- R and C enumerate the same rays. -/
theorem rays_perm_canonical
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c) :
    R.rays.Perm C.rays := by
  obtain ⟨k, hk⟩ := R.rotation
  rw [hk]
  exact List.rotate_perm C.rays k

/-- The natural floor set of the cut-sorted values is the same occupied cut
band set used by cutProjectiveBandPartition. -/
theorem occupiedNatBands_normalizedValues_card_eq_occupiedCut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    (occupiedNatBands (R.normalizedValues t)).card =
      (occupiedCutProjectiveBands hp t c n i).card := by
  classical
  have hpermRay := R.rays_perm_canonical
  have hpermFloor :
      (R.normalizedValues t).map Nat.floor
        ~
      cutFloorBandList C t c := by
    unfold normalizedValues cutFloorBandList
    simpa [List.map_map, Function.comp_def] using
      hpermRay.map
        (fun j : OtherVertex i =>
          Nat.floor (cutNormalizedRayTheta hp t c i j))
  have hfin :
      (R.normalizedValues t).map Nat.floor |>.toFinset =
        (cutFloorBandList C t c).toFinset := by
    ext m
    exact hpermFloor.mem_iff
  unfold occupiedNatBands
  rw [hfin,
      cutFloorBandList_toFinset_card_eq_occupied
        hp C ht hc0 hcpi n htop]

/-- Floor of scaled cyclic real gaps is exactly linearCyclicGapQuotients. -/
theorem linearCyclicGapQuotients_eq_floor_cyclicGapsAt
    (t : ℝ) (xs : List ℝ) :
    linearCyclicGapQuotients t xs =
      (cyclicGapsAt t xs).map Nat.floor := by
  cases xs with
  | nil =>
      rfl
  | cons a as =>
      simp [linearCyclicGapQuotients, cyclicGapsAt]

/-- The explicit canonical high++low cut rotation has exactly the
anglesAfterProjectiveCut normalized value list. -/
theorem normalizedValues_explicit_cut_rotation
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (low high : List (OtherVertex i))
    (hlow : ∀ j ∈ low, rayThetaAt hp i j < c)
    (hhigh : ∀ j ∈ high, c ≤ rayThetaAt hp i j) :
    (high ++ low).map
        (cutNormalizedRayTheta hp t c i)
      =
    (anglesAfterProjectiveCut c
        (low.map (rayThetaAt hp i))
        (high.map (rayThetaAt hp i))).map
      (scaleProjectiveAngle t) := by
  unfold anglesAfterProjectiveCut
  simp only [List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro j hj
    rw [cutRayTheta_eq_sub_of_ge hp (hhigh j hj)]
    rfl
  · apply List.map_congr_left
    intro j hj
    rw [cutRayTheta_eq_add_pi_sub_of_lt hp (hlow j hj)]
    rfl

/-- Main list-exponent invariance at an arbitrary cut-sorted centre cycle. -/
theorem exponent_eq_centreExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t) :
    R.exponent t = centreExponent C t := by
  obtain ⟨low, high, hdecomp, hlow, hhigh⟩ :=
    exists_ray_split_at_cut hp C.rays C.theta_sorted c
  let explicitRays := high ++ low
  let explicitValues :=
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

  let lowAngles := low.map (rayThetaAt hp i)
  let highAngles := high.map (rayThetaAt hp i)
  let cutAngles :=
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

  have hcutExponent :
      listExponent
          (linearCyclicGapQuotients t
            (cutAngles.map (scaleProjectiveAngle t)))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps cutAngles)) := by
    obtain ⟨a, as, hcut⟩ :
        ∃ a as, cutAngles = a :: as := by
      cases h : cutAngles with
      | nil => exact False.elim (hcutNe h)
      | cons a as => exact ⟨a, as, h⟩
    rw [hcut]
    rw [linearCyclicGapQuotients_eq_floor_cyclicGapsAt]
    rw [floor_scaled_cyclicGaps_eq_quotientList]

  have hangleDecomp :
      lowAngles ++ highAngles = C.angles := by
    dsimp [lowAngles, highAngles]
    rw [← List.map_append, ← hdecomp]
    rfl

  have hcutInvariant :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps cutAngles))
        =
      listExponent (quotientList t C.gaps) := by
    dsimp [cutAngles]
    rw [listExponent_after_projective_cut_any]
    rw [hangleDecomp]
    rfl

  unfold CentreCutRayCycle.exponent
    CentreCutRayCycle.gapQuotients
  rw [hvaluesEq, hexplicit, hcutExponent, hcutInvariant]
  exact listExponent_quotientList_eq_centreExponent' C t

#print axioms CentreCutRayCycle.normalizedValues_pairwise
#print axioms CentreCutRayCycle.occupiedNatBands_normalizedValues_card_eq_occupiedCut
#print axioms CentreCutRayCycle.exponent_eq_centreExponent

end CentreCutRayCycle
end JSP000404Research
