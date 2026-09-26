import JSP000404Research.CutProjectiveBandPartition
import JSP000404Research.ShortArcTransition
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Transition lower bounds on an arbitrary projective-cut ray path

After moving the projective cut, every actual ray has the representation

  rho * signedRayDirection (cutRaySign c) (c + cutRayTheta c).

Therefore an adjusted-sign change across two cut-ordered rays is subject to
the same global angle-cap cost as a canonical sign change: it consumes at
least one normalized Sendov unit.

This file packages that pointwise fact and lifts it to arbitrary finite
cut-ordered ray subpaths.  It is the reusable bridge needed before applying
AdjacentTransitionDominator to a short boundary-triangle arc.
-/

namespace JSP000404Research

open Real

/-- A cut-adjusted sign change across two cut-ordered rays costs at least one
normalized unit. -/
theorem one_le_t_mul_cutRay_gap_of_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (horder :
      cutRayTheta hp c i j ≤
        cutRayTheta hp c i k)
    (hsign :
      cutRaySign hp c i j ≠
        cutRaySign hp c i k) :
    1 ≤
      t * ((cutRayTheta hp c i k -
        cutRayTheta hp c i j) / Real.pi) := by
  have hji : j.1 ≠ i := j.2
  have hki : k.1 ≠ i := k.2
  have hjkVal : j.1 ≠ k.1 :=
    otherVertex_val_ne hjk
  have hcapJK :
      EuclideanGeometry.angle (p j.1) (p i) (p k.1)
        ≤ Real.pi - lam :=
    hcap j.1 i k.1 hji hjkVal hki.symm
  change
    InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i)
      ≤ Real.pi - lam at hcapJK
  rw [cutRayRepAt_eq hp c i j,
      cutRayRepAt_eq hp c i k] at hcapJK
  have hspan :
      (c + cutRayTheta hp c i k) -
          (c + cutRayTheta hp c i j)
        ≤ Real.pi := by
    have hj0 := cutRayTheta_nonneg hp hc0 hcpi i j
    have hkpi := cutRayTheta_lt_pi hp hc0 hcpi i k
    linarith
  have hscaled :=
    one_le_t_mul_normalized_gap_of_opposite_signs
      (rayRhoAt_pos hp i j)
      (rayRhoAt_pos hp i k)
      ht hlam
      (by linarith)
      hspan
      hsign
      hcapJK
  convert hscaled using 1 <;> ring

/-- Consecutive normalized gaps along a displayed cut-ordered ray path. -/
def consecutiveCutRayGaps
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V) :
    OtherVertex i → List (OtherVertex i) → List ℝ
  | _, [] => []
  | prev, r :: rs =>
      t * ((cutRayTheta hp c i r -
        cutRayTheta hp c i prev) / Real.pi) ::
      consecutiveCutRayGaps hp t c i r rs

theorem consecutiveCutRayGaps_length
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i)) :
    (consecutiveCutRayGaps hp t c i prev rs).length =
      rs.length := by
  induction rs generalizing prev with
  | nil => rfl
  | cons r rs ih =>
      simp [consecutiveCutRayGaps, ih r]

/-- Telescoping identity for the total displayed cut-path length. -/
theorem consecutiveCutRayGaps_sum
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i)) :
    (consecutiveCutRayGaps hp t c i prev rs).sum =
      t * ((cutRayTheta hp c i (rs.getLastD prev) -
        cutRayTheta hp c i prev) / Real.pi) := by
  induction rs generalizing prev with
  | nil =>
      simp [consecutiveCutRayGaps]
  | cons r rs ih =>
      simp only [consecutiveCutRayGaps, List.sum_cons]
      rw [ih r]
      cases rs with
      | nil =>
          simp
      | cons s ss =>
          simp only [List.getLastD_cons]
          ring

/-- The last adjusted sign of the mapped path is the adjusted sign of its last
displayed ray. -/
theorem boolLastFrom_map_cutRaySign
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i)) :
    boolLastFrom
        (cutRaySign hp c i prev)
        (rs.map (cutRaySign hp c i))
      =
    cutRaySign hp c i (rs.getLastD prev) := by
  rw [boolLastFrom_eq_getLastD, map_getLastD]

/-- Every finite cut-ordered ray subpath satisfies the exact list-level
transition lower-bound predicate used by AdjacentTransitionDominator. -/
theorem cutOrderedRayPath_transitionGapLowerBound
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    (hnodup : (prev :: rs).Nodup)
    (hsorted :
      (prev :: rs).Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b)) :
    TransitionGapLowerBound
      (cutRaySign hp c i prev)
      (rs.map (cutRaySign hp c i))
      (consecutiveCutRayGaps hp t c i prev rs) := by
  induction rs generalizing prev with
  | nil =>
      simp [TransitionGapLowerBound, consecutiveCutRayGaps]
  | cons r rs ih =>
      have hnod := List.nodup_cons.mp hnodup
      have hpair := List.pairwise_cons.mp hsorted
      have hprevR : prev ≠ r := by
        intro h
        subst r
        exact hnod.1 (by simp)
      have horder :
          cutRayTheta hp c i prev ≤
            cutRayTheta hp c i r :=
        hpair.1 r (by simp)
      have hgap0 :
          0 ≤
            t * ((cutRayTheta hp c i r -
              cutRayTheta hp c i prev) / Real.pi) := by
        positivity
      refine ⟨hgap0, ?_, ?_⟩
      · intro hsign
        exact one_le_t_mul_cutRay_gap_of_sign_ne
          hp hcap ht hlam hc0 hcpi i hprevR horder hsign
      · exact ih r hnod.2 hpair.2

#print axioms one_le_t_mul_cutRay_gap_of_sign_ne
#print axioms consecutiveCutRayGaps_sum
#print axioms cutOrderedRayPath_transitionGapLowerBound

end JSP000404Research
