import JSP000404Research.CutMergedCrossCentreFibre
import JSP000404Research.CutSupportThreeBadSmallAngle
import JSP000404Research.UncoveredBoundaryColoring
import Mathlib.Tactic

/-!
# Equal merged incident colour gives a uniformly short angle

At a critical-uncovered cut, take two rays from the same centre whose incident
colours in the final merged partition are equal.

The old cut colours are either:
* equal, in which case the rays lie in one old unit band and the genuine angle
  is < lambda; or
* the boundary pair 0,n (in either order), in which case after moving to the
  short boundary cut both rays lie in a normalized interval of length
  1+delta and have the same adjusted sign.

Thus in all cases

  angle <= (1+delta)*lambda.

This is the same-colour geometric outlet for the ordinary-minimum witness in
the remaining two-bad equality terminal.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem actual_angle_le_one_add_delta_lam_of_two_boundary_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
          C t delta u (t * c / Real.pi))
    (i : V)
    {x y : OtherVertex i}
    (hxy : x ≠ y)
    (hx :
      CutBoundaryRay hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith) i x)
    (hy :
      CutBoundaryRay hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith) i y) :
    EuclideanGeometry.angle (p x.1) (p i) (p y.1)
      ≤ (1 + delta) * lam := by
  let cS := boundaryShortCut t delta c
  have hcS0 : 0 ≤ cS :=
    boundaryShortCut_nonneg hn ht hdelta0 hc0 hcpi
  have hcSpi : cS < Real.pi :=
    boundaryShortCut_lt_pi hn ht hdelta0 hc0 hcpi

  have hxArc :=
    cutBoundaryRay_short_mem
      hp hn htpos ht hdelta0
      (by linarith : delta < 1)
      hc0 hcpi i x hx
  have hyArc :=
    cutBoundaryRay_short_mem
      hp hn htpos ht hdelta0
      (by linarith : delta < 1)
      hc0 hcpi i y hy

  have hxSign :=
    cutBoundaryWrapBit_eq_shortSign
      hp hcap C hn htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      huncovered i x hx
  have hySign :=
    cutBoundaryWrapBit_eq_shortSign
      hp hcap C hn htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      huncovered i y hy
  have hsign :
      cutRaySign hp cS i x =
        cutRaySign hp cS i y := by
    rw [← hxSign, ← hySign]

  rcases le_total
      (cutRayTheta hp cS i x)
      (cutRayTheta hp cS i y)
    with horder | horder
  · have hcoordGap :
        cutNormalizedRayTheta hp t cS i y -
            cutNormalizedRayTheta hp t cS i x
          ≤ 1 + delta := by
      linarith [hxArc.1, hyArc.2]
    have hscaled :
        t * ((cutRayTheta hp cS i y -
          cutRayTheta hp cS i x) / Real.pi)
          ≤ 1 + delta := by
      unfold cutNormalizedRayTheta at hcoordGap
      convert hcoordGap using 1 <;> ring
    exact
      actual_angle_le_delta_lam_of_cut_same_sign_gap
        hp htpos hlam hcS0 hcSpi i
        horder hsign hscaled
  · have hcoordGap :
        cutNormalizedRayTheta hp t cS i x -
            cutNormalizedRayTheta hp t cS i y
          ≤ 1 + delta := by
      linarith [hyArc.1, hxArc.2]
    have hscaled :
        t * ((cutRayTheta hp cS i x -
          cutRayTheta hp cS i y) / Real.pi)
          ≤ 1 + delta := by
      unfold cutNormalizedRayTheta at hcoordGap
      convert hcoordGap using 1 <;> ring
    have h :=
      actual_angle_le_delta_lam_of_cut_same_sign_gap
        hp htpos hlam hcS0 hcSpi i
        horder hsign.symm hscaled
    simpa only [EuclideanGeometry.angle_comm] using h

/-- Unified merged-colour conclusion at one centre. -/
theorem actual_angle_le_one_add_delta_lam_of_equal_uncovered_merged_color
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
          C t delta u (t * c / Real.pi))
    {i x y : V}
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hxy : x ≠ y)
    (heq :
      localIncidentColor
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht
            hdelta0 hdeltaHalf hc0 hcpi huncovered)
          i x
        =
      localIncidentColor
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht
            hdelta0 hdeltaHalf hc0 hcpi huncovered)
          i y) :
    EuclideanGeometry.angle (p x) (p i) (p y)
      ≤ (1 + delta) * lam := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop

  have hfibre :=
    equal_uncovered_merged_incident_colors_old_fibre
      hp hcap C hn htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      huncovered heq

  rcases hfibre with hold | hboundary | hboundary
  · have hlt :
        EuclideanGeometry.angle (p x) (p i) (p y) < lam :=
      actual_angle_lt_lam_of_equal_local_cut_color
        hp hcap htpos hlam hc0 hcpi n htop
        hix hiy hxy (by simpa [P] using hold)
    have hlampos : 0 < lam := by
      rw [hlam]
      exact div_pos Real.pi_pos htpos
    nlinarith
  · let xo : OtherVertex i := ⟨x, hix.symm⟩
    let yo : OtherVertex i := ⟨y, hiy.symm⟩
    have hxRay :
        CutBoundaryRay hp htpos hc0 hcpi n htop i xo := by
      change
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i x).val = 0 ∨
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i x).val = n
      have hlocal :
          localIncidentColor P i x =
            (0 : Fin (n + 1)) := by
        simpa [P] using hboundary.1
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop hix] at hlocal
      left
      exact congrArg Fin.val hlocal
    have hyRay :
        CutBoundaryRay hp htpos hc0 hcpi n htop i yo := by
      change
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i y).val = 0 ∨
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i y).val = n
      have hlocal :
          localIncidentColor P i y = Fin.last n := by
        simpa [P] using hboundary.2
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop hiy] at hlocal
      right
      exact congrArg Fin.val hlocal
    simpa [xo, yo] using
      actual_angle_le_one_add_delta_lam_of_two_boundary_rays
        hp hcap C hn htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi huncovered
        i (by
          intro h
          apply hxy
          exact congrArg Subtype.val h)
        hxRay hyRay
  · let xo : OtherVertex i := ⟨x, hix.symm⟩
    let yo : OtherVertex i := ⟨y, hiy.symm⟩
    have hxRay :
        CutBoundaryRay hp htpos hc0 hcpi n htop i xo := by
      change
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i x).val = 0 ∨
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i x).val = n
      have hlocal :
          localIncidentColor P i x = Fin.last n := by
        simpa [P] using hboundary.1
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop hix] at hlocal
      right
      exact congrArg Fin.val hlocal
    have hyRay :
        CutBoundaryRay hp htpos hc0 hcpi n htop i yo := by
      change
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i y).val = 0 ∨
        (cutProjectiveBandColor
          hp htpos hc0 hcpi n htop i y).val = n
      have hlocal :
          localIncidentColor P i y =
            (0 : Fin (n + 1)) := by
        simpa [P] using hboundary.2
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop hiy] at hlocal
      left
      exact congrArg Fin.val hlocal
    simpa [xo, yo] using
      actual_angle_le_one_add_delta_lam_of_two_boundary_rays
        hp hcap C hn htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi huncovered
        i (by
          intro h
          apply hxy
          exact congrArg Subtype.val h)
        hxRay hyRay

#print axioms actual_angle_le_one_add_delta_lam_of_two_boundary_rays
#print axioms actual_angle_le_one_add_delta_lam_of_equal_uncovered_merged_color

end JSP000404Research
