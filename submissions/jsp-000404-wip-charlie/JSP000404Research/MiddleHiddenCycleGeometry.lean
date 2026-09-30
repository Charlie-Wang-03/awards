import JSP000404Research.SupportThreeMiddleHiddenCycleCertificate
import JSP000404Research.FullQuotientZeroAngleMass
import JSP000404Research.CyclicEdgeRotation
import Mathlib.Tactic

/-!
# Geometry aligned to an explicit middle-hidden cycle certificate

The explicit five-ray middle-hidden certificate retains the quotient rotation

  [qFirst, 0, qHidden, 0, qLast]

but, by itself, does not retain the corresponding actual-angle list.  This
file aligns the canonical cyclic angle list to the same rotation.

For an exact deficit-three/support-three centre the total actual-angle mass on
zero quotient positions is at most delta*lambda.  In the displayed
middle-hidden cycle those zero positions are exactly r--b and c--d.  Hence

  angle(r,i,b) + angle(c,i,d) <= delta*lambda.

This gives a geometry statement whose witnesses are definitionally the same
r,b,c,d,qFirst,qHidden,qLast stored in
`MiddleHiddenPinnedCycleCertificate`.
-/

namespace JSP000404Research

open Real

namespace MiddleHiddenPinnedCycleCertificate

theorem rotated_actual_angles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    ∃ first0 : OtherVertex i, ∃ rest0 : List (OtherVertex i),
      C.rays = first0 :: rest0 ∧
      (cyclicRayAngles (p := p) i first0 rest0).rotate H.k =
        EuclideanGeometry.angle (p top) (p i) (p H.r.1) ::
        EuclideanGeometry.angle (p H.r.1) (p i) (p H.b.1) ::
        EuclideanGeometry.angle (p H.b.1) (p i) (p H.c.1) ::
        EuclideanGeometry.angle (p H.c.1) (p i) (p H.d.1) ::
        EuclideanGeometry.angle (p H.d.1) (p i) (p top) :: [] := by
  classical
  obtain ⟨first0, rest0, hrays0⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases hR : C.rays with
    | nil =>
        exact False.elim (C.nonempty hR)
    | cons first rest =>
        exact ⟨first, rest, hR⟩

  let As : List ℝ :=
    cyclicRayAngles (p := p) i first0 rest0
  let w :=
    fun x y : OtherVertex i =>
      EuclideanGeometry.angle (p x.1) (p i) (p y.1)

  have hAsEdge :
      As = cyclicEdgeValues w C.rays := by
    dsimp [As, w]
    rw [hrays0]
    exact cyclicRayAngles_eq_cyclicEdgeValues
      (p := p) i first0 rest0

  have hrot :
      As.rotate H.k =
        cyclicRayAngles (p := p) i
          (⟨top, htopi⟩ : OtherVertex i)
          (H.r :: H.b :: H.c :: H.d :: []) := by
    calc
      As.rotate H.k
          = (cyclicEdgeValues w C.rays).rotate H.k := by
              rw [hAsEdge]
      _ = cyclicEdgeValues w (C.rays.rotate H.k) := by
              symm
              exact cyclicEdgeValues_rotate w C.rays H.k
      _ = cyclicEdgeValues w
            ((⟨top, htopi⟩ : OtherVertex i) ::
              H.r :: H.b :: H.c :: H.d :: []) := by
              rw [H.rays_rotate]
      _ = cyclicRayAngles (p := p) i
            (⟨top, htopi⟩ : OtherVertex i)
            (H.r :: H.b :: H.c :: H.d :: []) := by
              symm
              exact cyclicRayAngles_eq_cyclicEdgeValues
                (p := p) i
                (⟨top, htopi⟩ : OtherVertex i)
                (H.r :: H.b :: H.c :: H.d :: [])

  refine ⟨first0, rest0, hrays0, ?_⟩
  dsimp [As] at hrot
  rw [hrot]
  simp [cyclicRayAngles, consecutiveRayAngles]

theorem zero_edge_sum_le_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    EuclideanGeometry.angle (p H.r.1) (p i) (p H.b.1) +
        EuclideanGeometry.angle (p H.c.1) (p i) (p H.d.1)
      ≤ delta * lam := by
  obtain ⟨first0, rest0, hrays0, hAngles⟩ :=
    H.rotated_actual_angles

  let qs : List ℕ := quotientList t C.gaps
  let As : List ℝ :=
    cyclicRayAngles (p := p) i first0 rest0

  have hqLen :
      qs.length = C.rays.length := by
    dsimp [qs]
    rw [quotientList_length, C.gaps_length]
  have hALen :
      As.length = C.rays.length := by
    dsimp [As]
    rw [cyclicRayAngles_length]
    simpa [hrays0]
  have hqA : qs.length = As.length := by
    rw [hqLen, hALen]

  have hmass :
      listZeroAngleMass qs As ≤ delta * lam := by
    dsimp [qs, As]
    exact
      centre_zeroAngleMass_le_delta_lam_of_deficit_three_support_three
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        i C hexp hsupport first0 rest0 hrays0

  have hmassRot :
      listZeroAngleMass
          (qs.rotate H.k) (As.rotate H.k)
        ≤ delta * lam := by
    rw [listZeroAngleMass_rotate qs As hqA H.k]
    exact hmass

  have hqShape :
      qs.rotate H.k =
        H.qFirst :: 0 :: H.qHidden :: 0 :: H.qLast :: [] := by
    dsimp [qs]
    exact H.quotients_rotate

  have hAShape :
      As.rotate H.k =
        EuclideanGeometry.angle (p top) (p i) (p H.r.1) ::
        EuclideanGeometry.angle (p H.r.1) (p i) (p H.b.1) ::
        EuclideanGeometry.angle (p H.b.1) (p i) (p H.c.1) ::
        EuclideanGeometry.angle (p H.c.1) (p i) (p H.d.1) ::
        EuclideanGeometry.angle (p H.d.1) (p i) (p top) :: [] := by
    dsimp [As]
    exact hAngles

  rw [hqShape, hAShape] at hmassRot
  have hFirstNe : H.qFirst ≠ 0 := by omega
  have hLastNe : H.qLast ≠ 0 := by omega
  simpa [listZeroAngleMass, hFirstNe, H.qHidden_ne, hLastNe]
    using hmassRot

#print axioms MiddleHiddenPinnedCycleCertificate.rotated_actual_angles
#print axioms MiddleHiddenPinnedCycleCertificate.zero_edge_sum_le_delta_lam

end MiddleHiddenPinnedCycleCertificate
end JSP000404Research
