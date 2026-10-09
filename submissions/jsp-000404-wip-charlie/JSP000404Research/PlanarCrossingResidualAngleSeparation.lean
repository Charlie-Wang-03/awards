import JSP000404Research.StandardResidualCrossingHalfBand
import JSP000404Research.ProjectionLocalDirectionValue
import Mathlib.Tactic

/-!
# Planar crossing residual edges force two physical full-lambda angular gaps

Let u<a<v<b in the *canonical projection order* and suppose uv and ab
are residual edges for a true injective planar AngleCap configuration.
The ordered DirectionData half-band crossing theorem implies av residual,
while ua and vb are non-residual directions each at least one normalized
unit below the central direction av.

Convert normalized direction differences into genuine forward-lifted
physical angular differences using the kernel-checked generic planar
DirectionData representation. The two flanks each lie at least lambda
below the angular direction of av, and since av is strictly below the
upper seam, each outer flank is STRICTLY farther than lambda from
that seam. Moreover the flanks are below normalized n-1/2.

This is a concrete four-vertex planar geometric restriction. It is
not a claim that the planar segments actually intersect, nor a global
injection or defect-payment theorem.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_crossing_residual_forces_two_full_lambda_angle_gaps
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (u a v b : ProjectionOrdered V)
    (hua :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      u < a)
    (hav :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < v)
    (hvb :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      v < b)
    (hres :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let hpos : 0 < t := by
        rw [ht]
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      let D := genericDirectionData_sendov hp hcap hpos hlam
      let B := standardResidualColoring D n
        (by rw [ht]; push_cast; linarith)
      IsResidual B u v ∧ IsResidual B a b) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n
      (by rw [ht]; push_cast; linarith)
    let beta := projectionAngleBase (genericProjectionSlope p)
    let phiUA :=
      centreForwardLiftedAngle hp u ⟨a, ne_of_gt hua⟩
    let phiAV :=
      centreForwardLiftedAngle hp a ⟨v, ne_of_gt hav⟩
    let phiVB :=
      centreForwardLiftedAngle hp v ⟨b, ne_of_gt hvb⟩
    IsResidual B a v ∧
      ¬ IsResidual B u a ∧
      ¬ IsResidual B v b ∧
      phiUA + lam ≤ phiAV ∧
      phiVB + lam ≤ phiAV ∧
      lam < Real.pi - (phiUA - beta) ∧
      lam < Real.pi - (phiVB - beta) ∧
      D.value u a + (1 : ℝ) / 2 < (n : ℝ) ∧
      D.value v b + (1 : ℝ) / 2 < (n : ℝ) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < ((n + 1 : ℕ) : ℝ) := by
    rw [ht]
    push_cast
    linarith
  let D := genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let beta : ℝ := projectionAngleBase (genericProjectionSlope p)
  let phiUA := centreForwardLiftedAngle hp u ⟨a, ne_of_gt hua⟩
  let phiAV := centreForwardLiftedAngle hp a ⟨v, ne_of_gt hav⟩
  let phiVB := centreForwardLiftedAngle hp v ⟨b, ne_of_gt hvb⟩
  change
    IsResidual B a v ∧
      ¬ IsResidual B u a ∧
      ¬ IsResidual B v b ∧
      phiUA + lam ≤ phiAV ∧
      phiVB + lam ≤ phiAV ∧
      lam < Real.pi - (phiUA - beta) ∧
      lam < Real.pi - (phiVB - beta) ∧
      D.value u a + (1 : ℝ) / 2 < (n : ℝ) ∧
      D.value v b + (1 : ℝ) / 2 < (n : ℝ)
  have hres' : IsResidual B u v ∧ IsResidual B a b := by
    simpa [B, D] using hres
  obtain ⟨hcentral, hnotUA, hnotVB,
    hgapUA, hgapVB, hhalfUA, hhalfVB⟩ :=
    standardResidual_crossing_forces_two_subhalf_flanks
      D hdeltaHalf ht hwidth hua hav hvb hres'.1 hres'.2
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos hpos
  have hpi : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt hpos]
  have hAng (x y : ProjectionOrdered V) (hxy : x < y) :
      D.value x y * lam =
        centreForwardLiftedAngle hp x ⟨y, ne_of_gt hxy⟩ -
          beta := by
    have hd :=
      genericLocalDirectionValue_eq_forward
        hp hcap hpos hlam x ⟨y, ne_of_gt hxy⟩
    have hdir :
        D.value x y =
          (centreForwardLiftedAngle hp x ⟨y, ne_of_gt hxy⟩ -
            beta) / lam := by
      simpa [D, beta, DirectionData.localDirectionValue,
        hxy, not_lt_of_ge hxy.le] using hd
    rw [hdir]
    field_simp [ne_of_gt hlamPos]
  have hAV := hAng a v hav
  have hVB := hAng v b hvb
  have hUA' : D.value u a * lam = phiUA - beta := by
    simpa [phiUA] using hAng u a hua
  have hAV' : D.value a v * lam = phiAV - beta := by
    simpa [phiAV] using hAV
  have hVB' : D.value v b * lam = phiVB - beta := by
    simpa [phiVB] using hVB
  have hAngularUA : phiUA + lam ≤ phiAV := by
    have hscaled := mul_le_mul_of_nonneg_right hgapUA hlamPos.le
    rw [add_mul, one_mul, hUA', hAV'] at hscaled
    linarith
  have hAngularVB : phiVB + lam ≤ phiAV := by
    have hscaled := mul_le_mul_of_nonneg_right hgapVB hlamPos.le
    rw [add_mul, one_mul, hVB', hAV'] at hscaled
    linarith
  have hAVUpper : phiAV - beta < Real.pi := by
    have hlt := mul_lt_mul_of_pos_right (D.belowWidth hav) hlamPos
    rw [hAV', hpi] at hlt
    exact hlt
  exact ⟨hcentral, hnotUA, hnotVB,
    hAngularUA, hAngularVB,
    by linarith, by linarith, hhalfUA, hhalfVB⟩

#print axioms planar_crossing_residual_forces_two_full_lambda_angle_gaps

end ProjectionOrdered
end JSP000404Research
