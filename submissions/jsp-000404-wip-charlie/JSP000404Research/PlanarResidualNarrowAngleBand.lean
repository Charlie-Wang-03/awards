import JSP000404Research.PlanarOverweightGeometricHardDichotomy
import JSP000404Research.ProjectionLocalDirectionValue
import Mathlib.Tactic

/-!
# Quantitative seam concentration of genuine planar residual edges

For a canonical generic projection of an injective planar AngleCap
configuration with t=n+delta, 0<=delta<1/2 and lambda=pi/t,
the residual colour is the last integer direction band.

Every ordered residual edge u<v has lifted forward angle
  phi = centreForwardLiftedAngle(u->v)
and global projection base beta. Its normalized direction value
  D(u,v) = (phi-beta)/lambda
lies in [n,t), so the *physical* distance to the upper seam
  pi-(phi-beta)
lies in the half-open interval (0,delta*lambda].

Since delta<1/2, EVERY residual edge direction lies within a
sub-half-lambda terminal wedge adjacent to the common projection seam.

This is genuine planar angular localization, not an abstract Hall
expansion, not a contradiction, and not a payment theorem.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

/-- Each genuine standard residual edge occupies the terminal
physical-angle wedge, of width at most delta*lambda < lambda/2. -/
theorem planar_standardResidual_edge_narrow_terminal_angle
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (u v : ProjectionOrdered V)
    (huv :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      u < v)
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
      IsResidual B u v) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let j : OtherVertex u := ⟨v, ne_of_gt huv⟩
    let a := centreForwardLiftedAngle hp u j -
        projectionAngleBase (genericProjectionSlope p)
    0 < Real.pi - a ∧
      Real.pi - a ≤ delta * lam ∧
      delta * lam < lam / 2 := by
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
  let j : OtherVertex u := ⟨v, ne_of_gt huv⟩
  let a : ℝ :=
    centreForwardLiftedAngle hp u j -
      projectionAngleBase (genericProjectionSlope p)
  change
    0 < Real.pi - a ∧
      Real.pi - a ≤ delta * lam ∧
      delta * lam < lam / 2
  have hres' : IsResidual B u v := by
    simpa [B, D] using hres
  have hlow : (n : ℝ) ≤ D.value u v :=
    (standardResidual_iff_high D n hwidth huv).1 hres'
  have hupper : D.value u v < t :=
    D.belowWidth huv
  have hdir :
      D.value u v = a / lam := by
    have hdirection :=
      genericLocalDirectionValue_eq_forward
        hp hcap hpos hlam u j
    have hnvu : ¬ v < u := not_lt_of_ge huv.le
    simpa [D, a, j, DirectionData.localDirectionValue,
      huv, hnvu] using hdirection
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos hpos
  have hpi : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt hpos]
  have hpi2 : (n : ℝ) * lam + delta * lam = Real.pi := by
    calc
      (n : ℝ) * lam + delta * lam =
          ((n : ℝ) + delta) * lam := by ring
      _ = t * lam := by rw [← ht]
      _ = Real.pi := hpi
  have hscaled : D.value u v * lam = a := by
    rw [hdir]
    field_simp [ne_of_gt hlamPos]
  have hloScaled :=
    mul_le_mul_of_nonneg_right hlow hlamPos.le
  have hhiScaled :=
    mul_lt_mul_of_pos_right hupper hlamPos
  have hhalfScaled :=
    mul_lt_mul_of_pos_right hdeltaHalf hlamPos
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

#print axioms planar_standardResidual_edge_narrow_terminal_angle


/-- A global cross-centre consequence: any two residual edges
(even with disjoint endpoints) have lifted angular directions in the
same terminal cone, whose diameter is at most delta*lambda < lambda/2.

This is a TRUE angular separation inequality between different edges,
not merely a separate top-band classification at each centre. -/
theorem planar_standardResidual_edges_common_narrow_cone
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (u v x y : ProjectionOrdered V)
    (huv :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      u < v)
    (hxy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      x < y)
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
      IsResidual B u v ∧ IsResidual B x y) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let juv : OtherVertex u := ⟨v, ne_of_gt huv⟩
    let jxy : OtherVertex x := ⟨y, ne_of_gt hxy⟩
    |centreForwardLiftedAngle hp u juv -
       centreForwardLiftedAngle hp x jxy| ≤ delta * lam ∧
      delta * lam < lam / 2 := by
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
  have hres' : IsResidual B u v ∧ IsResidual B x y := by
    simpa [B, D] using hres
  let juv : OtherVertex u := ⟨v, ne_of_gt huv⟩
  let jxy : OtherVertex x := ⟨y, ne_of_gt hxy⟩
  let beta : ℝ := projectionAngleBase (genericProjectionSlope p)
  let a : ℝ := centreForwardLiftedAngle hp u juv - beta
  let b : ℝ := centreForwardLiftedAngle hp x jxy - beta
  have ha :=
    planar_standardResidual_edge_narrow_terminal_angle
      hp hcap hn hdelta0 hdeltaHalf ht hlam u v huv hres'.1
  have hb :=
    planar_standardResidual_edge_narrow_terminal_angle
      hp hcap hn hdelta0 hdeltaHalf ht hlam x y hxy hres'.2
  change 0 < Real.pi - a ∧
    Real.pi - a ≤ delta * lam ∧ delta * lam < lam / 2 at ha
  change 0 < Real.pi - b ∧
    Real.pi - b ≤ delta * lam ∧ delta * lam < lam / 2 at hb
  change
    |centreForwardLiftedAngle hp u juv -
       centreForwardLiftedAngle hp x jxy| ≤ delta * lam ∧
      delta * lam < lam / 2
  constructor
  · have hAbs : |a - b| ≤ delta * lam := by
      apply abs_le.mpr
      constructor <;> dsimp [a, b] at * <;> linarith
    simpa [a, b, beta, sub_sub_sub_cancel_right] using hAbs
  · exact ha.2.2

#print axioms planar_standardResidual_edges_common_narrow_cone

end ProjectionOrdered
end JSP000404Research
