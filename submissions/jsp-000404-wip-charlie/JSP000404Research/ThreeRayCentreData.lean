import JSP000404Research.FinFourCentreCycle
import JSP000404Research.ThreeAngleGapDeletion
import Mathlib.Tactic

/-!
# Explicit three-ray data for a four-point centre

After FinFourCentreCycle, write the sorted canonical rays as r0,r1,r2.
The three normalized projective gaps are then

  g01 = (theta1-theta0)/pi,
  g12 = (theta2-theta1)/pi,
  g20 = (theta0+pi-theta2)/pi.

This file exposes those three numbers and their fixed-t floor quotients
directly from CentreProjectiveCycle.
-/

namespace JSP000404Research

open Real

def gap01
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (r0 r1 : OtherVertex i) : ℝ :=
  (rayThetaAt hp i r1 - rayThetaAt hp i r0) / Real.pi

def gap12
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (r1 r2 : OtherVertex i) : ℝ :=
  (rayThetaAt hp i r2 - rayThetaAt hp i r1) / Real.pi

def gap20
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (r0 r2 : OtherVertex i) : ℝ :=
  (rayThetaAt hp i r0 + Real.pi - rayThetaAt hp i r2) / Real.pi

theorem centre_gaps_eq_three
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    C.gaps =
      [gap01 r0 r1, gap12 r1 r2, gap20 r0 r2] := by
  rw [CentreProjectiveCycle.gaps, CentreProjectiveCycle.angles, hrays]
  simp [gap01, gap12, gap20,
    normalizedProjectiveGaps_three]

theorem centre_quotientList_eq_three
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    quotientList t C.gaps =
      [Nat.floor (t * gap01 r0 r1),
       Nat.floor (t * gap12 r1 r2),
       Nat.floor (t * gap20 r0 r2)] := by
  rw [centre_gaps_eq_three C r0 r1 r2 hrays]
  rfl

theorem three_ray_theta_order
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    rayThetaAt hp i r0 ≤ rayThetaAt hp i r1 ∧
      rayThetaAt hp i r1 ≤ rayThetaAt hp i r2 := by
  rw [hrays] at C.theta_sorted
  simp only [List.pairwise_cons, List.mem_cons,
    List.mem_singleton] at C.theta_sorted
  exact ⟨C.theta_sorted.1 r1 (by simp),
    C.theta_sorted.2.1 r2 (by simp)⟩

theorem three_gaps_nonneg
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    0 ≤ gap01 r0 r1 ∧
      0 ≤ gap12 r1 r2 ∧
      0 ≤ gap20 r0 r2 := by
  have hord := three_ray_theta_order C r0 r1 r2 hrays
  constructor
  · exact div_nonneg (sub_nonneg.mpr hord.1) Real.pi_pos.le
  constructor
  · exact div_nonneg (sub_nonneg.mpr hord.2) Real.pi_pos.le
  · apply div_nonneg
    · have h0 := rayThetaAt_nonneg hp i r0
      have h2 := rayThetaAt_lt_pi hp i r2
      linarith
    · exact Real.pi_pos.le

theorem three_gaps_sum_one
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    gap01 r0 r1 + gap12 r1 r2 + gap20 r0 r2 = 1 := by
  have hsum := C.gaps_sum
  rw [centre_gaps_eq_three C r0 r1 r2 hrays] at hsum
  simpa using hsum

/-- Scaled three gaps sum to the fixed parameter t. -/
theorem scaled_three_gaps_sum_t
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    t * gap01 r0 r1 +
      t * gap12 r1 r2 +
      t * gap20 r0 r2 = t := by
  have h := three_gaps_sum_one C r0 r1 r2 hrays
  nlinarith

#print axioms centre_gaps_eq_three
#print axioms centre_quotientList_eq_three
#print axioms three_ray_theta_order
#print axioms three_gaps_sum_one
#print axioms scaled_three_gaps_sum_t

end JSP000404Research
