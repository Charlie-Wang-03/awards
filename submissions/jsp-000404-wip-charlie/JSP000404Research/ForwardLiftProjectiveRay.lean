
import JSP000404Research.ProjectiveRayUniqueness
import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.LocalDirectionCycle
import Mathlib.Tactic

/-!
# Pointwise projective rays from a coherent forward lift

Fix a ForwardAngleLift on a linearly ordered planar configuration.

At a centre i and another vertex j, use the forward edge parameter in the
increasing orientation:

* theta(j,i) if j<i,
* theta(i,j) if i<j.

For an incoming vertex the centre-to-vertex displacement is the negative of
that forward edge, so only the Boolean sign changes; the projective theta is
the same.

When the common lift base lies in (-pi,0), every such local theta lies in
(-pi,pi).  Canonicalizing at the standard projective cut [0,pi) therefore
requires exactly one operation: add pi to negative theta values and flip the
Boolean sign.  ProjectiveRayUniqueness then identifies the resulting parameter
with rayThetaAt exactly.
-/

namespace JSP000404Research

open Real

namespace ForwardAngleLift

def localTheta
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) : ℝ :=
  if h : j.1 < i then
    F.theta j.1 i
  else
    F.theta i j.1

def localRho
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) : ℝ :=
  if h : j.1 < i then
    F.rho j.1 i
  else
    F.rho i j.1

def localSign
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) : Bool :=
  if _h : j.1 < i then false else true

theorem localRho_pos
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) :
    0 < F.localRho i j := by
  unfold localRho
  by_cases hji : j.1 < i
  · simp [hji, F.rho_pos hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, F.rho_pos hij]

theorem localTheta_lower
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) :
    base ≤ F.localTheta i j := by
  unfold localTheta
  by_cases hji : j.1 < i
  · simp [hji, F.theta_lower hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, F.theta_lower hij]

theorem localTheta_upper
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) :
    F.localTheta i j < base + Real.pi := by
  unfold localTheta
  by_cases hji : j.1 < i
  · simp [hji, F.theta_upper hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, F.theta_upper hij]

/-- Exact signed representation of the centre-to-vertex displacement using
the coherent forward theta. -/
theorem local_signed_repr
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) :
    p j.1 - p i =
      F.localRho i j •
        signedRayDirection
          (F.localSign i j)
          (F.localTheta i j) := by
  unfold localRho localSign localTheta
  by_cases hji : j.1 < i
  · simp only [hji, ↓reduceIte, signedRayDirection,
      Bool.false_eq_true, if_false]
    have hneg :
        p j.1 - p i = -(p i - p j.1) := by
      abel
    rw [hneg, F.repr hji]
    simp
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp only [hji, ↓reduceIte, signedRayDirection,
      if_true]
    exact F.repr hij

def canonicalizedLocalTheta
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) : ℝ :=
  if F.localTheta i j < 0 then
    F.localTheta i j + Real.pi
  else
    F.localTheta i j

def canonicalizedLocalSign
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) : Bool :=
  if F.localTheta i j < 0 then
    !(F.localSign i j)
  else
    F.localSign i j

theorem canonicalizedLocalTheta_bounds
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (hbaseLo : -Real.pi < base)
    (hbaseHi : base < 0)
    (i : V) (j : OtherVertex i) :
    0 ≤ F.canonicalizedLocalTheta i j ∧
      F.canonicalizedLocalTheta i j < Real.pi := by
  unfold canonicalizedLocalTheta
  by_cases hneg : F.localTheta i j < 0
  · simp only [hneg, if_true]
    have hlo := F.localTheta_lower i j
    constructor <;> linarith
  · simp only [hneg, if_false]
    have h0 : 0 ≤ F.localTheta i j :=
      le_of_not_gt hneg
    have hup := F.localTheta_upper i j
    constructor
    · exact h0
    · linarith

/-- Canonicalization preserves the represented geometric ray. -/
theorem local_signed_repr_canonicalized
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    (i : V) (j : OtherVertex i) :
    p j.1 - p i =
      F.localRho i j •
        signedRayDirection
          (F.canonicalizedLocalSign i j)
          (F.canonicalizedLocalTheta i j) := by
  rw [F.local_signed_repr i j]
  unfold canonicalizedLocalSign canonicalizedLocalTheta
  by_cases hneg : F.localTheta i j < 0
  · simp only [hneg, if_true]
    congr 1
    exact same_ray_after_pi_shift_to_common_sign
      (F.localSign i j) (F.localTheta i j)
  · simp [hneg]

/-- The canonical projective theta is exactly the zero-cut canonicalization of
the coherent forward theta. -/
theorem rayThetaAt_eq_canonicalizedLocalTheta
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (hp : Function.Injective p)
    (F : ForwardAngleLift p base)
    (hbaseLo : -Real.pi < base)
    (hbaseHi : base < 0)
    (i : V) (j : OtherVertex i) :
    rayThetaAt hp i j =
      F.canonicalizedLocalTheta i j := by
  have hb :=
    F.canonicalizedLocalTheta_bounds
      hbaseLo hbaseHi i j
  exact rayThetaAt_eq_of_positive_signed_repr
    hp i j
    (F.localRho_pos i j)
    hb.1 hb.2
    (F.local_signed_repr_canonicalized i j)

/-- Local DirectionData value induced by F is the affine rescaling of the
same local forward theta. -/
theorem toDirectionData_localDirectionValue
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base lam t : ℝ}
    (F : ForwardAngleLift p base)
    (hcap : AngleCap p lam)
    (hlam : 0 < lam)
    (ht : 0 < t)
    (hscale : Real.pi = t * lam)
    (i : V) (j : OtherVertex i) :
    (F.toDirectionData hcap hlam ht hscale).localDirectionValue i j =
      (F.localTheta i j - base) / lam := by
  unfold DirectionData.localDirectionValue
  unfold localTheta
  by_cases hji : j.1 < i
  · simp [hji, ForwardAngleLift.toDirectionData,
      ForwardAngleLift.value]
  · simp [hji, ForwardAngleLift.toDirectionData,
      ForwardAngleLift.value]

#print axioms ForwardAngleLift.local_signed_repr
#print axioms ForwardAngleLift.canonicalizedLocalTheta_bounds
#print axioms ForwardAngleLift.rayThetaAt_eq_canonicalizedLocalTheta
#print axioms ForwardAngleLift.toDirectionData_localDirectionValue

end ForwardAngleLift
end JSP000404Research
