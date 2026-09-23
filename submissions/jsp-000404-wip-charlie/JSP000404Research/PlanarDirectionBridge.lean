
import JSP000404Research.OrderedDirections
import JSP000404Research.ProjectiveInterval
import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# From a coherent forward angular lift to DirectionData

The centre-gap geometry and the ordered-band/residual geometry currently live
in separate formal layers.  This file supplies the metric half of the missing
bridge.

Assume the vertices have already been linearly ordered so that every increasing
edge admits a positive forward representation

  p(j)-p(i) = rho(i,j) * rayDirection(theta(i,j))

with all theta(i,j) in one half-open interval [base,base+pi), and assume the
elementary triangle direction-betweenness property: for i<j<k the outer-edge
direction theta(i,k) lies between theta(i,j) and theta(j,k).

Under the global angle cap pi-lambda and the normalization

  pi = t * lambda,

these data automatically satisfy every metric axiom of DirectionData after
normalizing

  value(i,j) = (theta(i,j)-base)/lambda.

Indeed:

* all values lie in [0,t);
* the angle at the middle vertex is
    pi - |theta(i,j)-theta(j,k)|,
  so the global cap forces a separation of at least lambda, hence at least
  one normalized unit;
* angles at the first and last vertices are the ordinary direction
  differences, hence at most pi-lambda=(t-1)lambda.

Therefore the only remaining Planar -> DirectionData existence problem is the
finite coherent-forward-lift construction itself (choose a generic projection
direction / vertex order and prove direction betweenness).  No Sendov
floor/exponent arithmetic is hidden in this bridge.
-/

namespace JSP000404Research

open Real

structure ForwardAngleLift
    {V : Type*} [LinearOrder V]
    (p : V → Plane) (base : ℝ) where
  theta : V → V → ℝ
  rho : V → V → ℝ
  rho_pos :
    ∀ {i j : V}, i < j → 0 < rho i j
  theta_lower :
    ∀ {i j : V}, i < j → base ≤ theta i j
  theta_upper :
    ∀ {i j : V}, i < j → theta i j < base + Real.pi
  repr :
    ∀ {i j : V}, i < j →
      p j - p i = rho i j • rayDirection (theta i j)
  between :
    ∀ {i j k : V}, i < j → j < k →
      (theta i j ≤ theta i k ∧ theta i k ≤ theta j k) ∨
      (theta j k ≤ theta i k ∧ theta i k ≤ theta i j)

namespace ForwardAngleLift

def value
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base lam : ℝ}
    (F : ForwardAngleLift p base) :
    V → V → ℝ :=
  fun i j => (F.theta i j - base) / lam

theorem theta_abs_sub_lt_pi
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    {i j k l : V}
    (hij : i < j) (hkl : k < l) :
    |F.theta i j - F.theta k l| < Real.pi := by
  have hijLo := F.theta_lower hij
  have hijHi := F.theta_upper hij
  have hklLo := F.theta_lower hkl
  have hklHi := F.theta_upper hkl
  rw [abs_lt]
  constructor <;> linarith

theorem theta_abs_sub_le_pi
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    {i j k l : V}
    (hij : i < j) (hkl : k < l) :
    |F.theta i j - F.theta k l| ≤ Real.pi :=
  (F.theta_abs_sub_lt_pi hij hkl).le

/-- Angle between two increasing forward edge vectors is exactly the absolute
difference of their lifted directions. -/
theorem angle_forward_edges
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    {i j k l : V}
    (hij : i < j) (hkl : k < l) :
    InnerProductGeometry.angle
        (p j - p i) (p l - p k) =
      |F.theta i j - F.theta k l| := by
  rw [F.repr hij, F.repr hkl,
      InnerProductGeometry.angle_smul_left_of_pos
        _ _ (F.rho_pos hij),
      InnerProductGeometry.angle_smul_right_of_pos
        _ _ (F.rho_pos hkl)]
  exact angle_rayDirection
    (F.theta i j) (F.theta k l)
    (F.theta_abs_sub_le_pi hij hkl)

/-- Angle at the middle point of an increasing triple is the supplement of the
difference of the two consecutive forward directions. -/
theorem angle_middle_eq_pi_sub_abs
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    {i j k : V}
    (hij : i < j) (hjk : j < k) :
    EuclideanGeometry.angle (p i) (p j) (p k) =
      Real.pi - |F.theta i j - F.theta j k| := by
  change
    InnerProductGeometry.angle
        (p i - p j) (p k - p j) =
      Real.pi - |F.theta i j - F.theta j k|
  have hneg : p i - p j = -(p j - p i) := by abel
  rw [hneg, InnerProductGeometry.angle_neg_left,
      F.angle_forward_edges hij hjk]

/-- Angle at the first point is the ordinary difference of the two forward
directions from that point. -/
theorem angle_first_eq_abs
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    {i j k : V}
    (hij : i < j) (hjk : j < k) :
    EuclideanGeometry.angle (p j) (p i) (p k) =
      |F.theta i j - F.theta i k| := by
  have hik : i < k := hij.trans hjk
  change
    InnerProductGeometry.angle
      (p j - p i) (p k - p i) =
        |F.theta i j - F.theta i k|
  exact F.angle_forward_edges hij hik

/-- Angle at the last point is the ordinary difference of the two forward
directions ending at that point. -/
theorem angle_last_eq_abs
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base : ℝ}
    (F : ForwardAngleLift p base)
    {i j k : V}
    (hij : i < j) (hjk : j < k) :
    EuclideanGeometry.angle (p i) (p k) (p j) =
      |F.theta i k - F.theta j k| := by
  have hik : i < k := hij.trans hjk
  change
    InnerProductGeometry.angle
      (p i - p k) (p j - p k) =
        |F.theta i k - F.theta j k|
  have hnegIK : p i - p k = -(p k - p i) := by abel
  have hnegJK : p j - p k = -(p k - p j) := by abel
  rw [hnegIK, hnegJK,
      InnerProductGeometry.angle_neg_neg,
      F.angle_forward_edges hik hjk]

theorem abs_value_sub_value
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base lam : ℝ}
    (F : ForwardAngleLift p base)
    (hlam : 0 < lam)
    (a b c d : V) :
    |F.value (lam := lam) a b -
        F.value (lam := lam) c d|
      =
    |F.theta a b - F.theta c d| / lam := by
  unfold value
  have h :
      (F.theta a b - base) / lam -
          (F.theta c d - base) / lam
        =
      (F.theta a b - F.theta c d) / lam := by
    ring
  rw [h, abs_div, abs_of_pos hlam]

/-- Main bridge: a coherent forward angular lift plus AngleCap produces the
abstract ordered direction data used by all band/residual modules. -/
noncomputable def toDirectionData
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base lam t : ℝ}
    (F : ForwardAngleLift p base)
    (hcap : AngleCap p lam)
    (hlam : 0 < lam)
    (ht : 0 < t)
    (hscale : Real.pi = t * lam) :
    DirectionData V t where
  value := F.value (lam := lam)
  nonnegative := by
    intro i j hij
    unfold value
    exact div_nonneg
      (sub_nonneg.mpr (F.theta_lower hij))
      hlam.le
  belowWidth := by
    intro i j hij
    unfold value
    rw [div_lt_iff₀ hlam]
    have htheta := F.theta_upper hij
    linarith
  between := by
    intro i j k hij hjk
    have hb := F.between hij hjk
    unfold value
    rcases hb with hb | hb
    · left
      constructor
      · exact (div_le_div_iff_of_pos_right hlam).2
          (sub_le_sub_right hb.1 base)
      · exact (div_le_div_iff_of_pos_right hlam).2
          (sub_le_sub_right hb.2 base)
    · right
      constructor
      · exact (div_le_div_iff_of_pos_right hlam).2
          (sub_le_sub_right hb.1 base)
      · exact (div_le_div_iff_of_pos_right hlam).2
          (sub_le_sub_right hb.2 base)
  middleSeparated := by
    intro i j k hij hjk
    have hcapMid :
        EuclideanGeometry.angle (p i) (p j) (p k)
          ≤ Real.pi - lam :=
      hcap i j k
        (ne_of_lt hij)
        (ne_of_lt (hij.trans hjk))
        (ne_of_lt hjk)
    rw [F.angle_middle_eq_pi_sub_abs hij hjk] at hcapMid
    have hgap :
        lam ≤ |F.theta i j - F.theta j k| := by
      linarith
    rw [F.abs_value_sub_value hlam]
    exact (le_div_iff₀ hlam).2 (by
      simpa using hgap)
  firstGap := by
    intro i j k hij hjk
    have hik : i < k := hij.trans hjk
    have hcapFirst :
        EuclideanGeometry.angle (p j) (p i) (p k)
          ≤ Real.pi - lam :=
      hcap j i k
        (ne_of_gt hij)
        (ne_of_lt hjk)
        (ne_of_lt hik)
    rw [F.angle_first_eq_abs hij hjk] at hcapFirst
    rw [F.abs_value_sub_value hlam]
    apply (div_le_iff₀ hlam).2
    rw [hscale] at hcapFirst ⊢
    nlinarith
  lastGap := by
    intro i j k hij hjk
    have hik : i < k := hij.trans hjk
    have hcapLast :
        EuclideanGeometry.angle (p i) (p k) (p j)
          ≤ Real.pi - lam :=
      hcap i k j
        (ne_of_lt hik)
        (ne_of_lt hij)
        (ne_of_gt hjk)
    rw [F.angle_last_eq_abs hij hjk] at hcapLast
    rw [F.abs_value_sub_value hlam]
    apply (div_le_iff₀ hlam).2
    rw [hscale] at hcapLast ⊢
    nlinarith

/-- Sendov-normalized wrapper. -/
noncomputable def toDirectionData_sendov
    {V : Type*} [LinearOrder V]
    {p : V → Plane} {base lam t : ℝ}
    (F : ForwardAngleLift p base)
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t) :
    DirectionData V t := by
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  have hscale : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt ht]
  exact F.toDirectionData hcap hlamPos ht hscale

#print axioms ForwardAngleLift.angle_middle_eq_pi_sub_abs
#print axioms ForwardAngleLift.angle_first_eq_abs
#print axioms ForwardAngleLift.angle_last_eq_abs
#print axioms ForwardAngleLift.toDirectionData
#print axioms ForwardAngleLift.toDirectionData_sendov

end ForwardAngleLift
end JSP000404Research
