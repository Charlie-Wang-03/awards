import JSP000404Research.CanonicalProjectiveRay
import JSP000404Research.PlanarDirectionBridge
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# A forward angular lift including a horizontal boundary edge

Order points by height, breaking equal heights by horizontal coordinate. Every
forward displacement then has argument in `[0, pi)`. Polar reconstruction and
the parallelogram angle identity supply a `ForwardAngleLift`, including its
betweenness property. This chart keeps a horizontal observer edge at angle zero.
-/

namespace JSP000404Research

/-- A real coordinate lying on the shortest path between two other coordinates
lies in their ordered interval. -/
private theorem between_of_abs_add {a b c : ℝ}
    (h : |a - c| = |a - b| + |c - b|) :
    (a ≤ b ∧ b ≤ c) ∨ (c ≤ b ∧ b ≤ a) := by
  rcases le_total a c with hac | hca
  · left
    rw [abs_of_nonpos (sub_nonpos.mpr hac)] at h
    constructor
    · by_contra! hab
      rw [abs_of_pos (sub_pos.mpr hab), abs_of_nonneg (by linarith)] at h
      linarith
    · by_contra! hcb
      rw [abs_of_nonpos (by linarith), abs_of_neg (sub_neg.mpr hcb)] at h
      linarith
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr hca)] at h
    constructor
    · by_contra! hcb
      rw [abs_of_nonneg (by linarith), abs_of_pos (sub_pos.mpr hcb)] at h
      linarith
    · by_contra! hab
      rw [abs_of_neg (sub_neg.mpr hab), abs_of_nonpos (by linarith)] at h
      linarith

/-- Ordered polar representations in one half-circle already imply betweenness. -/
noncomputable def forwardAngleLift_of_polar
    {V : Type*} [LinearOrder V] (p : V → Plane) (base : ℝ)
    (theta rho : V → V → ℝ)
    (hrho : ∀ {i j}, i < j → 0 < rho i j)
    (hlo : ∀ {i j}, i < j → base ≤ theta i j)
    (hhi : ∀ {i j}, i < j → theta i j < base + Real.pi)
    (hrep : ∀ {i j}, i < j → p j - p i = rho i j • rayDirection (theta i j)) :
    ForwardAngleLift p base where
  theta := theta
  rho := rho
  rho_pos := hrho
  theta_lower := hlo
  theta_upper := hhi
  repr := hrep
  between := by
    intro i j k hij hjk
    have hik := hij.trans hjk
    have hangle (u v w z : V) (huv : u < v) (hwz : w < z) :
        InnerProductGeometry.angle (p v - p u) (p z - p w) =
          |theta u v - theta w z| := by
      rw [hrep huv, hrep hwz,
        InnerProductGeometry.angle_smul_left_of_pos _ _ (hrho huv),
        InnerProductGeometry.angle_smul_right_of_pos _ _ (hrho hwz)]
      apply angle_rayDirection
      rw [abs_le]
      constructor <;> linarith [hlo huv, hlo hwz, hhi huv, hhi hwz]
    have hne : p k - p j ≠ 0 := by
      rw [hrep hjk]
      apply smul_ne_zero (ne_of_gt (hrho hjk))
      have hnorm := norm_rayDirection (theta j k)
      intro hzero
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    have hsum : (p j - p i) + (p k - p j) = p k - p i := by abel
    have h := InnerProductGeometry.angle_eq_angle_add_add_angle_add (p j - p i) hne
    rw [hsum, hangle i j j k hij hjk, hangle i j i k hij hik,
      hangle j k i k hjk hik] at h
    exact between_of_abs_add h

/-- Height order with left-to-right tie breaking gives a genuine closed-boundary
forward lift, without a generic-projection choice. -/
noncomputable def upperHalfPlaneForwardLift
    {V : Type*} [LinearOrder V] {p : V → Plane}
    (hp : Function.Injective p)
    (horder : ∀ i j, i < j → p i 1 ≤ p j 1 ∧ (p i 1 = p j 1 → p i 0 < p j 0)) :
    ForwardAngleLift p 0 := by
  let theta := fun i j ↦ (planeToComplex (p j - p i)).arg
  let rho := fun i j ↦ ‖planeToComplex (p j - p i)‖
  apply forwardAngleLift_of_polar p 0 theta rho
  · intro i j hij
    exact norm_pos_iff.mpr (planeToComplex_ne_zero (sub_ne_zero.mpr (hp.ne hij.ne')))
  · intro i j hij
    apply Complex.arg_nonneg_iff.mpr
    have h := (horder i j hij).1
    simpa [planeToComplex_apply, sub_apply] using sub_nonneg.mpr h
  · intro i j hij
    dsimp [theta]
    simp only [zero_add]
    apply Complex.arg_lt_pi_iff.mpr
    by_cases heq : p i 1 = p j 1
    · left
      have h := (horder i j hij).2 heq
      simpa [planeToComplex_apply, sub_apply] using (sub_pos.mpr h).le
    · right
      simpa [planeToComplex_apply, sub_apply] using sub_ne_zero.mpr (Ne.symm heq)
  · intro i j hij
    exact norm_smul_rayDirection_arg (sub_ne_zero.mpr (hp.ne hij.ne'))

/-- Coordinates for lexicographic height order. -/
noncomputable def heightCoordinates (p : V → Plane) (i : V) : ℝ ×ₗ ℝ :=
  toLex (p i 1, p i 0)

theorem heightCoordinates_injective {V : Type*} {p : V → Plane}
    (hp : Function.Injective p) : Function.Injective (heightCoordinates p) := by
  intro i j h
  apply hp
  have hpair := congrArg ofLex h
  have hy := congrArg Prod.fst hpair
  have hx := congrArg Prod.snd hpair
  ext c
  fin_cases c
  · exact hx
  · exact hy

@[instance_reducible]
noncomputable def heightLinearOrder {V : Type*} {p : V → Plane}
    (hp : Function.Injective p) : LinearOrder V :=
  LinearOrder.lift' (heightCoordinates p) (heightCoordinates_injective hp)

/-- The concrete coordinate order satisfies the hypotheses of the angular lift. -/
theorem heightLinearOrder_forward {V : Type*} {p : V → Plane}
    (hp : Function.Injective p) (i j : V) :
    letI := heightLinearOrder hp
    i < j → p i 1 ≤ p j 1 ∧ (p i 1 = p j 1 → p i 0 < p j 0) := by
  intro h
  change toLex (p i 1, p i 0) < toLex (p j 1, p j 0) at h
  rcases Prod.Lex.toLex_lt_toLex.mp h with h | ⟨heq, h⟩
  · exact ⟨h.le, fun heq ↦ False.elim (h.ne heq)⟩
  · exact ⟨heq.le, fun _ ↦ h⟩

#print axioms forwardAngleLift_of_polar
#print axioms upperHalfPlaneForwardLift
#print axioms heightCoordinates_injective
#print axioms heightLinearOrder_forward

end JSP000404Research
