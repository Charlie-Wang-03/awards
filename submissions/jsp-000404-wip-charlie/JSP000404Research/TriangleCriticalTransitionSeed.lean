import JSP000404Research.TriangleSignParity
import JSP000404Research.CanonicalSignGap
import JSP000404Research.CanonicalRayReversal
import Mathlib.Tactic

/-!
# Critical transition seed inside an ordinary triangle direction arc

Let i,j,k be three distinct planar vertices.  Use the canonical projective
direction of each unoriented edge, normalized by the Sendov scale t:

  x_ij = t * theta_ij / pi,
  x_ik = t * theta_ik / pi,
  x_jk = t * theta_jk / pi.

Assume all three directions lie in one ordinary lifted interval [L,L+S].
Canonical sign parity on a triangle says that at least one triangle vertex
sees its two incident edge rays with opposite canonical signs.

At such a transition vertex the global angle cap forces the projective
separation to contain at least one full cap unit.  Since both endpoint edge
directions lie inside the parent interval, the same separation is at most S.

Thus every ordinary short triangle-direction arc contains a transition seed
of normalized width s with

  1 <= s <= S.

This is the local geometric input needed before refining the seed through
intermediate rays to an adjacent critical q=1 gap.
-/

namespace JSP000404Research

open Real

/-- Normalized canonical projective direction of one oriented non-loop edge.
Reversal leaves this number unchanged. -/
noncomputable def normalizedEdgeTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ)
    (i j : V)
    (hij : i ≠ j) : ℝ :=
  t * (rayThetaAt hp i
    (⟨j, hij.symm⟩ : OtherVertex i) / Real.pi)

theorem normalizedEdgeTheta_reverse
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ)
    {i j : V}
    (hij : i ≠ j) :
    normalizedEdgeTheta hp t i j hij =
      normalizedEdgeTheta hp t j i hij.symm := by
  unfold normalizedEdgeTheta
  rw [rayThetaAt_reverse_eq hp hij]

/-- Opposite canonical signs force at least one normalized unit of absolute
projective separation, without choosing which endpoint is theta-smaller. -/
theorem one_le_normalized_abs_gap_of_canonical_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k) :
    1 ≤
      t * (|rayThetaAt hp i j - rayThetaAt hp i k| /
        Real.pi) := by
  rcases le_total
      (rayThetaAt hp i j) (rayThetaAt hp i k)
    with horder | horder
  · have h :=
      one_le_t_mul_gap_of_canonical_sign_ne
        hp hcap ht hlam i hjk horder hsign
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  · have h :=
      one_le_t_mul_gap_of_canonical_sign_ne
        hp hcap ht hlam i hjk.symm horder hsign.symm
    rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact h

/-- If two normalized edge directions lie in one interval of width S, their
absolute difference is at most S. -/
theorem abs_sub_le_width_of_mem_interval
    {x y L S : ℝ}
    (hx : L ≤ x ∧ x ≤ L + S)
    (hy : L ≤ y ∧ y ≤ L + S) :
    |x - y| ≤ S := by
  rw [abs_le]
  constructor <;> linarith

/-- Normalized separation expressed either by subtracting normalized edge
coordinates or by scaling the canonical theta difference. -/
theorem abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ}
    (ht : 0 ≤ t)
    (i : V)
    {j k : V}
    (hij : i ≠ j)
    (hik : i ≠ k) :
    |normalizedEdgeTheta hp t i j hij -
        normalizedEdgeTheta hp t i k hik|
      =
    t * (
      |rayThetaAt hp i (⟨j, hij.symm⟩ : OtherVertex i) -
        rayThetaAt hp i (⟨k, hik.symm⟩ : OtherVertex i)| /
        Real.pi) := by
  unfold normalizedEdgeTheta
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [← mul_sub]
  rw [abs_mul, abs_of_nonneg ht]
  have hdiv :
      rayThetaAt hp i (⟨j, hij.symm⟩ : OtherVertex i) / Real.pi -
          rayThetaAt hp i (⟨k, hik.symm⟩ : OtherVertex i) / Real.pi
        =
      (rayThetaAt hp i (⟨j, hij.symm⟩ : OtherVertex i) -
          rayThetaAt hp i (⟨k, hik.symm⟩ : OtherVertex i)) /
        Real.pi := by
    ring
  rw [hdiv, abs_div, abs_of_pos hpi]
  ring

/-- Ordinary parent-arc transition seed for a triangle.

The conclusion records which one of the three triangle vertices carries the
transition.  In every branch the transition separation is between one and the
parent arc width S. -/
theorem triangle_has_critical_transition_seed_in_ordinary_arc
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t L S : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    {i j k : V}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hijArc :
      L ≤ normalizedEdgeTheta hp t i j hij ∧
      normalizedEdgeTheta hp t i j hij ≤ L + S)
    (hikArc :
      L ≤ normalizedEdgeTheta hp t i k hik ∧
      normalizedEdgeTheta hp t i k hik ≤ L + S)
    (hjkArc :
      L ≤ normalizedEdgeTheta hp t j k hjk ∧
      normalizedEdgeTheta hp t j k hjk ≤ L + S) :
    (
      raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) ≠
        raySignAt hp i (⟨k, hik.symm⟩ : OtherVertex i)
      ∧
      1 ≤
        |normalizedEdgeTheta hp t i j hij -
          normalizedEdgeTheta hp t i k hik|
      ∧
      |normalizedEdgeTheta hp t i j hij -
          normalizedEdgeTheta hp t i k hik| ≤ S
    )
    ∨
    (
      raySignAt hp j (⟨i, hij⟩ : OtherVertex j) ≠
        raySignAt hp j (⟨k, hjk.symm⟩ : OtherVertex j)
      ∧
      1 ≤
        |normalizedEdgeTheta hp t i j hij -
          normalizedEdgeTheta hp t j k hjk|
      ∧
      |normalizedEdgeTheta hp t i j hij -
          normalizedEdgeTheta hp t j k hjk| ≤ S
    )
    ∨
    (
      raySignAt hp k (⟨i, hik⟩ : OtherVertex k) ≠
        raySignAt hp k (⟨j, hjk⟩ : OtherVertex k)
      ∧
      1 ≤
        |normalizedEdgeTheta hp t i k hik -
          normalizedEdgeTheta hp t j k hjk|
      ∧
      |normalizedEdgeTheta hp t i k hik -
          normalizedEdgeTheta hp t j k hjk| ≤ S
    ) := by
  let sij :=
    raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i)
  let sik :=
    raySignAt hp i (⟨k, hik.symm⟩ : OtherVertex i)
  by_cases hi : sij ≠ sik
  · left
    refine ⟨hi, ?_, abs_sub_le_width_of_mem_interval hijArc hikArc⟩
    rw [abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
      hp ht.le i hij hik]
    exact one_le_normalized_abs_gap_of_canonical_sign_ne
      hp hcap ht hlam i
      (by
        intro h
        apply hjk
        exact congrArg Subtype.val h)
      hi
  · have hiEq : sij = sik := not_ne_iff.mp hi
    have hpar :=
      triangle_exactly_one_other_sign_transition
        hp hij hik hjk (by simpa [sij, sik] using hiEq)
    rcases hpar with hjTrans | hkTrans
    · right
      left
      refine ⟨hjTrans.1, ?_,
        abs_sub_le_width_of_mem_interval hijArc hjkArc⟩
      have hsep :
          |normalizedEdgeTheta hp t i j hij -
              normalizedEdgeTheta hp t j k hjk|
            =
          t * (
            |rayThetaAt hp j
                (⟨i, hij⟩ : OtherVertex j) -
              rayThetaAt hp j
                (⟨k, hjk.symm⟩ : OtherVertex j)| /
              Real.pi) := by
        rw [normalizedEdgeTheta_reverse hp t hij]
        exact abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
          hp ht.le j hij.symm hjk
      rw [hsep]
      exact one_le_normalized_abs_gap_of_canonical_sign_ne
        hp hcap ht hlam j
        (by
          intro h
          apply hik
          exact congrArg Subtype.val h)
        hjTrans.1
    · right
      right
      refine ⟨hkTrans.2, ?_,
        abs_sub_le_width_of_mem_interval hikArc hjkArc⟩
      have hsep :
          |normalizedEdgeTheta hp t i k hik -
              normalizedEdgeTheta hp t j k hjk|
            =
          t * (
            |rayThetaAt hp k
                (⟨i, hik⟩ : OtherVertex k) -
              rayThetaAt hp k
                (⟨j, hjk⟩ : OtherVertex k)| /
              Real.pi) := by
        rw [normalizedEdgeTheta_reverse hp t hik,
            normalizedEdgeTheta_reverse hp t hjk]
        exact abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
          hp ht.le k hik.symm hjk.symm
      rw [hsep]
      exact one_le_normalized_abs_gap_of_canonical_sign_ne
        hp hcap ht hlam k
        (by
          intro h
          apply hij
          exact congrArg Subtype.val h)
        hkTrans.2

#print axioms normalizedEdgeTheta_reverse
#print axioms one_le_normalized_abs_gap_of_canonical_sign_ne
#print axioms triangle_has_critical_transition_seed_in_ordinary_arc

end JSP000404Research
