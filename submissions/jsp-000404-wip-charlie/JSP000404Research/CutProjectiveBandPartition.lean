import JSP000404Research.ProjectiveBandPartition
import JSP000404Research.SignedRayAngle
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Direct projective-band partition at an arbitrary projective cut

The canonical cut at theta=0 is not geometrically distinguished.  For any
cut c in [0,pi), rotate the projective representative into [0,pi) by

  theta_c =
    theta + pi - c,  theta < c,
    theta - c,       c <= theta.

Crossing the projective cut also flips the signed-ray Boolean:

  sigma_c = !sigma,  theta < c,
            sigma,   c <= theta.

Then the original displacement representation is unchanged when written as

  rho * signedRayDirection sigma_c (c + theta_c).

Under the global angle cap, all adjusted signs in one rotated unit band are
equal.  Reversing an edge preserves theta_c and flips sigma_c, so the usual
band/sign construction yields a genuine BinaryEdgePartition with n+1
coordinates for every cut.
-/

namespace JSP000404Research

open Real

noncomputable def cutRayTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V) (j : OtherVertex i) : ℝ :=
  if rayThetaAt hp i j < c then
    rayThetaAt hp i j + Real.pi - c
  else
    rayThetaAt hp i j - c

noncomputable def cutRaySign
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V) (j : OtherVertex i) : Bool :=
  if rayThetaAt hp i j < c then
    !raySignAt hp i j
  else
    raySignAt hp i j

def cutNormalizedRayTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V) (j : OtherVertex i) : ℝ :=
  t * cutRayTheta hp c i j / Real.pi

theorem cutRayTheta_nonneg
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c : ℝ} (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i) :
    0 ≤ cutRayTheta hp c i j := by
  unfold cutRayTheta
  split_ifs with h
  · have htheta0 := rayThetaAt_nonneg hp i j
    linarith
  · have hthetaC : c ≤ rayThetaAt hp i j := le_of_not_gt h
    linarith

theorem cutRayTheta_lt_pi
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c : ℝ} (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i) :
    cutRayTheta hp c i j < Real.pi := by
  unfold cutRayTheta
  split_ifs with h
  · linarith
  · have hthetaPi := rayThetaAt_lt_pi hp i j
    linarith

theorem cutNormalizedRayTheta_nonneg
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 ≤ t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i) :
    0 ≤ cutNormalizedRayTheta hp t c i j := by
  unfold cutNormalizedRayTheta
  positivity

theorem cutNormalizedRayTheta_lt_t
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i) :
    cutNormalizedRayTheta hp t c i j < t := by
  unfold cutNormalizedRayTheta
  have htheta := cutRayTheta_lt_pi hp hc0 hcpi i j
  nlinarith [Real.pi_pos]

theorem cutNormalizedRayTheta_eq_div_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V) (j : OtherVertex i) :
    cutNormalizedRayTheta hp t c i j =
      cutRayTheta hp c i j / lam := by
  unfold cutNormalizedRayTheta
  rw [hlam]
  field_simp [ne_of_gt ht, Real.pi_ne_zero]
  ring

/-- The cut-adjusted signed parameter represents the same actual ray. -/
theorem cutRayRepAt_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V) (j : OtherVertex i) :
    p j.1 - p i =
      rayRhoAt hp i j •
        signedRayDirection
          (cutRaySign hp c i j)
          (c + cutRayTheta hp c i j) := by
  rw [rayRepAt_eq hp i j]
  unfold cutRayTheta cutRaySign
  split_ifs with h
  · have hparam :
        c + (rayThetaAt hp i j + Real.pi - c) =
          rayThetaAt hp i j + Real.pi := by ring
    rw [hparam, signedRayDirection_not_add_pi]
  · congr 2
    ring

/-- Same rotated unit band forces the adjusted cut signs to agree. -/
theorem cutRaySign_eq_of_same_band
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j k : OtherVertex i)
    (hjk : j ≠ k)
    {m : ℕ}
    (hjm : (m : ℝ) ≤ cutNormalizedRayTheta hp t c i j)
    (hjM : cutNormalizedRayTheta hp t c i j < (m : ℝ) + 1)
    (hkm : (m : ℝ) ≤ cutNormalizedRayTheta hp t c i k)
    (hkM : cutNormalizedRayTheta hp t c i k < (m : ℝ) + 1) :
    cutRaySign hp c i j = cutRaySign hp c i k := by
  by_contra hsign
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  have hnorm :=
    abs_sub_lt_one_of_same_unit_band
      hjm hjM hkm hkM
  rw [cutNormalizedRayTheta_eq_div_lam hp ht hlam i j,
      cutNormalizedRayTheta_eq_div_lam hp ht hlam i k] at hnorm
  have hsmall :
      |cutRayTheta hp c i j - cutRayTheta hp c i k| < lam := by
    have hdiv :
        |(cutRayTheta hp c i j -
            cutRayTheta hp c i k) / lam| < 1 := by
      have h :
          cutRayTheta hp c i j / lam -
              cutRayTheta hp c i k / lam =
            (cutRayTheta hp c i j -
              cutRayTheta hp c i k) / lam := by ring
      rw [h] at hnorm
      exact hnorm
    rw [abs_div, abs_of_pos hlamPos] at hdiv
    exact (div_lt_one hlamPos).1 hdiv
  have hdiff :
      |(c + cutRayTheta hp c i j) -
        (c + cutRayTheta hp c i k)| ≤ Real.pi := by
    have hj0 := cutRayTheta_nonneg hp hc0 hcpi i j
    have hk0 := cutRayTheta_nonneg hp hc0 hcpi i k
    have hjpi := cutRayTheta_lt_pi hp hc0 hcpi i j
    have hkpi := cutRayTheta_lt_pi hp hc0 hcpi i k
    rw [show
      (c + cutRayTheta hp c i j) -
          (c + cutRayTheta hp c i k) =
        cutRayTheta hp c i j - cutRayTheta hp c i k by ring]
    rw [abs_le]
    constructor <;> linarith
  have hcapJK :
      EuclideanGeometry.angle (p j.1) (p i) (p k.1)
        ≤ Real.pi - lam :=
    hcap j.1 i k.1 j.2
      (otherVertex_val_ne hjk) k.2.symm
  change
    InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i)
      ≤ Real.pi - lam at hcapJK
  rw [cutRayRepAt_eq hp c i j,
      cutRayRepAt_eq hp c i k,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i j)
        (rayRhoAt_pos hp i k),
      angle_signedRayDirection_eq_pi_sub_of_sign_ne
        hsign hdiff] at hcapJK
  have habs :
      |(c + cutRayTheta hp c i j) -
          (c + cutRayTheta hp c i k)| =
        |cutRayTheta hp c i j -
          cutRayTheta hp c i k| := by
    congr 1
    ring
  rw [habs] at hcapJK
  linarith

theorem cutRayTheta_reverse_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) {u v : V} (huv : u ≠ v) :
    cutRayTheta hp c v ⟨u, huv⟩ =
      cutRayTheta hp c u ⟨v, huv.symm⟩ := by
  unfold cutRayTheta
  have htheta :
      rayThetaAt hp v ⟨u, huv⟩ =
        rayThetaAt hp u ⟨v, huv.symm⟩ :=
    (rayThetaAt_reverse_eq hp huv).symm
  rw [htheta]

theorem cutRaySign_reverse_eq_not
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) {u v : V} (huv : u ≠ v) :
    cutRaySign hp c v ⟨u, huv⟩ =
      !cutRaySign hp c u ⟨v, huv.symm⟩ := by
  unfold cutRaySign
  have htheta :
      rayThetaAt hp v ⟨u, huv⟩ =
        rayThetaAt hp u ⟨v, huv.symm⟩ :=
    (rayThetaAt_reverse_eq hp huv).symm
  rw [htheta]
  have hsign :
      raySignAt hp v ⟨u, huv⟩ =
        !raySignAt hp u ⟨v, huv.symm⟩ := by
    simpa using raySignAt_reverse_eq_not hp huv
  split_ifs <;> rw [hsign] <;>
    cases raySignAt hp u ⟨v, huv.symm⟩ <;> decide

def RayInCutProjectiveBand
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V) (j : OtherVertex i)
    {k : ℕ} (b : Fin k) : Prop :=
  (b : ℝ) ≤ cutNormalizedRayTheta hp t c i j ∧
    cutNormalizedRayTheta hp t c i j < (b : ℝ) + 1

noncomputable def cutProjectiveBandBit
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (i : V) (b : Fin (n + 1)) : Bool :=
  decide (∃ j : OtherVertex i,
    RayInCutProjectiveBand hp t c i j b ∧
      cutRaySign hp c i j = true)

theorem cutProjectiveBandBit_eq_cutRaySign
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (i : V) (b : Fin (n + 1))
    (j : OtherVertex i)
    (hj : RayInCutProjectiveBand hp t c i j b) :
    cutProjectiveBandBit hp hcap ht hlam hc0 hcpi n i b =
      cutRaySign hp c i j := by
  classical
  by_cases hs : cutRaySign hp c i j = true
  · have hex :
        ∃ k : OtherVertex i,
          RayInCutProjectiveBand hp t c i k b ∧
            cutRaySign hp c i k = true :=
      ⟨j, hj, hs⟩
    simp [cutProjectiveBandBit, hex, hs]
  · have hsj : cutRaySign hp c i j = false := by
      cases h : cutRaySign hp c i j <;> simp_all
    have hnot :
        ¬ ∃ k : OtherVertex i,
          RayInCutProjectiveBand hp t c i k b ∧
            cutRaySign hp c i k = true := by
      rintro ⟨k, hk, hkTrue⟩
      by_cases hkj : k = j
      · subst k
        rw [hsj] at hkTrue
        simp at hkTrue
      · have hsame :=
          cutRaySign_eq_of_same_band
            hp hcap ht hlam hc0 hcpi i k j hkj
            hk.1 hk.2 hj.1 hj.2
        rw [hkTrue, hsj] at hsame
        simp at hsame
    simp [cutProjectiveBandBit, hnot, hsj]

noncomputable def cutProjectiveBandColor
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    V → V → Fin (n + 1) := by
  intro u v
  by_cases huv : u = v
  · exact ⟨0, Nat.succ_pos n⟩
  · let j : OtherVertex u := ⟨v, huv.symm⟩
    let q := Nat.floor (cutNormalizedRayTheta hp t c u j)
    have hx0 :
        0 ≤ cutNormalizedRayTheta hp t c u j :=
      cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi u j
    have hxt :
        cutNormalizedRayTheta hp t c u j < t :=
      cutNormalizedRayTheta_lt_t hp ht hc0 hcpi u j
    have hxN :
        cutNormalizedRayTheta hp t c u j <
          ((n + 1 : ℕ) : ℝ) :=
      hxt.trans (by exact_mod_cast htop)
    have hq : q < n + 1 :=
      (Nat.floor_lt hx0).2 (by simpa using hxN)
    exact ⟨q, hq⟩

theorem cutProjectiveBandColor_val
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    (cutProjectiveBandColor hp ht hc0 hcpi n htop u v).val =
      Nat.floor
        (cutNormalizedRayTheta hp t c u ⟨v, huv.symm⟩) := by
  unfold cutProjectiveBandColor
  simp [huv]

theorem cutProjectiveBandColor_mem_lower
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    RayInCutProjectiveBand hp t c u ⟨v, huv.symm⟩
      (cutProjectiveBandColor hp ht hc0 hcpi n htop u v) := by
  unfold RayInCutProjectiveBand
  rw [cutProjectiveBandColor_val
      hp ht hc0 hcpi n htop huv]
  exact ⟨
    Nat.floor_le
      (cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi u
        ⟨v, huv.symm⟩),
    Nat.lt_floor_add_one _⟩

theorem cutProjectiveBandColor_symm
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    cutProjectiveBandColor hp ht hc0 hcpi n htop u v =
      cutProjectiveBandColor hp ht hc0 hcpi n htop v u := by
  apply Fin.ext
  rw [cutProjectiveBandColor_val
      hp ht hc0 hcpi n htop huv,
      cutProjectiveBandColor_val
      hp ht hc0 hcpi n htop huv.symm]
  unfold cutNormalizedRayTheta
  rw [cutRayTheta_reverse_eq hp c huv]

/-- The same cut band contains the reversed ray at the other endpoint. -/
theorem cutProjectiveBandColor_mem_upper
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    RayInCutProjectiveBand hp t c v ⟨u, huv⟩
      (cutProjectiveBandColor hp ht hc0 hcpi n htop u v) := by
  have hlower :=
    cutProjectiveBandColor_mem_lower
      hp ht hc0 hcpi n htop huv
  have htheta :
      cutNormalizedRayTheta hp t c v ⟨u, huv⟩ =
        cutNormalizedRayTheta hp t c u ⟨v, huv.symm⟩ := by
    unfold cutNormalizedRayTheta
    rw [cutRayTheta_reverse_eq hp c huv]
  unfold RayInCutProjectiveBand at hlower ⊢
  rw [htheta]
  exact hlower

/-- Rotated projective-band binary edge partition. -/
noncomputable def cutProjectiveBandPartition
    {V : Type*} [LinearOrder V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    BinaryEdgePartition V (n + 1) where
  edgeColor :=
    cutProjectiveBandColor hp ht hc0 hcpi n htop
  bit :=
    cutProjectiveBandBit hp hcap ht hlam hc0 hcpi n
  proper := by
    intro u v huv
    have huvNe : u ≠ v := ne_of_lt huv
    let b :=
      cutProjectiveBandColor hp ht hc0 hcpi n htop u v
    let uv : OtherVertex u := ⟨v, huvNe.symm⟩
    let vu : OtherVertex v := ⟨u, huvNe⟩
    have hbU :
        RayInCutProjectiveBand hp t c u uv b := by
      have hval :=
        cutProjectiveBandColor_val
          hp ht hc0 hcpi n htop huvNe
      unfold RayInCutProjectiveBand
      rw [hval]
      exact ⟨
        Nat.floor_le
          (cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi u uv),
        Nat.lt_floor_add_one _⟩
    have htheta :
        cutRayTheta hp c v vu =
          cutRayTheta hp c u uv :=
      cutRayTheta_reverse_eq hp c huvNe
    have hnorm :
        cutNormalizedRayTheta hp t c v vu =
          cutNormalizedRayTheta hp t c u uv := by
      unfold cutNormalizedRayTheta
      rw [htheta]
    have hbV :
        RayInCutProjectiveBand hp t c v vu b := by
      unfold RayInCutProjectiveBand at hbU ⊢
      rw [hnorm]
      exact hbU
    have hbitU :
        cutProjectiveBandBit hp hcap ht hlam hc0 hcpi n u b =
          cutRaySign hp c u uv :=
      cutProjectiveBandBit_eq_cutRaySign
        hp hcap ht hlam hc0 hcpi n u b uv hbU
    have hbitV :
        cutProjectiveBandBit hp hcap ht hlam hc0 hcpi n v b =
          cutRaySign hp c v vu :=
      cutProjectiveBandBit_eq_cutRaySign
        hp hcap ht hlam hc0 hcpi n v b vu hbV
    have hrev :
        cutRaySign hp c v vu =
          !cutRaySign hp c u uv :=
      cutRaySign_reverse_eq_not hp c huvNe
    rw [hbitU, hbitV, hrev]
    cases h : cutRaySign hp c u uv <;> decide

#print axioms cutRayRepAt_eq
#print axioms cutRaySign_eq_of_same_band
#print axioms cutRaySign_reverse_eq_not
#print axioms cutProjectiveBandPartition

end JSP000404Research
