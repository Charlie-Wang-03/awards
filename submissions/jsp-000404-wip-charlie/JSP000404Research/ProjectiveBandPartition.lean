
import JSP000404Research.ProjectiveBandSignRigidity
import JSP000404Research.BinaryEdgePartition
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Direct projective-band binary edge partition

The generic-projection OrderedEdgeColoring is useful for residual recursion,
but it is not needed to construct the first global partial code.

At every vertex, canonical projective rays have parameters theta in [0,pi).
Under Sendov normalization lambda=pi/t, use the normalized coordinate

  x = t*theta/pi.

If t<n+1, every edge lies in one of the n+1 half-open unit bands.

ProjectiveBandSignRigidity shows that at a fixed vertex every ray in one such
band has the same canonical sign.  Therefore the sign is a well-defined
Boolean bit of the vertex/band pair.

CanonicalRayReversal shows that an undirected edge has the same projective
parameter at both endpoints and opposite canonical signs.  Hence its band
coordinate separates its two endpoint bits.

This yields a genuine BinaryEdgePartition with n+1 coordinates directly in
the same projective coordinate system used by CentreProjectiveCycle.
-/

namespace JSP000404Research

open Real

def RayInProjectiveBand
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ) (i : V) (j : OtherVertex i)
    {k : ℕ} (c : Fin k) : Prop :=
  (c : ℝ) ≤ normalizedRayTheta hp t i j ∧
    normalizedRayTheta hp t i j < (c : ℝ) + 1

theorem rayInProjectiveBand_floor
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 ≤ t)
    (i : V) (j : OtherVertex i) :
    let q := Nat.floor (normalizedRayTheta hp t i j)
    (q : ℝ) ≤ normalizedRayTheta hp t i j ∧
      normalizedRayTheta hp t i j < (q : ℝ) + 1 := by
  dsimp
  constructor
  · exact Nat.floor_le
      (normalizedRayTheta_nonneg hp ht i j)
  · exact Nat.lt_floor_add_one _

noncomputable def projectiveBandBit
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (n : ℕ)
    (i : V) (c : Fin (n + 1)) : Bool :=
  decide (∃ j : OtherVertex i,
    RayInProjectiveBand hp t i j c ∧
      raySignAt hp i j = true)

/-- The band bit equals the sign of every ray in that band. -/
theorem projectiveBandBit_eq_raySignAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (n : ℕ)
    (i : V) (c : Fin (n + 1))
    (j : OtherVertex i)
    (hj : RayInProjectiveBand hp t i j c) :
    projectiveBandBit hp hcap ht hlam n i c =
      raySignAt hp i j := by
  classical
  by_cases hs : raySignAt hp i j = true
  · have hex :
        ∃ k : OtherVertex i,
          RayInProjectiveBand hp t i k c ∧
            raySignAt hp i k = true :=
      ⟨j, hj, hs⟩
    simp [projectiveBandBit, hex, hs]
  · have hsj : raySignAt hp i j = false := by
      cases h : raySignAt hp i j <;> simp_all
    have hnot :
        ¬ ∃ k : OtherVertex i,
          RayInProjectiveBand hp t i k c ∧
            raySignAt hp i k = true := by
      rintro ⟨k, hk, hkTrue⟩
      by_cases hkj : k = j
      · subst k
        rw [hsj] at hkTrue
        simp at hkTrue
      · have hsame :=
          raySignAt_eq_of_same_projective_band
            hp hcap ht hlam i k j hkj
            hk.1 hk.2 hj.1 hj.2
        rw [hkTrue, hsj] at hsame
        simp at hsame
    simp [projectiveBandBit, hnot, hsj]

noncomputable def projectiveBandColor
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    V → V → Fin (n + 1) := by
  intro u v
  by_cases huv : u = v
  · exact ⟨0, Nat.succ_pos n⟩
  · let j : OtherVertex u := ⟨v, huv.symm⟩
    let q := Nat.floor (normalizedRayTheta hp t u j)
    have hx0 :
        0 ≤ normalizedRayTheta hp t u j :=
      normalizedRayTheta_nonneg hp ht.le u j
    have hxt :
        normalizedRayTheta hp t u j < t :=
      normalizedRayTheta_lt_t hp ht u j
    have hxN :
        normalizedRayTheta hp t u j < ((n + 1 : ℕ) : ℝ) := by
      exact hxt.trans (by exact_mod_cast htop)
    have hq : q < n + 1 :=
      (Nat.floor_lt hx0).2 (by simpa using hxN)
    exact ⟨q, hq⟩

theorem projectiveBandColor_val
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    (projectiveBandColor hp ht n htop u v).val =
      Nat.floor
        (normalizedRayTheta hp t u ⟨v, huv.symm⟩) := by
  unfold projectiveBandColor
  simp [huv]

/-- The edge's projective band contains its ray at the lower endpoint. -/
theorem projectiveBandColor_mem_lower
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    RayInProjectiveBand hp t u ⟨v, huv.symm⟩
      (projectiveBandColor hp ht n htop u v) := by
  have hband :=
    rayInProjectiveBand_floor
      hp ht.le u ⟨v, huv.symm⟩
  rw [projectiveBandColor_val hp ht n htop huv]
  exact hband

/-- The same edge band contains the reversed ray at the other endpoint. -/
theorem projectiveBandColor_mem_upper
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v) :
    RayInProjectiveBand hp t v ⟨u, huv⟩
      (projectiveBandColor hp ht n htop u v) := by
  have hlower :=
    projectiveBandColor_mem_lower
      hp ht n htop huv
  have htheta :
      rayThetaAt hp v ⟨u, huv⟩ =
        rayThetaAt hp u ⟨v, huv.symm⟩ :=
    (rayThetaAt_reverse_eq hp huv).symm
  unfold RayInProjectiveBand at hlower ⊢
  unfold normalizedRayTheta at hlower ⊢
  rw [htheta]
  exact hlower

/-- Direct n+1-coordinate projective-band binary edge partition. -/
noncomputable def projectiveBandPartition
    {V : Type*} [LinearOrder V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    BinaryEdgePartition V (n + 1) where
  edgeColor :=
    projectiveBandColor hp ht n htop
  bit :=
    projectiveBandBit hp hcap ht hlam n
  proper := by
    intro u v huv
    have huvNe : u ≠ v := ne_of_lt huv
    let c :=
      projectiveBandColor hp ht n htop u v
    let uv : OtherVertex u := ⟨v, huvNe.symm⟩
    let vu : OtherVertex v := ⟨u, huvNe⟩
    have hcU :
        RayInProjectiveBand hp t u uv c := by
      simpa [c, uv] using
        projectiveBandColor_mem_lower
          hp ht n htop huvNe
    have hcV :
        RayInProjectiveBand hp t v vu c := by
      simpa [c, vu] using
        projectiveBandColor_mem_upper
          hp ht n htop huvNe
    have hbitU :
        projectiveBandBit hp hcap ht hlam n u c =
          raySignAt hp u uv :=
      projectiveBandBit_eq_raySignAt
        hp hcap ht hlam n u c uv hcU
    have hbitV :
        projectiveBandBit hp hcap ht hlam n v c =
          raySignAt hp v vu :=
      projectiveBandBit_eq_raySignAt
        hp hcap ht hlam n v c vu hcV
    have hrev :
        raySignAt hp v vu =
          ! raySignAt hp u uv := by
      simpa [uv, vu] using
        raySignAt_reverse_eq_not hp huvNe
    rw [hbitU, hbitV, hrev]
    cases h : raySignAt hp u uv <;> decide

#print axioms projectiveBandBit_eq_raySignAt
#print axioms projectiveBandColor_mem_upper
#print axioms projectiveBandPartition

end JSP000404Research
