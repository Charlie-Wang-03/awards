import JSP000404Research.CentreRayIndex
import JSP000404Research.CanonicalSignGap
import Mathlib.Data.Finset.Min
import Mathlib.Tactic

/-!
# Refining an ordered transition seed to an adjacent transition

Let j,k be two rays in one theta-sorted CentreProjectiveCycle with

  theta(j) < theta(k)

and opposite canonical signs.

Among ray indices strictly after j and no later than k, choose the first index
whose sign differs from sign(j).  This set is nonempty because it contains k.

If r is that first changed-sign index, then r has a predecessor q.  Minimality
forces q to retain sign(j), hence q,r form an actual adjacent sign transition.
Moreover

  j <= q < r <= k,

so the adjacent projective gap is no wider than the original seed gap.
The global angle cap forces every adjacent sign transition to have normalized
width at least one.

Thus any ordered transition seed refines in one shot to an adjacent critical
transition gap nested inside it.
-/

namespace JSP000404Research
namespace CentreProjectiveCycle

open Real

noncomputable def firstChangedSignIndices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (j k : OtherVertex i) :
    Finset (Fin C.rays.length) := by
  classical
  exact Finset.univ.filter fun r =>
    C.rayIndex j < r ∧
    r ≤ C.rayIndex k ∧
    raySignAt hp i (C.rays.get r) ≠ raySignAt hp i j

theorem rayIndex_k_mem_firstChangedSignIndices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (htheta : rayThetaAt hp i j < rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k) :
    C.rayIndex k ∈ C.firstChangedSignIndices j k := by
  classical
  simp [firstChangedSignIndices,
    C.rayIndex_lt_of_theta_lt htheta]
  simpa [C.get_rayIndex] using hsign.symm

/-- Main adjacent-refinement theorem. -/
theorem exists_adjacent_transition_inside_ordered_seed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    {j k : OtherVertex i}
    (htheta : rayThetaAt hp i j < rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k) :
    ∃ q r : Fin C.rays.length,
      r.val = q.val + 1 ∧
      C.rayIndex j ≤ q ∧
      r ≤ C.rayIndex k ∧
      raySignAt hp i (C.rays.get q) ≠
        raySignAt hp i (C.rays.get r) ∧
      1 ≤
        t * ((rayThetaAt hp i (C.rays.get r) -
          rayThetaAt hp i (C.rays.get q)) / Real.pi) ∧
      t * ((rayThetaAt hp i (C.rays.get r) -
          rayThetaAt hp i (C.rays.get q)) / Real.pi)
        ≤
      t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) := by
  classical
  let S := C.firstChangedSignIndices j k
  have hSne : S.Nonempty := by
    exact ⟨C.rayIndex k,
      C.rayIndex_k_mem_firstChangedSignIndices
        htheta hsign⟩
  let r : Fin C.rays.length := S.min' hSne
  have hrS : r ∈ S := Finset.min'_mem S hSne
  have hrData :
      C.rayIndex j < r ∧
      r ≤ C.rayIndex k ∧
      raySignAt hp i (C.rays.get r) ≠
        raySignAt hp i j := by
    simpa [S, firstChangedSignIndices] using hrS
  have hrPos : 0 < r.val := by
    have hjr : (C.rayIndex j).val < r.val := hrData.1
    omega
  let q : Fin C.rays.length :=
    ⟨r.val - 1, by
      have hrlt := r.isLt
      omega⟩
  have hqrVal : r.val = q.val + 1 := by
    dsimp [q]
    omega
  have hqLtR : q < r := by
    exact Fin.mk_lt_mk.mpr (by
      dsimp [q]
      omega)
  have hjLeQ : C.rayIndex j ≤ q := by
    exact Fin.mk_le_mk.mpr (by
      have hjr : (C.rayIndex j).val < r.val := hrData.1
      dsimp [q]
      omega)
  have hqSign :
      raySignAt hp i (C.rays.get q) =
        raySignAt hp i j := by
    by_contra hne
    by_cases hjq : C.rayIndex j = q
    · have hget :
          C.rays.get q = j := by
        rw [← hjq, C.get_rayIndex]
      exact hne (by rw [hget])
    · have hjLtQ : C.rayIndex j < q :=
        lt_of_le_of_ne hjLeQ hjq
      have hqLeK : q ≤ C.rayIndex k :=
        hqLtR.le.trans hrData.2.1
      have hqS : q ∈ S := by
        simp [S, firstChangedSignIndices,
          hjLtQ, hqLeK, hne]
      have hrLeQ : r ≤ q :=
        Finset.min'_le S q hqS
      exact (not_lt_of_ge hrLeQ) hqLtR
  have htransition :
      raySignAt hp i (C.rays.get q) ≠
        raySignAt hp i (C.rays.get r) := by
    rw [hqSign]
    exact hrData.2.2.symm
  have hthetaQR :
      rayThetaAt hp i (C.rays.get q) ≤
        rayThetaAt hp i (C.rays.get r) :=
    C.theta_sorted.rel_get_of_lt hqLtR
  have hqNeR : C.rays.get q ≠ C.rays.get r := by
    intro h
    have := C.nodup.get_injective q r h
    exact (ne_of_lt hqLtR) this
  have hlower :=
    one_le_t_mul_gap_of_canonical_sign_ne
      hp hcap ht hlam i
      hqNeR hthetaQR htransition
  have hthetaJQ :
      rayThetaAt hp i j ≤
        rayThetaAt hp i (C.rays.get q) := by
    have h := C.theta_le_of_rayIndex_le hjLeQ
    simpa [C.get_rayIndex] using h
  have hthetaRK :
      rayThetaAt hp i (C.rays.get r) ≤
        rayThetaAt hp i k := by
    have h := C.theta_le_of_rayIndex_le hrData.2.1
    simpa [C.get_rayIndex] using h
  have hgapLe :
      rayThetaAt hp i (C.rays.get r) -
          rayThetaAt hp i (C.rays.get q)
        ≤
      rayThetaAt hp i k - rayThetaAt hp i j := by
    linarith
  have hscale :
      t * ((rayThetaAt hp i (C.rays.get r) -
          rayThetaAt hp i (C.rays.get q)) / Real.pi)
        ≤
      t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hdiv :=
      div_le_div_of_nonneg_right hgapLe hpi.le
    exact mul_le_mul_of_nonneg_left hdiv ht.le
  exact ⟨q, r, hqrVal, hjLeQ, hrData.2.1,
    htransition, hlower, hscale⟩

#print axioms rayIndex_k_mem_firstChangedSignIndices
#print axioms exists_adjacent_transition_inside_ordered_seed

end CentreProjectiveCycle
end JSP000404Research
