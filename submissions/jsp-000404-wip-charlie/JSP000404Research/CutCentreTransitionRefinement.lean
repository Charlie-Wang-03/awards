import JSP000404Research.CutCentreRayCycle
import Mathlib
import Mathlib.Tactic

/-!
# Refining a cut-ordered transition seed to an adjacent transition

This is the arbitrary-projective-cut analogue of CentreTransitionRefinement.
Inside a CentreCutRayCycle, two rays with strictly ordered cut parameters and
opposite cut-adjusted signs contain a first changed-sign index.  Its
predecessor gives an actual adjacent transition of the cut-sorted cycle.

The adjacent transition is nested in the seed interval, and the global angle
cap forces its normalized cut gap to have length at least one.
-/

namespace JSP000404Research
namespace CentreCutRayCycle

open Real

noncomputable def firstChangedCutSignIndices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (j k : OtherVertex i) :
    Finset (Fin R.rays.length) := by
  classical
  exact Finset.univ.filter fun r =>
    R.rayIndex j < r ∧
    r ≤ R.rayIndex k ∧
    cutRaySign hp c i (R.rays.get r) ≠
      cutRaySign hp c i j

theorem rayIndex_k_mem_firstChangedCutSignIndices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    {j k : OtherVertex i}
    (htheta :
      cutRayTheta hp c i j <
        cutRayTheta hp c i k)
    (hsign :
      cutRaySign hp c i j ≠
        cutRaySign hp c i k) :
    R.rayIndex k ∈
      R.firstChangedCutSignIndices j k := by
  classical
  simp only [firstChangedCutSignIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨R.rayIndex_lt_of_cutTheta_lt htheta, le_rfl,
    by simpa only [R.get_rayIndex] using hsign.symm⟩

/-- Consecutive cut-cycle indices leave no third ray with adjusted theta
strictly between their endpoint values. -/
theorem no_cutTheta_strict_between_adjacent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    {q r : Fin R.rays.length}
    (hsucc : r.val = q.val + 1) :
    ∀ x : OtherVertex i,
      ¬ (cutRayTheta hp c i (R.rays.get q) <
            cutRayTheta hp c i x ∧
         cutRayTheta hp c i x <
            cutRayTheta hp c i (R.rays.get r)) := by
  intro x hx
  have hqx :
      q < R.rayIndex x := by
    have h :=
      R.rayIndex_lt_of_cutTheta_lt hx.1
    simpa only [R.rayIndex_get] using h
  have hxr :
      R.rayIndex x < r := by
    have h :=
      R.rayIndex_lt_of_cutTheta_lt hx.2
    simpa only [R.rayIndex_get] using h
  have hqv : q.val < (R.rayIndex x).val :=
    hqx
  have hrv : (R.rayIndex x).val < r.val :=
    hxr
  omega

/-- Main adjacent refinement in the cut-sorted cycle. -/
theorem exists_adjacent_cut_transition_inside_ordered_seed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    {j k : OtherVertex i}
    (htheta :
      cutRayTheta hp c i j <
        cutRayTheta hp c i k)
    (hsign :
      cutRaySign hp c i j ≠
        cutRaySign hp c i k) :
    ∃ q r : Fin R.rays.length,
      r.val = q.val + 1 ∧
      R.rayIndex j ≤ q ∧
      r ≤ R.rayIndex k ∧
      cutRaySign hp c i (R.rays.get q) ≠
        cutRaySign hp c i (R.rays.get r) ∧
      1 ≤
        t * ((cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)) / Real.pi) ∧
      t * ((cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)) / Real.pi)
        ≤
      t * ((cutRayTheta hp c i k -
          cutRayTheta hp c i j) / Real.pi) := by
  classical
  let S := R.firstChangedCutSignIndices j k
  have hSne : S.Nonempty := by
    exact ⟨R.rayIndex k,
      R.rayIndex_k_mem_firstChangedCutSignIndices
        htheta hsign⟩
  let r : Fin R.rays.length := S.min' hSne
  have hrS : r ∈ S := Finset.min'_mem S hSne
  have hrData :
      R.rayIndex j < r ∧
      r ≤ R.rayIndex k ∧
      cutRaySign hp c i (R.rays.get r) ≠
        cutRaySign hp c i j := by
    simpa [S, firstChangedCutSignIndices] using hrS
  have hrPos : 0 < r.val := by
    have hjr : (R.rayIndex j).val < r.val := hrData.1
    omega
  let q : Fin R.rays.length :=
    ⟨r.val - 1, by
      have hrlt := r.isLt
      omega⟩
  have hqrVal : r.val = q.val + 1 := by
    dsimp [q]
    omega
  have hqLtR : q < r := by
    exact Fin.mk_lt_mk.mpr (by omega)
  have hjLeQ : R.rayIndex j ≤ q := by
    have hjr : (R.rayIndex j).val < r.val := hrData.1
    exact Fin.mk_le_mk.mpr (by omega)
  have hqSign :
      cutRaySign hp c i (R.rays.get q) =
        cutRaySign hp c i j := by
    by_contra hne
    by_cases hjq : R.rayIndex j = q
    · have hget : R.rays.get q = j := by
        rw [← hjq, R.get_rayIndex]
      exact hne (by rw [hget])
    · have hjLtQ : R.rayIndex j < q :=
        lt_of_le_of_ne hjLeQ hjq
      have hqLeK : q ≤ R.rayIndex k :=
        hqLtR.le.trans hrData.2.1
      have hqS : q ∈ S := by
        simp [S, firstChangedCutSignIndices,
          hjLtQ, hqLeK, hne]
      have hrLeQ : r ≤ q :=
        Finset.min'_le S q hqS
      exact (not_lt_of_ge hrLeQ) hqLtR
  have htransition :
      cutRaySign hp c i (R.rays.get q) ≠
        cutRaySign hp c i (R.rays.get r) := by
    rw [hqSign]
    exact hrData.2.2.symm
  have hthetaQR :
      cutRayTheta hp c i (R.rays.get q) ≤
        cutRayTheta hp c i (R.rays.get r) :=
    R.cutTheta_sorted.rel_get_of_lt hqLtR
  have hqNeR : R.rays.get q ≠ R.rays.get r := by
    intro h
    have heq : q = r := by
      calc
        q = R.rayIndex (R.rays.get q) := (R.rayIndex_get q).symm
        _ = R.rayIndex (R.rays.get r) := congrArg R.rayIndex h
        _ = r := R.rayIndex_get r
    exact (ne_of_lt hqLtR) heq
  have hlower :=
    one_le_t_mul_cutRay_gap_of_sign_ne
      hp hcap ht hlam hc0 hcpi i
      hqNeR hthetaQR htransition
  have hthetaJQ :
      cutRayTheta hp c i j ≤
        cutRayTheta hp c i (R.rays.get q) := by
    have hidx :
        R.rayIndex j ≤ R.rayIndex (R.rays.get q) := by
      simpa only [R.rayIndex_get] using hjLeQ
    exact R.cutTheta_le_of_rayIndex_le hidx
  have hthetaRK :
      cutRayTheta hp c i (R.rays.get r) ≤
        cutRayTheta hp c i k := by
    have hidx :
        R.rayIndex (R.rays.get r) ≤ R.rayIndex k := by
      simpa only [R.rayIndex_get] using hrData.2.1
    exact R.cutTheta_le_of_rayIndex_le hidx
  have hgapLe :
      cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)
        ≤
      cutRayTheta hp c i k -
          cutRayTheta hp c i j := by
    linarith
  have hscale :
      t * ((cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)) / Real.pi)
        ≤
      t * ((cutRayTheta hp c i k -
          cutRayTheta hp c i j) / Real.pi) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hdiv :=
      div_le_div_of_nonneg_right hgapLe hpi.le
    exact mul_le_mul_of_nonneg_left hdiv ht.le
  exact ⟨q, r, hqrVal, hjLeQ, hrData.2.1,
    htransition, hlower, hscale⟩

#print axioms rayIndex_k_mem_firstChangedCutSignIndices
#print axioms exists_adjacent_cut_transition_inside_ordered_seed

end CentreCutRayCycle
end JSP000404Research
