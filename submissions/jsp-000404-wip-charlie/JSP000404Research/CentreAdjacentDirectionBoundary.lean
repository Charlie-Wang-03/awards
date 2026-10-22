
import JSP000404Research.CentreRayIndex
import JSP000404Research.AdjacentProjectiveGapIndex
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Adjacent boundary between two consecutive projective directions

Let j,k be rays in a theta-sorted CentreProjectiveCycle with theta_j<theta_k.
Assume no listed ray has parameter strictly between these two values.

Take the last list index whose ray still has parameter theta_j.  Its successor
exists, lies no later than the index of k, is not another theta_j ray, and by
the no-intermediate hypothesis must have parameter theta_k.

Thus two projective direction classes with an empty open interval between them
are represented by an actual adjacent pair in the sorted ray list.
-/

namespace JSP000404Research
namespace CentreProjectiveCycle

noncomputable def lowDirectionIndices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (j k : OtherVertex i) :
    Finset (Fin C.rays.length) := by
  classical
  exact Finset.univ.filter fun q =>
    q ≤ C.rayIndex k ∧
    rayThetaAt hp i (C.rays.get q) =
      rayThetaAt hp i j

theorem rayIndex_mem_lowDirectionIndices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (hjk :
      rayThetaAt hp i j < rayThetaAt hp i k) :
    C.rayIndex j ∈ C.lowDirectionIndices j k := by
  classical
  change C.rayIndex j ≤ C.rayIndex k ∧
    rayThetaAt hp i (C.rays.get (C.rayIndex j)) =
      rayThetaAt hp i j
  exact ⟨(C.rayIndex_lt_of_theta_lt hjk).le,
    by rw [C.get_rayIndex]⟩

/-- Main adjacent-boundary theorem, stated directly on angle-list entries. -/
theorem exists_adjacent_angles_of_no_strict_between
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (hjk :
      rayThetaAt hp i j < rayThetaAt hp i k)
    (hno :
      ∀ x : OtherVertex i,
        ¬ (rayThetaAt hp i j < rayThetaAt hp i x ∧
           rayThetaAt hp i x < rayThetaAt hp i k)) :
    ∃ m : ℕ, ∃ hm : m + 1 < C.angles.length,
      C.angles[m]'(by omega) = rayThetaAt hp i j ∧
      C.angles[m + 1]'hm = rayThetaAt hp i k := by
  classical
  let S := C.lowDirectionIndices j k
  have hSne : S.Nonempty := by
    exact ⟨C.rayIndex j,
      C.rayIndex_mem_lowDirectionIndices hjk⟩
  let q : Fin C.rays.length := S.max' hSne
  have hqS : q ∈ S := Finset.max'_mem S hSne
  have hqData :
      q ≤ C.rayIndex k ∧
      rayThetaAt hp i (C.rays.get q) =
        rayThetaAt hp i j := by
    simpa [S, lowDirectionIndices] using hqS
  have hqk : q < C.rayIndex k := by
    apply lt_of_le_of_ne hqData.1
    intro heq
    have hthetaK :
        rayThetaAt hp i (C.rays.get q) =
          rayThetaAt hp i k := by
      rw [heq, C.get_rayIndex]
    linarith
  have hsuccVal :
      q.val + 1 < C.rays.length := by
    have hklt := (C.rayIndex k).isLt
    have hqkNat : q.val < (C.rayIndex k).val := hqk
    omega
  let qsucc : Fin C.rays.length :=
    ⟨q.val + 1, hsuccVal⟩
  have hqsucc : q < qsucc := by
    change q.val < q.val + 1
    omega
  have hqsuccLeK : qsucc ≤ C.rayIndex k := by
    change q.val + 1 ≤ (C.rayIndex k).val
    exact Nat.succ_le_of_lt hqk
  have hthetaQ :
      rayThetaAt hp i (C.rays.get q) =
        rayThetaAt hp i j :=
    hqData.2
  have hthetaLower :
      rayThetaAt hp i j ≤
        rayThetaAt hp i (C.rays.get qsucc) := by
    have hsorted :=
      C.theta_sorted.rel_get_of_lt hqsucc
    rw [hthetaQ] at hsorted
    exact hsorted
  have hthetaUpper :
      rayThetaAt hp i (C.rays.get qsucc) ≤
        rayThetaAt hp i k := by
    by_cases heq : qsucc = C.rayIndex k
    · rw [heq, C.get_rayIndex]
    · have hlt : qsucc < C.rayIndex k :=
        lt_of_le_of_ne hqsuccLeK heq
      have hsorted :=
        C.theta_sorted.rel_get_of_lt hlt
      rw [C.get_rayIndex] at hsorted
      exact hsorted
  have hthetaNeLow :
      rayThetaAt hp i (C.rays.get qsucc) ≠
        rayThetaAt hp i j := by
    intro heq
    have hsuccS : qsucc ∈ S := by
      change qsucc ∈ C.lowDirectionIndices j k
      change qsucc ≤ C.rayIndex k ∧
        rayThetaAt hp i (C.rays.get qsucc) =
          rayThetaAt hp i j
      exact ⟨hqsuccLeK, heq⟩
    have hleMax : qsucc ≤ q :=
      Finset.le_max' S qsucc hsuccS
    exact (not_lt_of_ge hleMax) hqsucc
  have hthetaSucc :
      rayThetaAt hp i (C.rays.get qsucc) =
        rayThetaAt hp i k := by
    by_contra hne
    have hstrictLow :
        rayThetaAt hp i j <
          rayThetaAt hp i (C.rays.get qsucc) :=
      lt_of_le_of_ne hthetaLower (Ne.symm hthetaNeLow)
    have hstrictHigh :
        rayThetaAt hp i (C.rays.get qsucc) <
          rayThetaAt hp i k :=
      lt_of_le_of_ne hthetaUpper hne
    exact hno (C.rays.get qsucc)
      ⟨hstrictLow, hstrictHigh⟩
  have hsuccAngle : q.val + 1 < C.angles.length := by
    rw [C.angles_length]
    exact hsuccVal
  refine ⟨q.val, hsuccAngle, ?_, ?_⟩
  · have hqAngle : q.val < C.angles.length := by omega
    have hget :
        C.angles[q.val]'hqAngle =
          rayThetaAt hp i (C.rays.get q) := by
      simp [CentreProjectiveCycle.angles]
    exact hget.trans hthetaQ
  · have hget :
        C.angles[q.val + 1]'hsuccAngle =
          rayThetaAt hp i (C.rays.get qsucc) := by
      simp [CentreProjectiveCycle.angles, qsucc]
    exact hget.trans hthetaSucc

/-- If the boundary angle difference is exactly lambda and lambda has scaled
width one, then quotient 1 occurs in the centre quotient list. -/
theorem one_mem_quotientList_of_empty_exact_interval
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    {j k : OtherVertex i}
    {lam : ℝ}
    (hjk :
      rayThetaAt hp i j < rayThetaAt hp i k)
    (hgap :
      rayThetaAt hp i k - rayThetaAt hp i j = lam)
    (hscale :
      t * (lam / Real.pi) = 1)
    (hno :
      ∀ x : OtherVertex i,
        ¬ (rayThetaAt hp i j < rayThetaAt hp i x ∧
           rayThetaAt hp i x < rayThetaAt hp i k)) :
    1 ∈ quotientList t C.gaps := by
  obtain ⟨m, hm, hmLow, hmHigh⟩ :=
    C.exists_adjacent_angles_of_no_strict_between
      hjk hno
  have hmem :=
    centre_adjacent_angle_quotient_mem
      C t m hm
  have hfloor :
      Nat.floor
          (t * ((C.angles[m + 1] - C.angles[m]) / Real.pi))
        = 1 := by
    rw [hmLow, hmHigh, hgap, hscale]
    norm_num
  rw [hfloor] at hmem
  exact hmem

#print axioms exists_adjacent_angles_of_no_strict_between
#print axioms one_mem_quotientList_of_empty_exact_interval

end CentreProjectiveCycle
end JSP000404Research
