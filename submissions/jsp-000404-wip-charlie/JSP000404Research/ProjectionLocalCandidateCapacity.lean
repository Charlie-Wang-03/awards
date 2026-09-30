import JSP000404Research.ProjectionLossFlipCoordinate
import JSP000404Research.ResidualLocalCandidateCapacity
import JSP000404Research.ProjectionStandardBandBudget
import Mathlib.Tactic

/-!
# Every planar lower-branch centre has a full local candidate block

For the standard residual projection, every centre satisfies the one-layer
profile bound

  exponent <= projectedFree + 1.

There are two cases.

* Non-loss: exponent <= projectedFree, so the retained completion cube already
  has at least the full target mass 2^exponent.

* Exact projected loss: exponent = projectedFree + 1.  In the lower branch
  delta < 1/2, the planar loss-rigidity argument supplies a retained active
  flip coordinate c.  The doubled block Q_v union flip_c(Q_v) then has exactly
  2^exponent words.

Thus every centre admits a local Boolean candidate block of sufficient size.
The remaining all-N problem is global Hall expansion among these blocks.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_lowerBranch_exists_local_candidate_block
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t :=
      sendov_scale_pos hn hdelta0 ht
    let D :=
      genericDirectionData_sendov hp hcap htpos hlam
    let hwidth : t < (n + 1 : ℕ) := by
      rw [ht]
      exact_mod_cast
        (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
    let B :=
      standardResidualColoring D n hwidth
    let exponent : ProjectionOrdered V → ℕ :=
      fun j => centreExponent (C j) t
    ∃ block : Finset (Fin n → Bool),
      2 ^ exponent i ≤ block.card ∧
      (
        block = retainedCompletionWords B i
        ∨
        ∃ c : Fin n,
          c ∈ retainedActive B i ∧
          block = doubledCompletionBlock B i c
      ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun j => centreExponent (C j) t

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hexp : ∀ j, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 j)
  have hone :
      ∀ j, (active B j).card ≤ n - exponent j + 1 := by
    intro j
    simpa [B,D,exponent] using hprofile.2 j
  have hproj :
      ∀ j, exponent j ≤ projectedFree B j + 1 :=
    exponent_le_projectedFree_add_one
      B exponent hexp hone

  by_cases hloss :
      i ∈ projectedLossVertices B exponent
  · obtain ⟨c,hc,_hflip⟩ :=
      planar_projectedLoss_has_retained_active_flip_coordinate
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        (by simpa [B,D,exponent] using hloss)
    refine ⟨doubledCompletionBlock B i c, ?_, Or.inr ?_⟩
    · rw [projectedLoss_doubledBlock_card_eq_target
        B exponent hloss hc]
    · exact ⟨c,hc,rfl⟩
  · have hnotEq :
        exponent i ≠ projectedFree B i + 1 := by
      intro hEq
      exact hloss
        ((mem_projectedLossVertices B exponent i).2 hEq)
    have hle :
        exponent i ≤ projectedFree B i := by
      have h := hproj i
      omega
    refine ⟨retainedCompletionWords B i, ?_, Or.inl rfl⟩
    exact nonloss_completionBlock_target_le
      B exponent hle

#print axioms planar_lowerBranch_exists_local_candidate_block

end ProjectionOrdered
end JSP000404Research
