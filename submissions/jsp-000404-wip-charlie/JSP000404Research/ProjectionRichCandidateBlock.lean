import JSP000404Research.PlanarResidualHardRemainder
import JSP000404Research.ResidualLossStarCapacity
import JSP000404Research.WeightedBlockHallOutlet
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Rich planar candidate blocks

Use all one-active-coordinate exits at projected-loss vertices.

For the standard residual colouring R and centre exponent k:

* if v is non-loss, set B(v)=Q_v;
* if v is projected-loss, set B(v)=Star(v), the original cube together with
  every active one-coordinate translate.

The loss star has exact disjoint Hamming-star geometry and strictly more local
capacity than a single doubled block whenever k(v)<n.

Weighted Hall again reduces the all-N theorem to subset expansion of this rich
family.  In a minimal deficient subset, every loss vertex must share not just
one word but at least one more than its whole local slack.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

noncomputable def planarRichCandidateBlock
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
    Finset (Fin n → Bool) := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  if hloss : i ∈ projectedLossVertices R exponent then
    exact activeStarCandidateBlock R i
  else
    exact retainedCompletionWords R i

theorem planarRichCandidateBlock_loss
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
    {i : ProjectionOrdered V}
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      =
    activeStarCandidateBlock
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam) i := by
  classical
  simp [planarRichCandidateBlock, hloss]

theorem planarRichCandidateBlock_nonloss
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
    {i : ProjectionOrdered V}
    (hnloss :
      i ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      =
    retainedCompletionWords
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam) i := by
  classical
  simp [planarRichCandidateBlock, hnloss]

theorem planarRichCandidateBlock_local_capacity
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    ∀ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t ≤
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card := by
  classical
  intro i
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexp :
      ∀ j, exponent j ≤ n :=
    planarCentreExponent_le_n
      hp hn hdelta0 hdelta1 ht C
  have hone :
      ∀ j, (active R j).card ≤ n - exponent j + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hprofile :=
    exponent_le_projectedFree_add_one
      R exponent hexp hone
  by_cases hloss : i ∈ projectedLossVertices R exponent
  · rw [show
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        =
      activeStarCandidateBlock R i by
        simpa [R, exponent] using
          planarRichCandidateBlock_loss
            hp hcap hn hdelta0 hdeltaHalf ht hlam C hloss]
    exact projectedLoss_activeStar_target_le
      R exponent hloss
  · rw [show
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        =
      retainedCompletionWords R i by
        simpa [R, exponent] using
          planarRichCandidateBlock_nonloss
            hp hcap hn hdelta0 hdeltaHalf ht hlam C hloss]
    have hneq :
        exponent i ≠ projectedFree R i + 1 := by
      intro h
      exact hloss
        ((mem_projectedLossVertices R exponent i).2 h)
    have hle : exponent i ≤ projectedFree R i := by
      have h := hprofile i
      omega
    exact nonloss_completionBlock_target_le
      R exponent hle

theorem planar_lowerBranch_capacity_of_richBlock_expansion
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
    (hExpansion :
      ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t)
          ≤
        (S.biUnion
          (planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n :=
  dyadic_capacity_of_vertex_block_expansion
    (fun i : ProjectionOrdered V =>
      centreExponent (C i) t)
    (planarRichCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C)
    hExpansion

theorem planar_minimal_rich_core_loss_shared_ge_half_target_add_one
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
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U)
    {i : ProjectionOrdered V}
    (hi : i ∈ T)
    (hiLoss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    (retainedCompletionWords
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam) i).card + 1
      ≤
    (sharedBlockWords
      (planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      T i).card := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hiLt : exponent i < n :=
    centreExponent_lt_n
      (C i) n delta t hn hdelta0 (by linarith) ht
  have hblock :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        =
      activeStarCandidateBlock R i := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hiLoss
  have hslack :=
    projectedLoss_activeStar_slack_ge_half_target
      R exponent hiLoss hiLt
  have hshared :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun j : ProjectionOrdered V =>
        2 ^ centreExponent (C j) t)
      (planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hdef hmin hi
      (planarRichCandidateBlock_local_capacity
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i)
  rw [hblock] at hshared
  simpa [R, exponent] using
    (show
      (retainedCompletionWords R i).card + 1 ≤
        (sharedBlockWords
          (planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          T i).card by
      omega)

#print axioms planarRichCandidateBlock_local_capacity
#print axioms planar_lowerBranch_capacity_of_richBlock_expansion
#print axioms planar_minimal_rich_core_loss_shared_ge_half_target_add_one

end
end ProjectionOrdered
end JSP000404Research
