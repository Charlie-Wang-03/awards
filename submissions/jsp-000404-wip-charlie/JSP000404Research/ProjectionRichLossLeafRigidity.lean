import JSP000404Research.ProjectionRichCandidateBlock
import JSP000404Research.ResidualLossStarOrdinaryCollision
import JSP000404Research.ResidualLossStarCrossBound
import JSP000404Research.MinimalBlockSharedDeficit
import JSP000404Research.MinimalBlockConnectivity
import Mathlib.Tactic

/-!
# Leaf rigidity for projected-loss vertices in a minimal rich Hall core

Let T be an inclusion-minimal deficient set for the rich planar candidate
blocks, and let v in T be projected-loss.

If all shared words of v come from one neighbour w, then:

* w cannot be non-loss.  The v--w intersection has size at most |Q_v|, while
  minimal deficiency forces at least localSlack(v)+1 shared words and the loss
  star slack is already at least |Q_v|.

* if w is also loss and exponent(w) <= exponent(v), then
    |Star(v) ∩ Star(w)| <= |Q_v|+|Q_w| <= 2|Q_v|.
  If exponent(v) <= n-2, the rich-star slack is at least 2|Q_v|, again a
  contradiction.

Hence a maximal-exponent loss leaf can only occur at exponent n-1 and must be
adjacent to another loss vertex.
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

def HasUniqueBlockNeighbour
    {W : Type*} [DecidableEq W]
    (blocks : ProjectionOrdered V → Finset W)
    (T : Finset (ProjectionOrdered V))
    (v w : ProjectionOrdered V) : Prop :=
  w ∈ T ∧ w ≠ v ∧ BlocksCross blocks v w ∧
  ∀ z ∈ T, z ≠ v → BlocksCross blocks v z → z = w

theorem sharedBlockWords_subset_unique_neighbour_inter
    {W : Type*} [DecidableEq W]
    (blocks : ProjectionOrdered V → Finset W)
    {T : Finset (ProjectionOrdered V)}
    {v w : ProjectionOrdered V}
    (huniq : HasUniqueBlockNeighbour blocks T v w) :
    sharedBlockWords blocks T v ⊆
      blocks v ∩ blocks w := by
  classical
  intro word hshared
  have hparts := Finset.mem_inter.mp hshared
  rcases Finset.mem_biUnion.mp hparts.2 with
    ⟨z,hzErase,hzWord⟩
  have hzData := Finset.mem_erase.mp hzErase
  have hcross : BlocksCross blocks v z :=
    ⟨word,hparts.1,hzWord⟩
  have hzw :=
    huniq.2.2.2 z hzData.2 hzData.1 hcross
  subst z
  exact Finset.mem_inter.mpr ⟨hparts.1,hzWord⟩

theorem planarRich_loss_leaf_neighbour_is_loss
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
    {v w : ProjectionOrdered V}
    (hvT : v ∈ T)
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (huniq :
      HasUniqueBlockNeighbour
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T v w) :
    w ∈ projectedLossVertices
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam)
      (planarCentreExponent hp C) := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  by_contra hwNonloss
  have hblockV :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C v
        =
      activeStarCandidateBlock R v := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hvLoss
  have hblockW :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C w
        =
      retainedCompletionWords R w := by
    simpa [R, exponent] using
      planarRichCandidateBlock_nonloss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hwNonloss
  have hsharedSub :=
    sharedBlockWords_subset_unique_neighbour_inter
      (planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      huniq
  have hsharedCard :
      (sharedBlockWords
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T v).card
        ≤
      (retainedCompletionWords R v).card := by
    calc
      _ ≤
        (planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C v ∩
          planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C w).card :=
          Finset.card_le_card hsharedSub
      _ =
        (activeStarCandidateBlock R v ∩
          retainedCompletionWords R w).card := by
            rw [hblockV,hblockW]
      _ ≤ (retainedCompletionWords R v).card :=
          loss_activeStar_inter_completion_card_le_owner
            R exponent
            (planarCentreExponent_le_n
              hp hn hdelta0 (by linarith) ht C)
            (planarStandardResidual_oneLayer_budget
              hp hcap hn hdelta0 (by linarith) ht hlam C)
            hvLoss huniq.2.1.symm
  have hrequired :=
    planar_minimal_rich_core_loss_shared_ge_half_target_add_one
      hp hcap hn hdelta0 hdeltaHalf ht hlam C
      hdef hmin hvT hvLoss
  omega

theorem planarRich_maxExponent_loss_leaf_is_top_layer
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
    {v w : ProjectionOrdered V}
    (hvT : v ∈ T)
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (huniq :
      HasUniqueBlockNeighbour
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T v w)
    (hmaxLoss :
      ∀ z ∈ T,
        z ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam)
          (planarCentreExponent hp C) →
        centreExponent (C z) t ≤ centreExponent (C v) t) :
    centreExponent (C v) t = n - 1 := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hwLoss :=
    planarRich_loss_leaf_neighbour_is_loss
      hp hcap hn hdelta0 hdeltaHalf ht hlam C
      hdef hmin hvT hvLoss huniq
  have hwT := huniq.1
  have hwExp :
      exponent w ≤ exponent v := by
    exact hmaxLoss w hwT hwLoss
  have hqWle :
      (retainedCompletionWords R w).card ≤
        (retainedCompletionWords R v).card := by
    rw [retainedCompletionWords_card,
        retainedCompletionWords_card]
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    unfold projectedFree
    have hvLossEq :=
      (mem_projectedLossVertices R exponent v).1 hvLoss
    have hwLossEq :=
      (mem_projectedLossVertices R exponent w).1 hwLoss
    omega
  have hsharedSub :=
    sharedBlockWords_subset_unique_neighbour_inter
      (planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      huniq
  have hblockV :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C v
        =
      activeStarCandidateBlock R v := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hvLoss
  have hblockW :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C w
        =
      activeStarCandidateBlock R w := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hwLoss
  have hinter :=
    loss_activeStar_inter_activeStar_card_le_owner_sum
      R exponent
      (planarCentreExponent_le_n
        hp hn hdelta0 (by linarith) ht C)
      (planarStandardResidual_oneLayer_budget
        hp hcap hn hdelta0 (by linarith) ht hlam C)
      hvLoss hwLoss huniq.2.1.symm
  have hsharedUpper :
      (sharedBlockWords
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T v).card
        ≤
      2 * (retainedCompletionWords R v).card := by
    calc
      _ ≤
        (planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C v ∩
          planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C w).card :=
          Finset.card_le_card hsharedSub
      _ =
        (activeStarCandidateBlock R v ∩
          activeStarCandidateBlock R w).card := by
            rw [hblockV,hblockW]
      _ ≤
        (retainedCompletionWords R v).card +
          (retainedCompletionWords R w).card := hinter
      _ ≤ 2 * (retainedCompletionWords R v).card := by
            omega
  by_contra htop
  have hvLtN :
      exponent v < n :=
    centreExponent_lt_n
      (C v) n delta t hn hdelta0 (by linarith) ht
  have hvLe :
      exponent v ≤ n - 2 := by
    omega
  have hactiveCard :=
    projectedLoss_retainedActive_card R exponent hvLoss
  have hstar :=
    activeStarCandidateBlock_card R v
  have hhalf :=
    projectedLoss_completion_card_eq_half_target
      R exponent hvLoss
  have hlocalSlackTwoQ :
      2 * (retainedCompletionWords R v).card + 1 ≤
        (sharedBlockWords
          (planarRichCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          T v).card := by
    have hshared :=
      minimal_deficient_shared_card_ge_slack_add_one
        (fun j : ProjectionOrdered V =>
          2 ^ centreExponent (C j) t)
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        hdef hmin hvT
        (planarRichCandidateBlock_local_capacity
          hp hcap hn hdelta0 hdeltaHalf ht hlam C v)
    rw [hblockV] at hshared
    have hact3 :
        3 ≤ (retainedActive R v).card := by
      rw [hactiveCard]
      omega
    omega
  omega

#print axioms planarRich_loss_leaf_neighbour_is_loss
#print axioms planarRich_maxExponent_loss_leaf_is_top_layer

end
end ProjectionOrdered
end JSP000404Research
