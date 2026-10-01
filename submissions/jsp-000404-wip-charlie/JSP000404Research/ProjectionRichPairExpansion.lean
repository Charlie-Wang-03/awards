import JSP000404Research.ProjectionRichCandidateBlock
import JSP000404Research.ResidualLossStarOrdinaryCollision
import JSP000404Research.ResidualLossStarCrossBound
import Mathlib.Tactic

/-!
# Pair expansion for rich candidate blocks involving projected loss

For the rich planar candidate family, every two-vertex set containing a
projected-loss vertex already satisfies weighted expansion.

Loss--nonloss:
the loss-star local slack is at least card(Q_loss), while its intersection
with the ordinary non-loss completion cube has cardinality at most that same
quantity.

Loss--loss:
the two local slacks sum to at least card(Q_u)+card(Q_v), while the two rich
stars intersect in at most card(Q_u)+card(Q_v).

Thus a two-vertex Hall-deficient set, if any, must consist entirely of
non-loss vertices.
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

theorem planarRich_loss_nonloss_pair_expands
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
    {u v : ProjectionOrdered V}
    (huv : u ≠ v)
    (huLoss :
      u ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (hvNonloss :
      v ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    2 ^ centreExponent (C u) t +
        2 ^ centreExponent (C v) t
      ≤
    (planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C u ∪
      planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C v).card := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexp :
      ∀ x, exponent x ≤ n :=
    planarCentreExponent_le_n
      hp hn hdelta0 hdelta1 ht C
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have huLt : exponent u < n :=
    centreExponent_lt_n
      (C u) n delta t hn hdelta0 hdelta1 ht
  have hstarU :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C u
        =
      activeStarCandidateBlock R u := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C huLoss
  have hblockV :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C v
        =
      retainedCompletionWords R v := by
    simpa [R, exponent] using
      planarRichCandidateBlock_nonloss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hvNonloss
  have hlocalV :=
    planarRichCandidateBlock_local_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C v
  rw [hblockV] at hlocalV
  have hslackU :=
    projectedLoss_activeStar_slack_ge_half_target
      R exponent huLoss huLt
  have hinter :=
    loss_activeStar_inter_completion_card_le_owner
      R exponent hexp hone huLoss huv
  rw [hstarU,hblockV,Finset.card_union]
  omega

theorem planarRich_loss_loss_pair_expands
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
    {u v : ProjectionOrdered V}
    (huv : u ≠ v)
    (huLoss :
      u ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    2 ^ centreExponent (C u) t +
        2 ^ centreExponent (C v) t
      ≤
    (planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C u ∪
      planarRichCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C v).card := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexp :
      ∀ x, exponent x ≤ n :=
    planarCentreExponent_le_n
      hp hn hdelta0 hdelta1 ht C
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have huLt : exponent u < n :=
    centreExponent_lt_n
      (C u) n delta t hn hdelta0 hdelta1 ht
  have hvLt : exponent v < n :=
    centreExponent_lt_n
      (C v) n delta t hn hdelta0 hdelta1 ht
  have hstarU :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C u
        =
      activeStarCandidateBlock R u := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C huLoss
  have hstarV :
      planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C v
        =
      activeStarCandidateBlock R v := by
    simpa [R, exponent] using
      planarRichCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C hvLoss
  have hslackU :=
    projectedLoss_activeStar_slack_ge_half_target
      R exponent huLoss huLt
  have hslackV :=
    projectedLoss_activeStar_slack_ge_half_target
      R exponent hvLoss hvLt
  have hinter :=
    loss_activeStar_inter_activeStar_card_le_owner_sum
      R exponent hexp hone huLoss hvLoss huv
  rw [hstarU,hstarV,Finset.card_union]
  omega

#print axioms planarRich_loss_nonloss_pair_expands
#print axioms planarRich_loss_loss_pair_expands

end
end ProjectionOrdered
end JSP000404Research
