import JSP000404Research.ProjectionRichPairExpansion
import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Two-vertex rich Hall obstructions contain no projected loss

For the rich planar candidate family, every two-vertex set containing a
projected-loss vertex satisfies weighted expansion. Therefore any deficient
two-vertex set consists entirely of non-loss vertices.

This separates the genuinely global projected-loss obstruction from the
two-centre overlap problem: projected loss can only participate in a Hall
obstruction of cardinality at least three.
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

theorem planarRich_deficient_pair_vertices_nonloss
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
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarRichCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        {u,v}) :
    u ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)
    ∧
    v ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C) := by
  classical
  constructor
  · intro huLoss
    by_cases hvLoss :
        v ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam)
          (planarCentreExponent hp C)
    · have hexpand :=
        planarRich_loss_loss_pair_expands
          hp hcap hn hdelta0 hdeltaHalf ht hlam C
          huv huLoss hvLoss
      unfold BlockDeficient at hdef
      simp only [Finset.biUnion_insert, Finset.biUnion_singleton,
        Finset.sum_insert, Finset.mem_singleton, huv,
        not_false_eq_true, Finset.sum_singleton] at hdef
      omega
    · have hexpand :=
        planarRich_loss_nonloss_pair_expands
          hp hcap hn hdelta0 hdeltaHalf ht hlam C
          huv huLoss hvLoss
      unfold BlockDeficient at hdef
      simp only [Finset.biUnion_insert, Finset.biUnion_singleton,
        Finset.sum_insert, Finset.mem_singleton, huv,
        not_false_eq_true, Finset.sum_singleton] at hdef
      omega
  · intro hvLoss
    by_cases huLoss :
        u ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam)
          (planarCentreExponent hp C)
    · have hexpand :=
        planarRich_loss_loss_pair_expands
          hp hcap hn hdelta0 hdeltaHalf ht hlam C
          huv huLoss hvLoss
      unfold BlockDeficient at hdef
      simp only [Finset.biUnion_insert, Finset.biUnion_singleton,
        Finset.sum_insert, Finset.mem_singleton, huv,
        not_false_eq_true, Finset.sum_singleton] at hdef
      omega
    · have hexpand :=
        planarRich_loss_nonloss_pair_expands
          hp hcap hn hdelta0 hdeltaHalf ht hlam C
          huv.symm hvLoss huLoss
      unfold BlockDeficient at hdef
      have hpairUnion :
          planarRichCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C v ∪
            planarRichCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C u
          =
          planarRichCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C u ∪
            planarRichCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C v := by
        exact Finset.union_comm _ _
      simp only [Finset.biUnion_insert, Finset.biUnion_singleton,
        Finset.sum_insert, Finset.mem_singleton, huv,
        not_false_eq_true, Finset.sum_singleton] at hdef
      rw [hpairUnion] at hexpand
      omega

#print axioms planarRich_deficient_pair_vertices_nonloss

end
end ProjectionOrdered
end JSP000404Research
