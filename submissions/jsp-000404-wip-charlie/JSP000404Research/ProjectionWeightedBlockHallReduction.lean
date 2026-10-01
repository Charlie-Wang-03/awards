import JSP000404Research.ProjectionLocalCandidateCapacity
import JSP000404Research.WeightedBlockHallOutlet
import Mathlib.Tactic

/-!
# Planar lower branch reduced to vertex-block expansion

ProjectionLocalCandidateCapacity proves that every centre in the planar lower
branch has a Boolean candidate block of cardinality at least its full dyadic
target mass.  This file chooses one such block for every centre simultaneously.

The weighted block Hall theorem then shows that the all-N dyadic centre
capacity follows from one explicit subset-expansion statement for this chosen
family:

  for every S,
    sum_{i in S} 2^(centreExponent_i)
      <= card (union_{i in S} candidateBlock_i).

Each chosen block is either the original retained completion cube or, at a
projected-loss centre, one doubled completion block Q_i union flip_c(Q_i).

Thus all local-capacity issues are closed; the only remaining obligation is
global expansion of this concrete block family.
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

noncomputable def planarLowerCandidateBlock
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
  classical
  exact Classical.choose
    (planar_lowerBranch_exists_local_candidate_block
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i)

theorem planarLowerCandidateBlock_spec
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
    2 ^ exponent i ≤
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card
    ∧
    (
      planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        = retainedCompletionWords B i
      ∨
      ∃ c : Fin n,
        c ∈ retainedActive B i ∧
        planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C i
          = doubledCompletionBlock B i c
    ) := by
  classical
  exact Classical.choose_spec
    (planar_lowerBranch_exists_local_candidate_block
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i)

theorem planar_lowerBranch_capacity_of_candidateBlock_expansion
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
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  apply dyadic_capacity_of_vertex_block_expansion
    (fun i : ProjectionOrdered V =>
      centreExponent (C i) t)
    (planarLowerCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C)
  exact hExpansion

theorem planar_lowerBranch_candidateBlock_local_capacity
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
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card := by
  intro i
  have hspec :=
    planarLowerCandidateBlock_spec
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  simpa using hspec.1

#print axioms planarLowerCandidateBlock_spec
#print axioms planar_lowerBranch_capacity_of_candidateBlock_expansion
#print axioms planar_lowerBranch_candidateBlock_local_capacity

end
end ProjectionOrdered
end JSP000404Research
