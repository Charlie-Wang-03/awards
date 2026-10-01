import JSP000404Research.ProjectionCanonicalBlockHall
import JSP000404Research.ResidualLossBlockerEdge
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Semantic collision classification for canonical planar candidate blocks

For the canonical planar block family, a translated component occurs only at a
projected-loss vertex. Therefore the four syntactic collision types from
ResidualCandidateCollision can be refined semantically.

For a shared word between distinct vertices i,j:

* Q_i--Q_j:
    both original completion cubes contain the word.  Hence neither endpoint
    can be projected-loss (a loss completion cube is disjoint from every other
    completion cube), and the pair is a residual overlap.

* Q_i--T_j:
    j is projected-loss.  Undo the j-translation to a source word in Q_j.
    The actual retained edge joining j to i has colour equal to j's chosen
    flip coordinate.

* T_i--Q_j:
    symmetric.

* T_i--T_j:
    both i,j are projected-loss.  Same-coordinate translated blocks are
    disjoint; for distinct coordinates, any intersection forces the connecting
    retained edge colour to equal one of the two flip coordinates.

This turns every shared word in a minimal canonical Hall obstruction into a
concrete residual-colour edge constraint.
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

theorem planarCanonicalCandidateBlock_translated_implies_loss
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
    {word : Fin n → Bool}
    {c : Fin n}
    (hc : c ∈ retainedActive
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam) i)
    (htrans :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i c)
    (hwordBlock :
      word ∈ planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i)
    (hnotOrig :
      word ∉ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i) :
    i ∈ projectedLossVertices
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam)
      (planarCentreExponent hp C) := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  by_contra hnloss
  have hblock :=
    planarCanonicalCandidateBlock_nonloss
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      (by simpa [R, exponent] using hnloss)
  have : word ∈ retainedCompletionWords R i := by
    simpa [R] using (show
      word ∈ planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i from hwordBlock)
      |> fun h => by simpa [hblock] using h
  exact hnotOrig (by simpa [R] using this)

theorem planarCanonical_original_original_collision_residual_nonloss
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
    {i j : ProjectionOrdered V}
    (hij : i ≠ j)
    {word : Fin n → Bool}
    (hi :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i)
    (hj :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) j) :
    i ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)
    ∧
    j ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)
    ∧
    (
      (i < j ∧ IsResidual
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i j)
      ∨
      (j < i ∧ IsResidual
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) j i)
    ) := by
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
  have hiNloss : i ∉ projectedLossVertices R exponent := by
    intro hiLoss
    have hdisj :=
      projectedLoss_completion_disjoint
        R exponent hexp hone hiLoss hij
    exact Finset.disjoint_left.mp hdisj hi hj
  have hjNloss : j ∉ projectedLossVertices R exponent := by
    intro hjLoss
    have hdisj :=
      projectedLoss_completion_disjoint
        R exponent hexp hone hjLoss hij.symm
    exact Finset.disjoint_left.mp hdisj hj hi
  refine ⟨hiNloss,hjNloss,?_⟩
  exact retainedCompletion_overlap_forces_residual
    R hij hi hj

theorem planarCanonical_original_translated_collision_loss_edge
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
    {i j : ProjectionOrdered V}
    (hij : i ≠ j)
    {word : Fin n → Bool}
    {d : Fin n}
    (hiQ :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i)
    (hd :
      d ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) j)
    (hjT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) j d)
    (hjLoss :
      j ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    (
      ∃ hji : j < i,
        ∃ hret :
          ((planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam).color j i).val < n,
          retainedColor
            (planarStandardResidualColoring
              hp hcap hn hdelta0 (by linarith) ht hlam)
            j i hret = d
    )
    ∨
    (
      ∃ hij' : i < j,
        ∃ hret :
          ((planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam).color i j).val < n,
          retainedColor
            (planarStandardResidualColoring
              hp hcap hn hdelta0 (by linarith) ht hlam)
            i j hret = d
    ) := by
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
  have hjOrig :
      flipBoolWordAt word d ∈ retainedCompletionWords R j :=
    (mem_translatedCompletionWords R j d word).1 hjT
  have hiAsFlip :
      flipBoolWordAt (flipBoolWordAt word d) d = word := by
    exact flipBoolWordAt_involutive d word
  have hblock :=
    loss_translated_blocker_edge_colour
      R exponent hexp hone
      hjLoss hij.symm hd hjOrig
      (by simpa [flipBoolWordAt_involutive] using hiQ)
  rcases hblock with hright | hleft
  · exact Or.inl hright
  · exact Or.inr hleft

theorem planarCanonical_translated_translated_collision_loss_rigidity
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
    {i j : ProjectionOrdered V}
    (hij : i ≠ j)
    {word : Fin n → Bool}
    {c d : Fin n}
    (hiLoss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (hjLoss :
      j ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (hiT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i c)
    (hjT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) j d) :
    c ≠ d ∧
    (
      (∃ hij' : i < j,
        ∃ hret :
          ((planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam).color i j).val < n,
          retainedColor
            (planarStandardResidualColoring
              hp hcap hn hdelta0 (by linarith) ht hlam)
            i j hret = c
          ∨
          retainedColor
            (planarStandardResidualColoring
              hp hcap hn hdelta0 (by linarith) ht hlam)
            i j hret = d)
      ∨
      (∃ hji : j < i,
        ∃ hret :
          ((planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam).color j i).val < n,
          retainedColor
            (planarStandardResidualColoring
              hp hcap hn hdelta0 (by linarith) ht hlam)
            j i hret = c
          ∨
          retainedColor
            (planarStandardResidualColoring
              hp hcap hn hdelta0 (by linarith) ht hlam)
            j i hret = d)
    ) := by
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
  have hcd : c ≠ d := by
    intro h
    subst d
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        R exponent hexp hone hiLoss hjLoss hij c
    exact Finset.disjoint_left.mp hdisj hiT hjT
  refine ⟨hcd,?_⟩
  exact translated_loss_conflict_edge_colour
    R exponent hexp hone
    hiLoss hjLoss hij hiT hjT

#print axioms planarCanonical_original_original_collision_residual_nonloss
#print axioms planarCanonical_original_translated_collision_loss_edge
#print axioms planarCanonical_translated_translated_collision_loss_rigidity

end
end ProjectionOrdered
end JSP000404Research
