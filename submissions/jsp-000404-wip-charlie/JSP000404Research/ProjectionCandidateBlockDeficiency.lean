import JSP000404Research.ProjectionWeightedBlockHallReduction
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Minimal Hall obstruction for the planar candidate-block family

Assume the concrete planar lower-branch candidate blocks fail weighted subset
expansion.  Then there is an inclusion-minimal deficient vertex set T.

For every centre i in T:

* deleting i restores the required expansion;
* the private part of its candidate block has cardinality strictly below the
  dyadic demand 2^(centreExponent_i);
* equivalently,
      card(block_i) - 2^(centreExponent_i) + 1
        <= card(shared_i).
* in particular every candidate block has a word shared with another block in
  T, because the local block-capacity theorem gives
      2^(centreExponent_i) <= card(block_i).

This is the canonical geometric obstruction object for the final all-N
expansion proof.
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

theorem planar_lowerBranch_expansion_failure_gives_minimal_collision_core
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
    (hfail :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t)
          ≤
        (S.biUnion
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    ∃ T : Finset (ProjectionOrdered V),
      T.Nonempty ∧
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T ∧
      (∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U) ∧
      ∀ i ∈ T,
        (
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card
          - 2 ^ centreExponent (C i) t + 1
        )
        ≤
        (sharedBlockWords
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          T i).card := by
  classical
  push_neg at hfail
  obtain ⟨S,hSdef⟩ := hfail
  have hS :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        S := by
    unfold BlockDeficient
    exact hSdef
  obtain ⟨T,hTS,hTdef,hTmin⟩ :=
    exists_minimal_deficient_subset
      (fun i : ProjectionOrdered V =>
        2 ^ centreExponent (C i) t)
      (planarLowerCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hS
  have hTnonempty :
      T.Nonempty := by
    apply deficient_set_nonempty_of_positive_demands
      (fun i : ProjectionOrdered V =>
        2 ^ centreExponent (C i) t)
      (planarLowerCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      (fun i => by positivity)
      hTdef
  refine ⟨T,hTnonempty,hTdef,hTmin,?_⟩
  intro i hi
  have hlocal :=
    planar_lowerBranch_candidateBlock_local_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  exact
    minimal_deficient_shared_card_ge_slack_add_one
      (fun j : ProjectionOrdered V =>
        2 ^ centreExponent (C j) t)
      (planarLowerCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hTdef hTmin hi hlocal

theorem planar_minimal_collision_core_each_block_shared
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
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U) :
    ∀ i ∈ T,
      (sharedBlockWords
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T i).Nonempty := by
  intro i hi
  have hlocal :=
    planar_lowerBranch_candidateBlock_local_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  have hbound :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun j : ProjectionOrdered V =>
        2 ^ centreExponent (C j) t)
      (planarLowerCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hdef hmin hi hlocal
  have hpos :
      0 <
      (sharedBlockWords
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T i).card := by
    omega
  exact Finset.card_pos.mp hpos

#print axioms planar_lowerBranch_expansion_failure_gives_minimal_collision_core
#print axioms planar_minimal_collision_core_each_block_shared

end
end ProjectionOrdered
end JSP000404Research
