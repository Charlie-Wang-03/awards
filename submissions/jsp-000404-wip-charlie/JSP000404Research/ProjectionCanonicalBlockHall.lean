import JSP000404Research.ProjectionCanonicalCandidateBlock
import JSP000404Research.WeightedBlockHallOutlet
import JSP000404Research.MinimalBlockSharedDeficit
import JSP000404Research.ResidualCandidateCollision
import Mathlib.Tactic

/-!
# Canonical planar candidate blocks: Hall reduction and minimal collision core

Use the explicit candidate family

* non-loss: Q_i,
* loss: Q_i union flip_{c_i}(Q_i),

where c_i is the canonical retained-active loss coordinate chosen by the
planar rigidity theorem.

If this family satisfies weighted subset expansion, the all-N dyadic centre
capacity follows by the block-level Hall theorem.

If expansion fails, choose an inclusion-minimal deficient set T. Every vertex
of T has a shared candidate word. Since every block has explicit
completion/doubled shape, that word yields one of the four concrete collision
types:

  Q_i-Q_j,
  Q_i-T_j,
  T_i-Q_j,
  T_i-T_j.

This is the precise global obstruction surface for the remaining proof.
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

theorem planarCanonicalCandidateBlock_shape
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
    let R :=
      planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam
    CandidateBlockShape R
      (planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C) i := by
  classical
  dsimp
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  by_cases hloss : i ∈ projectedLossVertices R exponent
  · right
    let c :=
      planarCanonicalLossCoordinate
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        (by simpa [R, exponent] using hloss)
    have hc :
        c ∈ retainedActive R i := by
      dsimp [c]
      simpa [R, exponent] using
        planarCanonicalLossCoordinate_active
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
          (by simpa [R, exponent] using hloss)
    refine ⟨c,hc,?_⟩
    simpa [R, exponent, c] using
      planarCanonicalCandidateBlock_loss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        (by simpa [R, exponent] using hloss)
  · left
    simpa [R, exponent] using
      planarCanonicalCandidateBlock_nonloss
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        (by simpa [R, exponent] using hloss)

theorem planar_lowerBranch_capacity_of_canonicalBlock_expansion
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
          (planarCanonicalCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  exact dyadic_capacity_of_vertex_block_expansion
    (fun i : ProjectionOrdered V =>
      centreExponent (C i) t)
    (planarCanonicalCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C)
    hExpansion

theorem planar_canonical_expansion_failure_minimal_core
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
          (planarCanonicalCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    ∃ T : Finset (ProjectionOrdered V),
      T.Nonempty ∧
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T ∧
      (∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarCanonicalCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U) ∧
      ∀ i ∈ T,
        (sharedBlockWords
          (planarCanonicalCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          T i).Nonempty := by
  classical
  push_neg at hfail
  obtain ⟨S,hSdef⟩ := hfail
  have hS :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        S := by
    unfold BlockDeficient
    exact hSdef
  obtain ⟨T,hTS,hTdef,hTmin⟩ :=
    exists_minimal_deficient_subset
      (fun i : ProjectionOrdered V =>
        2 ^ centreExponent (C i) t)
      (planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hS
  have hTnonempty :
      T.Nonempty := by
    apply deficient_set_nonempty_of_positive_demands
      (fun i : ProjectionOrdered V =>
        2 ^ centreExponent (C i) t)
      (planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      (fun i => by positivity)
      hTdef
  refine ⟨T,hTnonempty,hTdef,hTmin,?_⟩
  intro i hi
  have hlocal :=
    planarCanonicalCandidateBlock_local_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  have hbound :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun j : ProjectionOrdered V =>
        2 ^ centreExponent (C j) t)
      (planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hTdef hTmin hi hlocal
  have hpos :
      0 <
      (sharedBlockWords
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T i).card := by
    omega
  exact Finset.card_pos.mp hpos

theorem planar_minimal_core_vertex_has_four_way_collision
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
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarCanonicalCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U)
    {i : ProjectionOrdered V}
    (hi : i ∈ T) :
    let R :=
      planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam
    ∃ word : Fin n → Bool,
      ∃ j : ProjectionOrdered V,
        j ∈ T ∧
        j ≠ i ∧
        (
          (
            word ∈ retainedCompletionWords R i ∧
            word ∈ retainedCompletionWords R j
          )
          ∨
          (
            word ∈ retainedCompletionWords R i ∧
            ∃ d : Fin n,
              d ∈ retainedActive R j ∧
              word ∈ translatedCompletionWords R j d
          )
          ∨
          (
            (∃ c : Fin n,
              c ∈ retainedActive R i ∧
              word ∈ translatedCompletionWords R i c) ∧
            word ∈ retainedCompletionWords R j
          )
          ∨
          (
            ∃ c d : Fin n,
              c ∈ retainedActive R i ∧
              d ∈ retainedActive R j ∧
              word ∈ translatedCompletionWords R i c ∧
              word ∈ translatedCompletionWords R j d
          )
        ) := by
  classical
  dsimp
  have hlocal :=
    planarCanonicalCandidateBlock_local_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  have hsharedNonempty :
      (sharedBlockWords
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T i).Nonempty := by
    have hbound :=
      minimal_deficient_shared_card_ge_slack_add_one
        (fun j : ProjectionOrdered V =>
          2 ^ centreExponent (C j) t)
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        hdef hmin hi hlocal
    apply Finset.card_pos.mp
    omega
  obtain ⟨word,hwordShared⟩ := hsharedNonempty
  have hshape :
      ∀ v : ProjectionOrdered V,
        CandidateBlockShape
          (planarStandardResidualColoring
            hp hcap hn hdelta0 (by linarith) ht hlam)
          (planarCanonicalCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          v := by
    intro v
    exact planarCanonicalCandidateBlock_shape
      hp hcap hn hdelta0 hdeltaHalf ht hlam C v
  obtain ⟨j,hjT,hji,hcases⟩ :=
    shared_candidate_collision_four_way
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam)
      (planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
      hshape hwordShared
  exact ⟨word,j,hjT,hji,hcases⟩

#print axioms planarCanonicalCandidateBlock_shape
#print axioms planar_lowerBranch_capacity_of_canonicalBlock_expansion
#print axioms planar_canonical_expansion_failure_minimal_core
#print axioms planar_minimal_core_vertex_has_four_way_collision

end
end ProjectionOrdered
end JSP000404Research
