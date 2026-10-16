import JSP000404Research.ProjectionLocalCandidateCapacity
import JSP000404Research.WeightedBlockHallOutlet
import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

set_option maxHeartbeats 1000000

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

-- The projection order depends on hp; it must be bound locally where used.
-- A typeclass instance with hp as an uninferable parameter is invalid.

noncomputable def planarLowerCandidateBlock
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V) :
    Finset (Fin n → Bool) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
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
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
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
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
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
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hExpansion :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t)
          ≤
        (S.biUnion
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
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
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∀ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t ≤
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  intro i
  have hspec :=
    planarLowerCandidateBlock_spec
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  simpa using hspec.1


/-- Every genuine failure of the planar lower-branch dyadic capacity
produces an inclusion-minimal deficient subset of the *actual chosen*
single-flip completion blocks.  Local capacity rules out singleton cores,
so the obstruction necessarily involves at least two distinct centres. -/
theorem planar_lowerBranch_overweight_has_nontrivial_candidate_core
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (C i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∃ T : Finset (ProjectionOrdered V),
      2 ≤ T.card ∧
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C) T
      ∧
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarLowerCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C) U := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (C i) t
  let blocks : ProjectionOrdered V → Finset (Fin n → Bool) :=
    planarLowerCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C
  have hfail :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ exponent i) ≤ (S.biUnion blocks).card := by
    intro hexpansion
    have hcap' :=
      planar_lowerBranch_capacity_of_candidateBlock_expansion
        hp hcap hn hdelta0 hdeltaHalf ht hlam C
        (by simpa [exponent, blocks] using hexpansion)
    omega
  push_neg at hfail
  obtain ⟨S, hS⟩ := hfail
  have hdefS :
      BlockDeficient (fun i => 2 ^ exponent i) blocks S := by
    exact hS
  obtain ⟨T, _hTS, hdefT, hminT⟩ :=
    exists_minimal_deficient_subset
      (fun i : ProjectionOrdered V => 2 ^ exponent i)
      blocks hdefS
  have hnonempty : T.Nonempty := by
    exact deficient_set_nonempty_of_positive_demands
      (fun i : ProjectionOrdered V => 2 ^ exponent i)
      blocks (fun i => by positivity) hdefT
  have hpos : 0 < T.card := Finset.card_pos.mpr hnonempty
  have hlocal : ∀ i, 2 ^ exponent i ≤ (blocks i).card := by
    intro i
    exact planar_lowerBranch_candidateBlock_local_capacity
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
  have hnotone : T.card ≠ 1 := by
    intro hcard
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    subst T
    have hbound := hlocal v
    unfold BlockDeficient at hdefT
    simp only [Finset.sum_singleton] at hdefT
    have hblockEq :
        ({v} : Finset (ProjectionOrdered V)).biUnion blocks = blocks v := by
      ext word
      simp only [Finset.mem_biUnion, Finset.mem_singleton]
      constructor
      · rintro ⟨u, rfl, hw⟩
        exact hw
      · intro hw
        exact ⟨v, rfl, hw⟩
    rw [hblockEq] at hdefT
    omega
  have htwo : 2 ≤ T.card := by omega
  exact ⟨T, htwo,
    (by simpa only [exponent, blocks] using hdefT),
    (by
      intro U hUT
      simpa only [exponent, blocks] using hminT U hUT)⟩

#print axioms planar_lowerBranch_overweight_has_nontrivial_candidate_core

#print axioms planarLowerCandidateBlock_spec
#print axioms planar_lowerBranch_capacity_of_candidateBlock_expansion
#print axioms planar_lowerBranch_candidateBlock_local_capacity

end
end ProjectionOrdered
end JSP000404Research
