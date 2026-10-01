import JSP000404Research.ResidualEnlargedCandidateHall
import JSP000404Research.PlanarResidualHardRemainder
import JSP000404Research.ProjectionStandardBandBudget
import Mathlib.Tactic

/-!
# Planar lower branch via enlarged all-active loss candidate blocks

Instantiate the enlarged residual candidate family in the genuine planar
standard residual colouring.

For a planar lower-branch centre i:

* if i is not projected-loss, use the retained completion cube Q_i;
* if i is projected-loss, use Q_i together with every active one-coordinate
  translate.

The planar exponent satisfies exponent(i)<n and the one-layer active-colour
bound, so every enlarged block contains at least 2^exponent(i) Boolean words.

Weighted subset expansion of this explicit family therefore implies the sharp
all-N lower-branch dyadic capacity.
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

noncomputable def planarEnlargedCandidateBlock
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
  exact enlargedProjectedCandidateBlock R exponent i

theorem planarEnlargedCandidateBlock_local_capacity
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
    2 ^ centreExponent (C i) t ≤
      (planarEnlargedCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ j : ProjectionOrdered V, exponent j < n := by
    intro j
    simpa [exponent, planarCentreExponent] using
      (centreExponent_lt_n
        (C j) n delta t hn hdelta0 hdelta1 ht)
  have hexp :
      ∀ j : ProjectionOrdered V, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt (hexpLt j)
  have hone :
      ∀ j, (active R j).card ≤ n - exponent j + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      R exponent hexpLt hexp hone i
  simpa [planarEnlargedCandidateBlock,R,exponent,
    planarCentreExponent] using hlocal

theorem planar_lowerBranch_capacity_of_enlargedBlock_expansion
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
        (∑ i ∈ S, 2 ^ centreExponent (C i) t) ≤
          (S.biUnion
            (planarEnlargedCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  exact dyadic_capacity_of_vertex_block_expansion
    (fun i : ProjectionOrdered V =>
      centreExponent (C i) t)
    (planarEnlargedCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C)
    hExpansion

theorem planar_enlarged_expansion_failure_minimal_core
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
        (∑ i ∈ S, 2 ^ centreExponent (C i) t) ≤
          (S.biUnion
            (planarEnlargedCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    ∃ T : Finset (ProjectionOrdered V),
      T.Nonempty ∧
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T ∧
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hfail' :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ exponent i) ≤
          (S.biUnion
            (enlargedProjectedCandidateBlock R exponent)).card := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hfail
  obtain ⟨T,hT,hdef,hmin⟩ :=
    exists_minimal_enlargedCandidate_deficient_core
      R exponent hfail'
  refine ⟨T,hT,?_,?_⟩
  · simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hdef
  · intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hmin U hUT

#print axioms planarEnlargedCandidateBlock_local_capacity
#print axioms planar_lowerBranch_capacity_of_enlargedBlock_expansion
#print axioms planar_enlarged_expansion_failure_minimal_core

end
end ProjectionOrdered
end JSP000404Research
