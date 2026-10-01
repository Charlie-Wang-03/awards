import JSP000404Research.PlanarResidualHardRemainder
import JSP000404Research.ProjectionLossFlipCoordinate
import JSP000404Research.ResidualLocalCandidateCapacity
import Mathlib.Tactic

/-!
# Canonical planar candidate blocks with explicit loss semantics

The earlier existential local-candidate theorem is enough for Hall in
principle, but hides whether a chosen doubled block came from a projected-loss
vertex.

For the global collision analysis we choose the block family explicitly.

* non-loss vertex v:
      B(v) = Q_v;
* projected-loss vertex v:
      choose one planar retained-active flip coordinate c(v) and set
      B(v) = Q_v union flip_{c(v)}(Q_v).

The chosen coordinate is retained-active by construction.  Every block has
cardinality at least the target mass, and a doubled block occurs exactly in the
projected-loss branch of the definition.
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

noncomputable def planarCanonicalLossCoordinate
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
    (i : ProjectionOrdered V)
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    Fin n := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hloss' : i ∈ projectedLossVertices R exponent := by
    simpa [R, exponent] using hloss
  obtain ⟨c,hc,_hexit⟩ :=
    planar_projectedLoss_has_retained_active_flip_coordinate
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      (by simpa [R, exponent] using hloss')
  exact c

theorem planarCanonicalLossCoordinate_active
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
    (i : ProjectionOrdered V)
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    planarCanonicalLossCoordinate
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i hloss
      ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam) i := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hloss' : i ∈ projectedLossVertices R exponent := by
    simpa [R, exponent] using hloss
  have hchosen :=
    Classical.choose_spec
      (show ∃ c : Fin n,
          c ∈ retainedActive R i ∧
          ∀ word : Fin n → Bool,
            word ∈ retainedCompletionWords R i →
            let y := flipBoolWordAt word c
            ((completionFibre R y).card = 0)
            ∨
            ((completionFibre R y).card = 1 ∨
              (completionFibre R y).card = 2) ∧
              ∀ w : ProjectionOrdered V,
                y ∈ retainedCompletionWords R w →
                w ≠ i ∧
                c ∈ retainedActive R w ∧
                retainedBit R w c =
                  !(retainedBit R i c) by
        exact planar_projectedLoss_uniform_augmenting_coordinate
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
          (by simpa [R, exponent] using hloss'))
  -- The chosen coordinate in the definition is propositionally the same
  -- witness supplied by the existential theorem.
  simpa [planarCanonicalLossCoordinate, R, exponent] using hchosen.1

noncomputable def planarCanonicalCandidateBlock
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
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  if hloss : i ∈ projectedLossVertices R exponent then
    exact doubledCompletionBlock R i
      (planarCanonicalLossCoordinate
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        (by simpa [R, exponent] using hloss))
  else
    exact retainedCompletionWords R i

theorem planarCanonicalCandidateBlock_loss
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
    (i : ProjectionOrdered V)
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      =
    doubledCompletionBlock
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam)
      i
      (planarCanonicalLossCoordinate
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i hloss) := by
  classical
  simp [planarCanonicalCandidateBlock, hloss]

theorem planarCanonicalCandidateBlock_nonloss
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
    (i : ProjectionOrdered V)
    (hnloss :
      i ∉ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C)) :
    planarCanonicalCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      =
    retainedCompletionWords
      (planarStandardResidualColoring
        hp hcap hn hdelta0 (by linarith) ht hlam) i := by
  classical
  simp [planarCanonicalCandidateBlock, hnloss]

theorem planarCanonicalCandidateBlock_local_capacity
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
        (planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card := by
  classical
  intro i
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hexp :
      ∀ j, exponent j ≤ n :=
    planarCentreExponent_le_n
      hp hn hdelta0 (by linarith) ht C
  have hone :
      ∀ j, (active R j).card ≤ n - exponent j + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 (by linarith) ht hlam C
  have hprofile :=
    exponent_le_projectedFree_add_one
      R exponent hexp hone
  by_cases hloss : i ∈ projectedLossVertices R exponent
  · have hc :=
      planarCanonicalLossCoordinate_active
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i
        (by simpa [R, exponent] using hloss)
    rw [show
      planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i =
        doubledCompletionBlock R i
          (planarCanonicalLossCoordinate
            hp hcap hn hdelta0 hdeltaHalf ht hlam C i
            (by simpa [R, exponent] using hloss)) by
      simpa [R, exponent] using
        planarCanonicalCandidateBlock_loss
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
          (by simpa [R, exponent] using hloss)]
    rw [projectedLoss_doubledBlock_card_eq_target
      R exponent hloss hc]
    rfl
  · have hneq : exponent i ≠ projectedFree R i + 1 := by
      intro h
      exact hloss
        ((mem_projectedLossVertices R exponent i).2 h)
    have hle : exponent i ≤ projectedFree R i := by
      have h := hprofile i
      omega
    rw [show
      planarCanonicalCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i =
        retainedCompletionWords R i by
      simpa [R, exponent] using
        planarCanonicalCandidateBlock_nonloss
          hp hcap hn hdelta0 hdeltaHalf ht hlam C i
          (by simpa [R, exponent] using hloss)]
    exact nonloss_completionBlock_target_le
      R exponent hle

#print axioms planarCanonicalLossCoordinate_active
#print axioms planarCanonicalCandidateBlock_loss
#print axioms planarCanonicalCandidateBlock_nonloss
#print axioms planarCanonicalCandidateBlock_local_capacity

end
end ProjectionOrdered
end JSP000404Research
