import JSP000404Research.StrictNonlossSubsetHallCapacity
import JSP000404Research.DirectionDataOneLayerProfileAnyWidth
import Mathlib.Tactic

/-!
# Geometry gap G1 reduces to exact non-loss vertices

Strict projected-free slack already pays Hall demands on arbitrary
vertex subsets by twofold completion multiplicity.

The genuine DirectionData budget t < n+1 gives one-layer rigidity
  exponent(v) <= projectedFree(v) + 1.
Therefore any deficient enlarged candidate family must contain either:

* a projected-loss vertex, exponent(v)=projectedFree(v)+1, or
* an exact non-loss vertex, exponent(v)=projectedFree(v).

If the core is loss-free, the second case is forced.  Thus geometry gap G1
needs only exclude or compensate the exact non-loss boundary in a
loss-free deficient core.  All strictly non-loss vertices are already paid.

This is NOT an unconditional proof that exact non-loss-only cores cannot
be deficient; that remains a genuine open geometry requirement.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- At any deficient enlarged-block subset in genuine direction data,
there is a loss vertex or a precisely saturated non-loss vertex. -/
theorem deficient_true_core_has_loss_or_exact_nonloss
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    {T : Finset V}
    (hdef :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      BlockDeficient
        (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) T) :
    let B := standardResidualColoring D n (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    (∃ v ∈ T, v ∈ projectedLossVertices B k) ∨
      (∃ v ∈ T,
        v ∉ projectedLossVertices B k ∧
        k v = projectedFree B v) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  obtain ⟨v, hv, hge⟩ :=
    deficient_enlarged_core_has_exact_or_loss_profile
      B k hdef
  by_cases hvLoss : v ∈ projectedLossVertices B k
  · exact Or.inl ⟨v, hv, hvLoss⟩
  · have hprofile :=
      localCycles_standardResidual_oneLayer_profile D ht cycles
    have hexp : ∀ x, k x ≤ n := hprofile.1
    have hone :
        ∀ x, (active B x).card ≤ n - k x + 1 := hprofile.2
    have hupper :
        k v ≤ projectedFree B v + 1 :=
      exponent_le_projectedFree_add_one B k hexp hone v
    have hne : k v ≠ projectedFree B v + 1 := by
      intro hEq
      exact hvLoss
        ((mem_projectedLossVertices B k v).2 hEq)
    have heq : k v = projectedFree B v := by
      omega
    exact Or.inr ⟨v, hv, hvLoss, heq⟩

/-- A loss-free Hall-deficient core must contain at least one exact
non-loss centre. This is the sole remaining local profile type in G1. -/
theorem deficient_loss_free_core_has_exact_nonloss
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    {T : Finset V}
    (hdef :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      BlockDeficient
        (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) T)
    (hnoLoss :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      ∀ v ∈ T, v ∉ projectedLossVertices B k) :
    let B := standardResidualColoring D n (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    ∃ v ∈ T,
      v ∉ projectedLossVertices B k ∧
      k v = projectedFree B v := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  rcases deficient_true_core_has_loss_or_exact_nonloss
    D ht cycles hdef with hLoss | hExact
  · obtain ⟨v, hv, hvLoss⟩ := hLoss
    exact False.elim (hnoLoss v hv hvLoss)
  · exact hExact

#print axioms deficient_true_core_has_loss_or_exact_nonloss
#print axioms deficient_loss_free_core_has_exact_nonloss

end DirectionData
end JSP000404Research
