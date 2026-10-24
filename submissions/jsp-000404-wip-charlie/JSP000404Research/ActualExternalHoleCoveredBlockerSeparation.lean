import JSP000404Research.ResidualLossActualEdgeCarrierFrontier
import JSP000404Research.ResidualLossExternalHoleBudget
import Mathlib.Tactic

/-!
# REAL blocker words cannot be redeemed as TRUE exterior Boolean holes

Unlike a purely numerical debt-counting inequality, this is an actual
set-theoretic nonreuse theorem in the original retained completion cubes.

For any genuinely active choice under the certified exponent/one-layer
hypotheses, the union of all ACTUAL same-colour source/blocker/flip
triple words is contained in the original globally COVERED set and
therefore disjoint from TRUE holes OUTSIDE ALL translated-loss slices.

This closes an invalid shortcut: the same blocker word is NEVER a
hole credit. It does not produce substitute external holes and does
not solve the all-cardinality geometric payment existence problem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every actual covered-loss blocker triple word is ALREADY globally
covered, regardless of how many triples witness the same word. -/
theorem actual_blocker_triple_union_subset_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (hexp : ∀ v, k v ≤ n)
    (honeLoss : ∀ v, (active B v).card ≤ n - k v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices B k,
      choice v ∈ retainedActive B v) :
    (chosenLossActualEdgeBlockerTriples B k choice).biUnion
      (lossCoveredBlockerTripleWords B) ⊆
      coveredCompletionWords B := by
  intro w hw
  have hword : w ∈ translatedLossCoveredWords B k choice := by
    rw [translatedLossCovered_eq_actualEdgeTriple_union
      B k hexp honeLoss choice hchoice]
    exact hw
  exact (Finset.mem_inter.mp hword).2

/-- Real already-covered blocker words and real outside-translated holes
have literally NO common Boolean word, even before cardinality estimates.
The no-reuse obstruction holds for the full union, not individual triples. -/
theorem actual_blocker_triple_union_disjoint_external_true_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (hexp : ∀ v, k v ≤ n)
    (honeLoss : ∀ v, (active B v).card ≤ n - k v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices B k,
      choice v ∈ retainedActive B v) :
    Disjoint
      ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
        (lossCoveredBlockerTripleWords B))
      (lossLedgerOutsideTranslatedTrueHoles B k choice) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hblock hh
  have hcovered :=
    actual_blocker_triple_union_subset_covered
      B k hexp honeLoss choice hchoice hblock
  have hglobal :
      w ∈ lossLedgerGlobalTrueHoles B :=
    (Finset.mem_sdiff.mp hh).1
  have hnotCovered :
      w ∉ coveredCompletionWords B :=
    (Finset.mem_sdiff.mp hglobal).2
  exact hnotCovered hcovered

#print axioms actual_blocker_triple_union_subset_covered
#print axioms actual_blocker_triple_union_disjoint_external_true_holes

end OrderedEdgeColoring
end JSP000404Research
