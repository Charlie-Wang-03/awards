import JSP000404Research.ResidualLossCoveredExactTripleLedger
import Mathlib.Tactic

/-!
# Local dyadic size bounds for actual covered-loss blocker carriers

An individual actual source--blocker intersection is simultaneously
contained in the translated source completion cube and in the blocker's
original completion cube. Therefore its size is bounded by the minimum
of their (dyadic) cardinalities, with NO independence assumption.

This supplies a genuine quantitative upper bound for the EXACT
chosen-coordinate blocker-triple union, without treating carrier
intersections as disjoint or turning covered words into true holes.

The final global surplus-versus-debt inequality remains unproved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The intersection for one concrete loss source and blocker cannot
exceed either endpoint completion-cube capacity. -/
theorem lossCoveredBlockerTripleWords_card_le_min_dyadic
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (z : (V × V) × Fin n) :
    (lossCoveredBlockerTripleWords C z).card ≤
      min (2 ^ projectedFree C z.1.1)
          (2 ^ projectedFree C z.1.2) := by
  classical
  have hsource :
      (lossCoveredBlockerTripleWords C z).card ≤
        (translatedCompletionWords C z.1.1 z.2).card := by
    exact Finset.card_le_card (Finset.inter_subset_left)
  have hblock :
      (lossCoveredBlockerTripleWords C z).card ≤
        (retainedCompletionWords C z.1.2).card := by
    exact Finset.card_le_card (Finset.inter_subset_right)
  rw [translatedCompletionWords_card,
    retainedCompletionWords_card] at hsource
  rw [retainedCompletionWords_card] at hblock
  exact le_min hsource hblock

/-- Every genuine covered translated-loss word is quantitatively
charged to a concrete opposite-bit carrier with dyadic capacity at
most the minimum free-coordinate budget of the two owners.
This remains an UPPER BOUND, not a hole injection. -/
theorem translatedLossCovered_card_le_chosenTriple_min_dyadic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    (translatedLossCoveredWords C exponent choice).card ≤
      ∑ z ∈ chosenLossCoveredBlockerTriples C exponent choice,
        min (2 ^ projectedFree C z.1.1)
            (2 ^ projectedFree C z.1.2) := by
  classical
  calc
    (translatedLossCoveredWords C exponent choice).card ≤
        ∑ z ∈ chosenLossCoveredBlockerTriples C exponent choice,
          (lossCoveredBlockerTripleWords C z).card :=
      translatedLossCovered_card_le_chosenTriple_mass
        C exponent hexp honeLoss choice hchoice
    _ ≤ ∑ z ∈ chosenLossCoveredBlockerTriples C exponent choice,
        min (2 ^ projectedFree C z.1.1)
            (2 ^ projectedFree C z.1.2) := by
      apply Finset.sum_le_sum
      intro z hz
      exact lossCoveredBlockerTripleWords_card_le_min_dyadic C z

#print axioms lossCoveredBlockerTripleWords_card_le_min_dyadic
#print axioms translatedLossCovered_card_le_chosenTriple_min_dyadic

end OrderedEdgeColoring
end JSP000404Research
