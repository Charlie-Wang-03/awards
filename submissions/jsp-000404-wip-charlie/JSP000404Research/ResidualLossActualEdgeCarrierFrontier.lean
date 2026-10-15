import JSP000404Research.ResidualLossBlockerEdgeColourRigidity
import JSP000404Research.ResidualLossBlockerTripleLocalCapacity
import Mathlib.Tactic

/-!
# Exact projected-loss covered mass on true same-colour retained edges

We remove false-positive blocker triples from the previous exact
chosen-coordinate carrier cover. A covered translated word is only
possible if its source and blocker are directly joined by a retained
edge of precisely the chosen flip coordinate.

This is an EXACT set equality, not merely a broader upper bound:
   covered-loss = union of actual-edge source/blocker intersections.

It implies a strictly more restrictive quantitative dyadic upper bound
indexed only by genuinely eligible coloured original edges. No
geometric AngleCap exclusion or global nonreuse allocation is assumed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def chosenLossActualEdgeBlockerTriples
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Finset ((V × V) × Fin n) := by
  classical
  exact (chosenLossCoveredBlockerTriples C exponent choice).filter
    (fun z =>
      (∃ hvw : z.1.1 < z.1.2,
        ∃ hret : (C.color z.1.1 z.1.2).val < n,
          retainedColor C z.1.1 z.1.2 hret = z.2) ∨
      (∃ hwv : z.1.2 < z.1.1,
        ∃ hret : (C.color z.1.2 z.1.1).val < n,
          retainedColor C z.1.2 z.1.1 hret = z.2))

theorem translatedLossCovered_eq_actualEdgeTriple_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    translatedLossCoveredWords C exponent choice =
      (chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
        (lossCoveredBlockerTripleWords C) := by
  classical
  rw [translatedLossCovered_eq_chosenTriple_union
    C exponent hexp honeLoss choice hchoice]
  apply Finset.Subset.antisymm
  · intro word hword
    obtain ⟨⟨⟨v, w⟩, c⟩, hz, hinter⟩ :=
      Finset.mem_biUnion.mp hword
    have hdata :
        v ∈ projectedLossVertices C exponent ∧
        v ≠ w ∧ choice v = c ∧
        c ∈ retainedActive C v ∧
        c ∈ retainedActive C w ∧
        retainedBit C w c = !(retainedBit C v c) :=
      (Finset.mem_filter.mp hz).2
    have hvT :
        word ∈ translatedCompletionWords C v c :=
      (Finset.mem_inter.mp hinter).1
    have hw :
        word ∈ retainedCompletionWords C w :=
      (Finset.mem_inter.mp hinter).2
    have hed :=
      loss_translated_blocker_edge_colour_eq_flip
        C exponent hexp honeLoss hdata.1 hdata.2.1 hvT hw
    apply Finset.mem_biUnion.mpr
    refine ⟨((v, w), c), ?_, hinter⟩
    exact Finset.mem_filter.mpr ⟨hz, hed⟩
  · intro word hword
    obtain ⟨z, hz, hinter⟩ := Finset.mem_biUnion.mp hword
    exact Finset.mem_biUnion.mpr
      ⟨z, (Finset.mem_filter.mp hz).1, hinter⟩

/-- Exact edge rigidity permits a more restrictive local dyadic
bound than the broad all-opposite-bit triple sum. No carrier
disjointness is used. -/
theorem translatedLossCovered_card_le_actualEdgeTriple_dyadic
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
      ∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
        min (2 ^ projectedFree C z.1.1)
            (2 ^ projectedFree C z.1.2) := by
  classical
  rw [translatedLossCovered_eq_actualEdgeTriple_union
    C exponent hexp honeLoss choice hchoice]
  calc
    ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
      (lossCoveredBlockerTripleWords C)).card ≤
        ∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
          (lossCoveredBlockerTripleWords C z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
          min (2 ^ projectedFree C z.1.1)
              (2 ^ projectedFree C z.1.2) := by
      apply Finset.sum_le_sum
      intro z hz
      exact lossCoveredBlockerTripleWords_card_le_min_dyadic C z

#print axioms translatedLossCovered_eq_actualEdgeTriple_union
#print axioms translatedLossCovered_card_le_actualEdgeTriple_dyadic

end OrderedEdgeColoring
end JSP000404Research
