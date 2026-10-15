import JSP000404Research.ResidualLossCoveredOppositeBitBlocker
import Mathlib.Tactic

/-!
# Certified triple-carrier upper bound for truly blocked projected-loss mass

Any translated-loss Boolean word that remains covered after a retained-active
flip has a **different** covering centre and an opposite canonical bit at
a common retained-active coordinate.

Here we do not merely infer the existence of one such pair. We cover the
ENTIRE `translatedLossCoveredWords` set by a finite union of concrete
source--blocker--coordinate intersections, and derive a valid cardinal
upper bound by their sum.

This is an unconditional finite combinatorial inequality under the original
one-layer hypotheses and active choice. It is NOT a payment into real holes;
intersections for different triples can overlap and are never counted as
disjoint without proof.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A genuine covered-loss obstruction carrier consists of a source loss
vertex, a different blocker, and a common active retained coordinate with
opposite canonical bits. -/
noncomputable def lossCoveredBlockerTriples
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset ((V × V) × Fin n) := by
  classical
  exact Finset.univ.filter (fun z =>
    z.1.1 ∈ projectedLossVertices C exponent ∧
    z.1.1 ≠ z.1.2 ∧
    z.2 ∈ retainedActive C z.1.1 ∧
    z.2 ∈ retainedActive C z.1.2 ∧
    retainedBit C z.1.2 z.2 = !(retainedBit C z.1.1 z.2))

/-- Concrete translated-block intersection carried by a source/blocker
pair at one common retained-active coordinate. -/
noncomputable def lossCoveredBlockerTripleWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (z : (V × V) × Fin n) : Finset (Fin n → Bool) :=
  translatedCompletionWords C z.1.1 z.2 ∩
    retainedCompletionWords C z.1.2

theorem translatedLossCovered_subset_real_blockerTriple_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    translatedLossCoveredWords C exponent choice ⊆
      (lossCoveredBlockerTriples C exponent).biUnion
        (lossCoveredBlockerTripleWords C) := by
  classical
  intro word hcovered
  obtain ⟨v, hv, w, hvw, c, hcv, hcw, hop, hsource, hblock⟩ :=
    translatedLossCoveredWord_has_opposite_active_bits
      C exponent hexp honeLoss choice hchoice hcovered
  apply Finset.mem_biUnion.mpr
  refine ⟨((v, w), c), ?_, ?_⟩
  · simp [lossCoveredBlockerTriples,
      hv, hvw, hcv, hcw, hop]
  · exact Finset.mem_inter.mpr ⟨hsource, hblock⟩

/-- A precise finite *upper* bound for all covered-loss words in terms
of genuine opposite-bit source/blocker/coordinate intersections. No
cardinality disjointness is assumed for different triples. -/
theorem translatedLossCovered_card_le_real_blockerTriple_mass
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
      ∑ z ∈ lossCoveredBlockerTriples C exponent,
        (lossCoveredBlockerTripleWords C z).card := by
  classical
  have hsub :=
    translatedLossCovered_subset_real_blockerTriple_union
      C exponent hexp honeLoss choice hchoice
  calc
    (translatedLossCoveredWords C exponent choice).card ≤
        ((lossCoveredBlockerTriples C exponent).biUnion
          (lossCoveredBlockerTripleWords C)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ z ∈ lossCoveredBlockerTriples C exponent,
        (lossCoveredBlockerTripleWords C z).card :=
      Finset.card_biUnion_le

#print axioms translatedLossCovered_subset_real_blockerTriple_union
#print axioms translatedLossCovered_card_le_real_blockerTriple_mass

end OrderedEdgeColoring
end JSP000404Research
