import JSP000404Research.ActualEarliestSourceExteriorCrossActivity
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Necessary two-bicolour-owner condition for an ORIGINAL exterior eighth-debt hole

This result concerns the original earliest-prior collision records, not a
proxy edge-carrier family.  If there are not two different projected-loss
centres which EACH retain two different colours, no canonical opposite
candidate can be a genuine exterior hole.  Consequently, ALL such
candidates belong to the actual O \\ H nonlocal-defect term.

This is an obstruction, not a construction of surplus credit.  It does
NOT prove the all-eight-source planar payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Under the original choice-active contract, if every pair of distinct
projected-loss centres has a monochromatic member, an actual eighth-debt
opposite candidate is NEVER a truly exterior hole.  This is an arbitrary-
width result, with no exponent, ambient-cardinality, or AngleCap bound. -/
theorem actual_eighth_exterior_requires_two_bicolour_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hnoPair : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      v ≠ u →
      (∀ c d : Fin n, c ∈ retainedActive C v →
        d ∈ retainedActive C v → c = d) ∨
      (∀ c d : Fin n, c ∈ retainedActive C u →
        d ∈ retainedActive C u → c = d))
    (q : Fin n → Bool)
    (hq : q ∈ actualLossEarliestOppositeCandidateWords C exponent choice) :
    q ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  classical
  intro hhole
  change q ∈
    (actualEarliestLossCollisionRecords C exponent choice).image
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) at hq
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hq
  have hqRecord :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    simpa only [heq] using hhole
  obtain ⟨v,u,hne,hv,hu,hvc,hvd,huc,hud,_,_⟩ :=
    actual_earliest_exterior_record_has_two_biactive_owners
      C exponent choice hchoice a ha hqRecord
  have hcolNe : a.1 ≠ a.2.1 :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).1
  rcases hnoPair v u hv hu hne with hmonoV | hmonoU
  · exact hcolNe (hmonoV a.1 a.2.1 hvc hvd)
  · exact hcolNe (hmonoU a.1 a.2.1 huc hud)

/-- Exact nonlocal-defect accounting in the same regime: every
candidate is an ineligible original opposite word (O \\ H = O).
No hole is silently created or spent, and unrelated seven-source
payments are not assumed. -/
theorem actual_eighth_all_candidates_nonlocal_of_no_bicolour_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hnoPair : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      v ≠ u →
      (∀ c d : Fin n, c ∈ retainedActive C v →
        d ∈ retainedActive C v → c = d) ∨
      (∀ c d : Fin n, c ∈ retainedActive C u →
        d ∈ retainedActive C u → c = d)) :
    (actualLossEarliestOppositeCandidateWords C exponent choice \
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) =
      actualLossEarliestOppositeCandidateWords C exponent choice := by
  classical
  ext q
  constructor
  · intro h
    exact (Finset.mem_sdiff.mp h).1
  · intro h
    exact Finset.mem_sdiff.mpr
      ⟨h, actual_eighth_exterior_requires_two_bicolour_loss_centres
        C exponent choice hchoice hnoPair q h⟩

#print axioms actual_eighth_exterior_requires_two_bicolour_loss_centres
#print axioms actual_eighth_all_candidates_nonlocal_of_no_bicolour_pair

end OrderedEdgeColoring
end JSP000404Research
