import JSP000404Research.ActualEarliestBicolourNonlocalBarrier
import Mathlib.Tactic

/-!
# Necessary active-incidence rectangles for actual eighth-source exterior holes

This bridges a genuine original earliest-prior duplicate record to a
four-edge K₂,₂ pattern in the *original* incidence relation
  loss vertex × retained active colour.
Both vertices are genuine projected-loss owners, not artificial edge slots.
The proof is arbitrary-width and imports the certified source-owner
cross-activity theorem. It does NOT provide the missing global payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A REAL locally payable original earliest-prior opposite word forces
two different ORIGINAL projected-loss centres sharing two different
retained-active colours. This is a K₂,₂ in the original
(vertex, active-colour) incidence graph, not in the auxiliary C4 graph. -/
theorem actual_earliest_exterior_forces_original_active_rectangle
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (q : Fin n → Bool)
    (hq : q ∈ actualLossEarliestEligibleLocalHoles C exponent choice) :
    ∃ v u : V, ∃ c d : Fin n,
      v ≠ u ∧ c ≠ d ∧
      v ∈ projectedLossVertices C exponent ∧
      u ∈ projectedLossVertices C exponent ∧
      c ∈ retainedActive C v ∧
      c ∈ retainedActive C u ∧
      d ∈ retainedActive C v ∧
      d ∈ retainedActive C u := by
  classical
  have hpair : q ∈
      actualLossEarliestOppositeCandidateWords C exponent choice ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := hq
  obtain ⟨himage, hhole⟩ := Finset.mem_inter.mp hpair
  change q ∈
    (actualEarliestLossCollisionRecords C exponent choice).image
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) at himage
  obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp himage
  have hqRecord :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    rw [hqa]
    exact hhole
  obtain ⟨v,u,hne,hv,hu,hvc,hvd,huc,hud,_,_⟩ :=
    actual_earliest_exterior_record_has_two_biactive_owners
      C exponent choice hchoice a ha hqRecord
  have hcd : a.1 ≠ a.2.1 :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).1
  exact ⟨v,u,a.1,a.2.1,hne,hcd,hv,hu,hvc,huc,hvd,hud⟩

/-- If the original loss-centre/active-colour incidence graph has no
K₂,₂, there are no eligible eighth-source *local* true-hole credits.
In particular, any numerical eighth-debt must be paid entirely outside
this local square mechanism. -/
theorem actual_earliest_no_original_rectangle_no_local_credit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hnoRectangle : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      v ≠ u →
      ∀ c d : Fin n,
        c ∈ retainedActive C v →
        c ∈ retainedActive C u →
        d ∈ retainedActive C v →
        d ∈ retainedActive C u →
        c = d) :
    actualLossEarliestEligibleLocalHoles C exponent choice = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  obtain ⟨v,u,c,d,hne,hcd,hv,hu,hvc,huc,hvd,hud⟩ :=
    actual_earliest_exterior_forces_original_active_rectangle
      C exponent choice hchoice q hq
  exact hcd (hnoRectangle v u hv hu hne c d hvc huc hvd hud)

#print axioms actual_earliest_exterior_forces_original_active_rectangle
#print axioms actual_earliest_no_original_rectangle_no_local_credit

end OrderedEdgeColoring
end JSP000404Research
