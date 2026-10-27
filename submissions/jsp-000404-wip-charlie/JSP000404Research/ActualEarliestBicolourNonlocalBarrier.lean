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

/-- A genuine ORIGINAL eighth-lane exterior candidate gives an actual
two-by-two active rectangle on two distinct original projected-loss
centres. Unlike the no-bicolour-pair contrapositive, this statement
provides positive, named vertex and colour witnesses for downstream
cardinality and geometric arguments. It does not construct a hole. -/
theorem actual_eighth_exterior_candidate_has_biactive_rectangle
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (q : Fin n → Bool)
    (hq : q ∈ actualLossEarliestOppositeCandidateWords C exponent choice ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    ∃ v u : V,
      v ≠ u ∧
      v ∈ projectedLossVertices C exponent ∧
      u ∈ projectedLossVertices C exponent ∧
      ∃ c d : Fin n,
        c ≠ d ∧
        c ∈ retainedActive C v ∧
        d ∈ retainedActive C v ∧
        c ∈ retainedActive C u ∧
        d ∈ retainedActive C u := by
  classical
  obtain ⟨hsrc, hhole⟩ := Finset.mem_inter.mp hq
  change q ∈
    (actualEarliestLossCollisionRecords C exponent choice).image
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) at hsrc
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hsrc
  have hreal :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    simpa only [heq] using hhole
  obtain ⟨v, u, hne, hv, hu, hvc, hvd, huc, hud, _, _⟩ :=
    actual_earliest_exterior_record_has_two_biactive_owners
      C exponent choice hchoice a ha hreal
  have hcd : a.1 ≠ a.2.1 :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).1
  exact ⟨v, u, hne, hv, hu, a.1, a.2.1,
    hcd, hvc, hvd, huc, hud⟩

/-- At least TWO distinct genuinely projected-loss centres must each
carry two different retained-active colours before even ONE actual
eighth-source opposite candidate can be a true exterior hole.
This quantitative necessary condition holds at every width and for
arbitrary original exponent data, conditional only on the original
active-choice contract. -/
theorem actual_eighth_exterior_candidate_forces_two_biactive_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (q : Fin n → Bool)
    (hq : q ∈ actualLossEarliestOppositeCandidateWords C exponent choice ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    2 ≤ ((projectedLossVertices C exponent).filter (fun v =>
      ∃ c d : Fin n,
        c ≠ d ∧
        c ∈ retainedActive C v ∧
        d ∈ retainedActive C v)).card := by
  classical
  obtain ⟨v, u, hne, hv, hu, c, d, hcd,
    hvc, hvd, huc, hud⟩ :=
    actual_eighth_exterior_candidate_has_biactive_rectangle
      C exponent choice hchoice q hq
  let T : Finset V := (projectedLossVertices C exponent).filter (fun w =>
    ∃ c d : Fin n,
      c ≠ d ∧
      c ∈ retainedActive C w ∧
      d ∈ retainedActive C w)
  have hvT : v ∈ T :=
    Finset.mem_filter.mpr ⟨hv, ⟨c, d, hcd, hvc, hvd⟩⟩
  have huT : u ∈ T :=
    Finset.mem_filter.mpr ⟨hu, ⟨c, d, hcd, huc, hud⟩⟩
  have hsubset : ({v, u} : Finset V) ⊆ T := by
    intro w hw
    rcases Finset.mem_insert.mp hw with hwv | hwu
    · rw [hwv]
      exact hvT
    · have hwu' : w = u := Finset.mem_singleton.mp hwu
      rw [hwu']
      exact huT
  have htwo : ({v, u} : Finset V).card = 2 := by
    simp [hne, hne.symm]
  have hle : ({v, u} : Finset V).card ≤ T.card :=
    Finset.card_le_card hsubset
  change 2 ≤ T.card
  omega

/-- Concrete closed subcase of the ORIGINAL eighth-source local
eligibility problem: if at most one actual projected-loss centre retains
two distinct colours, then NO original opposite candidate is an exterior
true Boolean hole. This is not a claim that other source debts vanish. -/
theorem actual_eighth_no_local_exterior_of_biactive_card_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n,
          c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v)).card ≤ 1) :
    actualLossEarliestOppositeCandidateWords C exponent choice ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice = ∅ := by
  classical
  ext q
  constructor
  · intro hq
    have htwo :=
      actual_eighth_exterior_candidate_forces_two_biactive_centres
        C exponent choice hchoice q hq
    omega
  · intro hq
    exact (Finset.not_mem_empty q hq).elim

/-- In the same count-controlled subcase, ALL genuine original eighth
opposite candidates lie in the actual nonlocal-ineligible deficit
O \ H; NONE can be silently booked as local exterior payment. -/
theorem actual_eighth_all_nonlocal_of_biactive_card_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n,
          c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v)).card ≤ 1) :
    (actualLossEarliestOppositeCandidateWords C exponent choice \
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) =
      actualLossEarliestOppositeCandidateWords C exponent choice := by
  classical
  have hEmpty :=
    actual_eighth_no_local_exterior_of_biactive_card_le_one
      C exponent choice hchoice hsmall
  ext q
  constructor
  · intro h
    exact (Finset.mem_sdiff.mp h).1
  · intro hq
    have hnot : q ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
      intro hh
      have hboth : q ∈
          actualLossEarliestOppositeCandidateWords C exponent choice ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice :=
        Finset.mem_inter.mpr ⟨hq, hh⟩
      rw [hEmpty] at hboth
      exact Finset.not_mem_empty q hboth
    exact Finset.mem_sdiff.mpr ⟨hq, hnot⟩

#print axioms actual_eighth_no_local_exterior_of_biactive_card_le_one
#print axioms actual_eighth_all_nonlocal_of_biactive_card_le_one

#print axioms actual_eighth_exterior_candidate_has_biactive_rectangle
#print axioms actual_eighth_exterior_candidate_forces_two_biactive_centres

#print axioms actual_eighth_exterior_requires_two_bicolour_loss_centres
#print axioms actual_eighth_all_candidates_nonlocal_of_no_bicolour_pair

end OrderedEdgeColoring
end JSP000404Research
