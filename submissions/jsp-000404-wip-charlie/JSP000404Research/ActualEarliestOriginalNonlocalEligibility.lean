import JSP000404Research.ActualEarliestSourceExteriorCrossActivity
import JSP000404Research.ResidualLossCollisionDoubleFlipExactTrueHole
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Exact TRUE-HOLE eligibility of every ORIGINAL eighth-debt collision record

The previous exact two-owner eligibility iff was certified for selected
earliest-actual-edge carriers, NOT for the entire original earliest-prior
duplicate debt. Here we prove the analogous IFF for every genuine record,
with its two genuine original owner vertices.

An opposite word is a truly payable exterior hole iff both owner
cross-activity conditions hold, all third-party original cubes miss it,
and every translated-loss slice misses it.

If either source owner's opposite colour is inactive, the candidate
actually belongs to that ORIGINAL cube. We formally charge it to
the ORIGINAL ineligible-opposite nonlocal-defect set. This is a
classification of real debt, not a construction of new hole credits.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact source-native EXTERIOR hole iff for EVERY REAL earliest-prior
collision debt record (not merely selected edge carriers).
The two owners v,u are the actual original vertices supplying
the same source word through the two different loss slices. -/
theorem actual_earliest_record_exterior_iff_full_owner_eligibility
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (v u : V)
    (hv : v ∈ lossCoordinateSlice C exponent choice a.1)
    (hu : u ∈ lossCoordinateSlice C exponent choice a.2.1)
    (hw : a.2.2 ∈ translatedCompletionWords C v a.1)
    (hz : a.2.2 ∈ translatedCompletionWords C u a.2.1) :
    let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
    q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice ↔
      a.2.1 ∈ retainedActive C v ∧
      a.1 ∈ retainedActive C u ∧
      (∀ z : V, z ≠ v → z ≠ u →
        q ∉ retainedCompletionWords C z) ∧
      q ∉ translatedLossAllCoordinateWords C exponent choice := by
  classical
  dsimp only
  let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  change q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice ↔
      a.2.1 ∈ retainedActive C v ∧
      a.1 ∈ retainedActive C u ∧
      (∀ z : V, z ≠ v → z ≠ u →
        q ∉ retainedCompletionWords C z) ∧
      q ∉ translatedLossAllCoordinateWords C exponent choice
  have horder := (actual_earliest_loss_collision_record_valid
    C exponent choice a ha).2.1
  constructor
  · intro hq
    have hcrossV :=
      (actual_earliest_exterior_record_owner_other_active
        C exponent choice a ha hq v a.1 (Or.inl rfl) hv hw).1 rfl
    have hcrossU :=
      (actual_earliest_exterior_record_owner_other_active
        C exponent choice a ha hq u a.2.1 (Or.inr rfl) hu hz).2 rfl
    refine ⟨hcrossV,hcrossU,?_,(Finset.mem_sdiff.mp hq).2⟩
    intro z hz1 hz2 hzMember
    have hcovered : q ∈ coveredCompletionWords C :=
      (mem_coveredCompletionWords C q).2
        ⟨z,(mem_completionFibre C q z).2 hzMember⟩
    exact (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp hq).1).2 hcovered
  · rintro ⟨hcrossV,hcrossU,hthird,hnotLoss⟩
    have hvSource : flipBoolWordAt a.2.2 a.1 ∈
        retainedCompletionWords C v :=
      (mem_translatedCompletionWords C v a.1 a.2.2).mp hw
    have huSource : flipBoolWordAt a.2.2 a.2.1 ∈
        retainedCompletionWords C u :=
      (mem_translatedCompletionWords C u a.2.1 a.2.2).mp hz
    have hnotV : q ∉ retainedCompletionWords C v :=
      flip_active_not_mem_completion C hvSource hcrossV
    have hnotU' :
        flipBoolWordAt (flipBoolWordAt a.2.2 a.2.1) a.1 ∉
          retainedCompletionWords C u :=
      flip_active_not_mem_completion C huSource hcrossU
    have hnotU : q ∉ retainedCompletionWords C u := by
      simpa only [q, flipBoolWordAt_commute a.2.2
        (ne_of_lt horder).symm] using hnotU'
    have hnotCovered : q ∉ coveredCompletionWords C := by
      intro hcovered
      obtain ⟨z,hfib⟩ := (mem_coveredCompletionWords C q).1 hcovered
      have hmem := (mem_completionFibre C q z).1 hfib
      by_cases hz1 : z = v
      · subst z
        exact hnotV hmem
      by_cases hz2 : z = u
      · subst z
        exact hnotU hmem
      exact hthird z hz1 hz2 hmem
    have hglobal : q ∈ lossLedgerGlobalTrueHoles C :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnotCovered⟩
    exact Finset.mem_sdiff.mpr ⟨hglobal,hnotLoss⟩

/-- A REAL ORIGINAL source record which fails cross-activity at even
one of its two actual owner vertices has an opposite word covered by
an original retained cube, and the very same candidate enters the
CANONICAL nonlocal ineligible-opposite deficit set O \ H.
No synthetic tokens, missing-source assumptions or exterior credits. -/
theorem actual_earliest_cross_inactive_forces_covered_nonlocal_defect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (v u : V)
    (hv : v ∈ lossCoordinateSlice C exponent choice a.1)
    (hu : u ∈ lossCoordinateSlice C exponent choice a.2.1)
    (hw : a.2.2 ∈ translatedCompletionWords C v a.1)
    (hz : a.2.2 ∈ translatedCompletionWords C u a.2.1)
    (hfail :
      a.2.1 ∉ retainedActive C v ∨
      a.1 ∉ retainedActive C u) :
    let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
    q ∈ coveredCompletionWords C ∧
    q ∈ (actualLossEarliestOppositeCandidateWords C exponent choice \
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) := by
  classical
  dsimp only
  let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have horder := (actual_earliest_loss_collision_record_valid
    C exponent choice a ha).2.1
  have hcovered : q ∈ coveredCompletionWords C := by
    rcases hfail with hfailV | hfailU
    · have hvSource : flipBoolWordAt a.2.2 a.1 ∈
          retainedCompletionWords C v :=
        (mem_translatedCompletionWords C v a.1 a.2.2).mp hw
      have hmember : q ∈ retainedCompletionWords C v :=
        (mem_retainedCompletionWords_flip_iff_of_inactive
          C hfailV).2 hvSource
      exact (mem_coveredCompletionWords C q).2
        ⟨v,(mem_completionFibre C q v).2 hmember⟩
    · have huSource : flipBoolWordAt a.2.2 a.2.1 ∈
          retainedCompletionWords C u :=
        (mem_translatedCompletionWords C u a.2.1 a.2.2).mp hz
      have hmember' :
          flipBoolWordAt (flipBoolWordAt a.2.2 a.2.1) a.1 ∈
            retainedCompletionWords C u :=
        (mem_retainedCompletionWords_flip_iff_of_inactive
          C hfailU).2 huSource
      have hmember : q ∈ retainedCompletionWords C u := by
        simpa only [q, flipBoolWordAt_commute a.2.2
          (ne_of_lt horder).symm] using hmember'
      exact (mem_coveredCompletionWords C q).2
        ⟨u,(mem_completionFibre C q u).2 hmember⟩
  have hcandidate : q ∈
      actualLossEarliestOppositeCandidateWords C exponent choice :=
    Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hnotExterior :
      q ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    intro hq
    exact (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp hq).1).2 hcovered
  exact ⟨hcovered,Finset.mem_sdiff.mpr ⟨hcandidate,hnotExterior⟩⟩

#print axioms actual_earliest_record_exterior_iff_full_owner_eligibility
#print axioms actual_earliest_cross_inactive_forces_covered_nonlocal_defect

end OrderedEdgeColoring
end JSP000404Research
