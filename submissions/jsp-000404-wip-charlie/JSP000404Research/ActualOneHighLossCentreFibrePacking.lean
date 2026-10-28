import JSP000404Research.ActualAnyWidthHighExponentReuseGate
import JSP000404Research.ResidualLossCanonicalOppositeFibreBound
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Actual opposite-fibre injection into LOW-exponent original loss centres

Unlike earlier 2m <= |L| packing assuming ALL exponents <=2,
the new high-exponent collision reuse obstruction yields a DIFFERENT
bound valid even with arbitrarily HIGH exponents:

  if at most ONE genuine loss centre has exponent >=3,
  every actual opposite-candidate collision fibre injects into
  ACTUAL low-exponent (<=2) projected-loss centres.

Each earliest-prior record has two distinct actual cube owners,
so at least ONE owner is low when the high pool has cardinal <=1.
No low owner can support source records with the same opposite
target twice: otherwise the proven shared-owner high-exponent gate
would force its exponent >=3. Choose one real low owner for each
record and obtain a genuine injection.

This is the first mixed-profile fibre packing rule; no exterior
Boolean hole or unreserved surplus is invented.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Even when some original loss exponents are >2, provided at
most ONE actual loss centre has exponent >=3, the number of original
earliest-prior source records claiming any one opposite word is bounded
by the number of distinct ACTUAL low-exponent loss centres. -/
theorem actual_one_high_loss_centre_opposite_fibre_le_low_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hhigh :
      ((projectedLossVertices C exponent).filter
        (fun v => 3 ≤ exponent v)).card ≤ 1)
    (q : Fin n → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤
      ((projectedLossVertices C exponent).filter
        (fun v => exponent v ≤ 2)).card := by
  classical
  let F := actualLossOppositeCandidateFibre C exponent choice q
  let L := projectedLossVertices C exponent
  let H := L.filter (fun v => 3 ≤ exponent v)
  let Low := L.filter (fun v => exponent v ≤ 2)
  have hm (a : F) :
      a.1 ∈ actualEarliestLossCollisionRecords C exponent choice ∧
      flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 = q :=
    Finset.mem_filter.mp a.2
  have hex (a : F) :
      ∃ p : V × V,
        p.1 ∈ lossCoordinateSlice C exponent choice a.1.1 ∧
        p.2 ∈ lossCoordinateSlice C exponent choice a.1.2.1 ∧
        a.1.2.2 ∈ translatedCompletionWords C p.1 a.1.1 ∧
        a.1.2.2 ∈ translatedCompletionWords C p.2 a.1.2.1 := by
    obtain ⟨v,u,hv,hu,hw,hz⟩ :=
      actual_earliest_record_has_two_word_owners
        C exponent choice a.1 (hm a).1
    exact ⟨(v,u),hv,hu,hw,hz⟩
  let owner (a : F) : V × V := Classical.choose (hex a)
  have hos (a : F) :
      (owner a).1 ∈ lossCoordinateSlice C exponent choice a.1.1 ∧
      (owner a).2 ∈ lossCoordinateSlice C exponent choice a.1.2.1 ∧
      a.1.2.2 ∈ translatedCompletionWords C (owner a).1 a.1.1 ∧
      a.1.2.2 ∈ translatedCompletionWords C (owner a).2 a.1.2.1 :=
    Classical.choose_spec (hex a)
  have htwo (a : F) : (owner a).1 ≠ (owner a).2 := by
    intro heq
    have hca := ((mem_lossCoordinateSlice
      C exponent choice a.1.1 (owner a).1).mp (hos a).1).2
    have hcb := ((mem_lossCoordinateSlice
      C exponent choice a.1.2.1 (owner a).2).mp (hos a).2.1).2
    rw [← heq] at hcb
    have hlt :=
      (actual_earliest_loss_collision_record_valid
        C exponent choice a.1 (hm a).1).2.1
    exact (ne_of_gt hlt) (hca.symm.trans hcb)
  have hlowsome (a : F) :
      exponent (owner a).1 ≤ 2 ∨ exponent (owner a).2 ≤ 2 := by
    by_contra hnot
    push_neg at hnot
    have hva : (owner a).1 ∈ H := by
      apply Finset.mem_filter.mpr
      exact ⟨((mem_lossCoordinateSlice C exponent choice a.1.1
        (owner a).1).mp (hos a).1).1, by omega⟩
    have hua : (owner a).2 ∈ H := by
      apply Finset.mem_filter.mpr
      exact ⟨((mem_lossCoordinateSlice C exponent choice a.1.2.1
        (owner a).2).mp (hos a).2.1).1, by omega⟩
    have heq : (owner a).1 = (owner a).2 :=
      (Finset.card_le_one.mp hhigh) (owner a).1 hva (owner a).2 hua
    exact (htwo a) heq
  let pick (a : F) : V :=
    if exponent (owner a).1 ≤ 2 then (owner a).1 else (owner a).2
  have hcert (a : F) :
      ∃ c : Fin n, (c = a.1.1 ∨ c = a.1.2.1) ∧
        pick a ∈ lossCoordinateSlice C exponent choice c ∧
        a.1.2.2 ∈ translatedCompletionWords C (pick a) c := by
    by_cases hfirst : exponent (owner a).1 ≤ 2
    · refine ⟨a.1.1,Or.inl rfl,?_,?_⟩
      · simpa [pick,hfirst] using (hos a).1
      · simpa [pick,hfirst] using (hos a).2.2.1
    · refine ⟨a.1.2.1,Or.inr rfl,?_,?_⟩
      · simpa [pick,hfirst] using (hos a).2.1
      · simpa [pick,hfirst] using (hos a).2.2.2
  have hlow (a : F) : pick a ∈ Low := by
    obtain ⟨c,_,hc,_⟩ := hcert a
    have hp : pick a ∈ L :=
      ((mem_lossCoordinateSlice C exponent choice c (pick a)).mp hc).1
    apply Finset.mem_filter.mpr
    refine ⟨hp,?_⟩
    by_cases hfirst : exponent (owner a).1 ≤ 2
    · simpa [pick,hfirst] using hfirst
    · have hsecond : exponent (owner a).2 ≤ 2 :=
        (hlowsome a).resolve_left hfirst
      simpa [pick,hfirst] using hsecond
  have hinj : Function.Injective pick := by
    intro a b heq
    by_contra hab
    have hneq : a.1 ≠ b.1 := by
      intro ha
      exact hab (Subtype.ext ha)
    have htarget : flipBoolWordAt
        (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 =
        flipBoolWordAt (flipBoolWordAt b.1.2.2 b.1.1) b.1.2.1 :=
      (hm a).2.trans (hm b).2.symm
    obtain ⟨c,hca,ha,hw⟩ := hcert a
    obtain ⟨d,hdb,hb,hz⟩ := hcert b
    have hb' : pick a ∈ lossCoordinateSlice C exponent choice d := by
      rw [heq]
      exact hb
    have hz' : b.1.2.2 ∈ translatedCompletionWords C (pick a) d := by
      rw [heq]
      exact hz
    have hbig :=
      actual_any_width_reused_opposite_shared_owner_exponent_three
        C exponent choice a.1 b.1 (hm a).1 (hm b).1
        hneq htarget (pick a) c d hca hdb ha hb' hw hz'
    have hsmall := (Finset.mem_filter.mp (hlow a)).2
    omega
  have hsub : (Finset.univ : Finset F).image pick ⊆ Low := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact hlow a
  have hbound : (Finset.univ : Finset F).card ≤ Low.card := by
    calc
      (Finset.univ : Finset F).card =
          ((Finset.univ : Finset F).image pick).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ Low.card := Finset.card_le_card hsub
  simpa only [Finset.card_univ, Fintype.card_coe] using hbound

#print axioms actual_one_high_loss_centre_opposite_fibre_le_low_centres

end OrderedEdgeColoring
end JSP000404Research
