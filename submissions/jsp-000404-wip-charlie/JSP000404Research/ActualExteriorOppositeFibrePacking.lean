import JSP000404Research.ActualSharedOwnerOppositeNotExterior
import JSP000404Research.ActualAnyWidthOppositeFibrePacking
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Actual true-exterior collision fibres pack original owners without exponent bounds

If a candidate opposite Boolean word q is a GENUINE exterior true
hole, two different original earliest-prior source records charging
q cannot share any genuine original projected-loss owner: our already
kernel-certified theorem proves that every shared-owner candidate
belongs to the original retained cube and so is covered.

Consequently, whenever q is truly exterior, every actual original
q-fibre source record consumes two distinct genuine loss-centre owners
and different records consume DISJOINT pairs, at arbitrary n with
NO exponent(v) <= 2 hypothesis and NO global planar hypothesis.

This does NOT say every candidate word is exterior, nor that the
other seven debt classes can be paid from unreserved dyadic surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- REAL exterior eligibility rules out reused original loss owners
for any two different earliest-prior records charging the same q,
even when genuine source exponents are arbitrarily high. -/
theorem actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hab : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1)
    (hq :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice)
    (v u : V) (c d : Fin n)
    (hvc : c = a.1 ∨ c = a.2.1)
    (hud : d = b.1 ∨ d = b.2.1)
    (hv : v ∈ lossCoordinateSlice C exponent choice c)
    (hu : u ∈ lossCoordinateSlice C exponent choice d)
    (hw : a.2.2 ∈ translatedCompletionWords C v c)
    (hz : b.2.2 ∈ translatedCompletionWords C u d) :
    v ≠ u := by
  intro heq
  subst u
  exact (actual_any_width_shared_owner_reused_opposite_not_exterior
    C exponent choice a b ha hb hab hopposite v c d
    hvc hud hv hu hw hz) hq

/-- Uniform actual TRUE-HOLE q-fibre capacity, without any original
exponent restriction. The proof constructs a genuine injection
(actual source record, one of its two different actual owners)
into the original projected-loss vertices; being a real exterior
hole prevents ANY two different records from reusing an owner. -/
theorem actual_any_width_exterior_opposite_fibre_twice_card_le_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool)
    (hq : q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    2 * (actualLossOppositeCandidateFibre C exponent choice q).card ≤
      (projectedLossVertices C exponent).card := by
  classical
  let F := actualLossOppositeCandidateFibre C exponent choice q
  let L := projectedLossVertices C exponent
  have hm (a : F) :
      a.1 ∈ actualEarliestLossCollisionRecords C exponent choice ∧
      flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 = q := by
    exact Finset.mem_filter.mp a.2
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
  let pick : F × Fin 2 → V := fun x =>
    if x.2 = 0 then (owner x.1).1 else (owner x.1).2
  have hchoose (a : F) (i : Fin 2) : pick (a,i) ∈ L := by
    fin_cases i
    · simpa [pick,L] using
        ((mem_lossCoordinateSlice C exponent choice a.1.1
          (owner a).1).mp (hos a).1).1
    · simpa [pick,L] using
        ((mem_lossCoordinateSlice C exponent choice a.1.2.1
          (owner a).2).mp (hos a).2.1).1
  have hcross (a b : F) (hab : a ≠ b) (i j : Fin 2) :
      pick (a,i) ≠ pick (b,j) := by
    have hneq : a.1 ≠ b.1 := by
      intro heq
      exact hab (Subtype.ext heq)
    have htarget : flipBoolWordAt
        (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 =
        flipBoolWordAt (flipBoolWordAt b.1.2.2 b.1.1) b.1.2.1 :=
      (hm a).2.trans (hm b).2.symm
    have hrealHole :
        flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 ∈
          lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
      rw [(hm a).2]
      exact hq
    fin_cases i <;> fin_cases j
    · simpa [pick] using
        (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
          C exponent choice a.1 b.1 (hm a).1 (hm b).1
          hneq htarget hrealHole (owner a).1 (owner b).1
          a.1.1 b.1.1 (Or.inl rfl) (Or.inl rfl)
          (hos a).1 (hos b).1 (hos a).2.2.1 (hos b).2.2.1)
    · simpa [pick] using
        (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
          C exponent choice a.1 b.1 (hm a).1 (hm b).1
          hneq htarget hrealHole (owner a).1 (owner b).2
          a.1.1 b.1.2.1 (Or.inl rfl) (Or.inr rfl)
          (hos a).1 (hos b).2.1 (hos a).2.2.1 (hos b).2.2.2)
    · simpa [pick] using
        (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
          C exponent choice a.1 b.1 (hm a).1 (hm b).1
          hneq htarget hrealHole (owner a).2 (owner b).1
          a.1.2.1 b.1.1 (Or.inr rfl) (Or.inl rfl)
          (hos a).2.1 (hos b).1 (hos a).2.2.2 (hos b).2.2.1)
    · simpa [pick] using
        (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
          C exponent choice a.1 b.1 (hm a).1 (hm b).1
          hneq htarget hrealHole (owner a).2 (owner b).2
          a.1.2.1 b.1.2.1 (Or.inr rfl) (Or.inr rfl)
          (hos a).2.1 (hos b).2.1 (hos a).2.2.2 (hos b).2.2.2)
  have hinj : Function.Injective pick := by
    intro x y heq
    rcases x with ⟨a,i⟩
    rcases y with ⟨b,j⟩
    by_cases hab : a = b
    · subst b
      have hij : i = j := by
        fin_cases i <;> fin_cases j
        · rfl
        · have h : (owner a).1 = (owner a).2 := by
            simpa [pick] using heq
          exact False.elim ((htwo a) h)
        · have h : (owner a).2 = (owner a).1 := by
            simpa [pick] using heq
          exact False.elim ((htwo a) h.symm)
        · rfl
      exact congrArg (fun k : Fin 2 => (a,k)) hij
    · exact False.elim ((hcross a b hab i j) heq)
  have hsub : (Finset.univ : Finset (F × Fin 2)).image pick ⊆ L := by
    intro v hv
    obtain ⟨⟨a,i⟩,_,rfl⟩ := Finset.mem_image.mp hv
    exact hchoose a i
  have hbound : (Finset.univ : Finset (F × Fin 2)).card ≤ L.card := by
    calc
      (Finset.univ : Finset (F × Fin 2)).card =
          ((Finset.univ : Finset (F × Fin 2)).image pick).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ L.card := Finset.card_le_card hsub
  have hcard : F.card * 2 ≤ L.card := by
    simpa only [Finset.card_univ, Fintype.card_prod,
      Fintype.card_coe, Fintype.card_fin] using hbound
  simpa only [mul_comm] using hcard

#print axioms actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
#print axioms actual_any_width_exterior_opposite_fibre_twice_card_le_loss_centres

end OrderedEdgeColoring
end JSP000404Research
