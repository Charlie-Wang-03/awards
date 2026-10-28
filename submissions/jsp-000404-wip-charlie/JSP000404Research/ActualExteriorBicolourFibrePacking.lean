import JSP000404Research.ActualExteriorOppositeFibrePacking
import JSP000404Research.ActualEarliestSourceExteriorCrossActivity
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Genuine true-exterior collision fibres pack BICHROMATIC owners

A real exterior collision record contributes two distinct original
projected-loss centres which retain both collision colours. Two different
records with the same exterior target cannot reuse any of those centres.
This yields a stronger count than packing into ALL projected-loss centres.
No global AngleCap payment or new credit is assumed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Each original true-hole opposite fibre uses two original
bichromatic projected-loss owners per independent record. -/
theorem actual_any_width_true_exterior_opposite_fibre_twice_card_le_bichromatic_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool)
    (hq : q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    2 * (actualLossOppositeCandidateFibre C exponent choice q).card ≤
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n, c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v)).card := by
  classical
  let F := actualLossOppositeCandidateFibre C exponent choice q
  let L := (projectedLossVertices C exponent).filter (fun v =>
    ∃ c d : Fin n, c ≠ d ∧
      c ∈ retainedActive C v ∧
      d ∈ retainedActive C v)
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
  have hwordNe (a : F) : a.1.1 ≠ a.1.2.1 :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a.1 (hm a).1).1
  have hqRecord (a : F) :
      flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    rw [(hm a).2]
    exact hq
  have hOrig (a : F) :
      a.1.1 ∈ retainedActive C (owner a).1 ∧
        a.1.2.1 ∈ retainedActive C (owner a).2 := by
    constructor
    · have hdat := (mem_lossCoordinateSlice
        C exponent choice a.1.1 (owner a).1).mp (hos a).1
      rw [← hdat.2]
      exact hchoice _ hdat.1
    · have hdat := (mem_lossCoordinateSlice
        C exponent choice a.1.2.1 (owner a).2).mp (hos a).2.1
      rw [← hdat.2]
      exact hchoice _ hdat.1
  have hOther (a : F) :
      a.1.2.1 ∈ retainedActive C (owner a).1 ∧
        a.1.1 ∈ retainedActive C (owner a).2 := by
    constructor
    · exact (actual_earliest_exterior_record_owner_other_active
        C exponent choice a.1 (hm a).1 (hqRecord a)
          (owner a).1 a.1.1 (Or.inl rfl)
          (hos a).1 (hos a).2.2.1).1 rfl
    · exact (actual_earliest_exterior_record_owner_other_active
        C exponent choice a.1 (hm a).1 (hqRecord a)
          (owner a).2 a.1.2.1 (Or.inr rfl)
          (hos a).2.1 (hos a).2.2.2).2 rfl
  have hchoose (a : F) (i : Fin 2) : pick (a,i) ∈ L := by
    have hfirst : (owner a).1 ∈ L :=
      Finset.mem_filter.mpr
        ⟨((mem_lossCoordinateSlice C exponent choice a.1.1
            (owner a).1).mp (hos a).1).1,
          ⟨a.1.1, a.1.2.1, hwordNe a,
            (hOrig a).1, (hOther a).1⟩⟩
    have hsecond : (owner a).2 ∈ L :=
      Finset.mem_filter.mpr
        ⟨((mem_lossCoordinateSlice C exponent choice a.1.2.1
            (owner a).2).mp (hos a).2.1).1,
          ⟨a.1.1, a.1.2.1, hwordNe a,
            (hOther a).2, (hOrig a).2⟩⟩
    fin_cases i
    · simpa [pick] using hfirst
    · simpa [pick] using hsecond
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

#print axioms actual_any_width_true_exterior_opposite_fibre_twice_card_le_bichromatic_centres

end OrderedEdgeColoring
end JSP000404Research
