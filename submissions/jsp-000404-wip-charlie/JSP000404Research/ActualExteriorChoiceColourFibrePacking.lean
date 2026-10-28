import JSP000404Research.ActualExteriorBicolourFibrePacking
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Source-native strict colour-class ceiling for a true exterior collision fibre

The previously kernel-certified bicolour owner packing bound gives
    2 * |F_q| <= |B|,
where B is the original set of genuinely bichromatic loss centres.
Here we use the actual original CHOSEN loss colours as well.

Every source record contributing to a TRUE exterior hole q has two
original source owners with two distinct chosen loss colours.
Different q-fibre records have fully disjoint source owners.

Fix ANY colour c0. Choosing ONE owner of each record whose actual
chosen colour is not c0 gives a source-native injection into
    {v in B | choice(v) != c0}.
Hence |F_q| <= |B excluding the c0 choice class| at every n.
This is genuinely stronger when one chosen colour is concentrated.

No available hole is invented; this is an UPPER bound on already-real
hole demand, NOT a lower bound on the all-eight credit supply.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- For EVERY original retained-active choice and ANY designated
loss colour c0, actual earliest-prior records sharing the SAME
genuinely exterior opposite word must each consume a DIFFERENT
bichromatic original loss centre whose ORIGINAL selected loss
colour is not c0. At most one centre is charged to each record. -/
theorem actual_true_exterior_fibre_le_bichromatic_away_from_one_chosen_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (q : Fin n → Bool)
    (hq : q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice)
    (c0 : Fin n) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤
      ((projectedLossVertices C exponent).filter (fun v =>
        (∃ c d : Fin n, c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v) ∧ choice v ≠ c0)).card := by
  classical
  let F := actualLossOppositeCandidateFibre C exponent choice q
  let B := (projectedLossVertices C exponent).filter (fun v =>
    (∃ c d : Fin n, c ≠ d ∧
      c ∈ retainedActive C v ∧
      d ∈ retainedActive C v) ∧ choice v ≠ c0)
  have hm (a : F) :
      a.1 ∈ actualEarliestLossCollisionRecords C exponent choice ∧
      flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 = q :=
    Finset.mem_filter.mp a.2
  have howners (a : F) :
      ∃ p : V × V,
        p.1 ∈ lossCoordinateSlice C exponent choice a.1.1 ∧
        p.2 ∈ lossCoordinateSlice C exponent choice a.1.2.1 ∧
        a.1.2.2 ∈ translatedCompletionWords C p.1 a.1.1 ∧
        a.1.2.2 ∈ translatedCompletionWords C p.2 a.1.2.1 := by
    obtain ⟨v,u,hv,hu,hw,hz⟩ :=
      actual_earliest_record_has_two_word_owners
        C exponent choice a.1 (hm a).1
    exact ⟨(v,u),hv,hu,hw,hz⟩
  let owner (a : F) : V × V := Classical.choose (howners a)
  have hos (a : F) :
      (owner a).1 ∈ lossCoordinateSlice C exponent choice a.1.1 ∧
      (owner a).2 ∈ lossCoordinateSlice C exponent choice a.1.2.1 ∧
      a.1.2.2 ∈ translatedCompletionWords C (owner a).1 a.1.1 ∧
      a.1.2.2 ∈ translatedCompletionWords C (owner a).2 a.1.2.1 :=
    Classical.choose_spec (howners a)
  have hdiff (a : F) : a.1.1 ≠ a.1.2.1 :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a.1 (hm a).1).1
  have hqA (a : F) :
      flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    rw [(hm a).2]
    exact hq
  have hfirst (a : F) :
      (owner a).1 ∈ projectedLossVertices C exponent ∧
      choice (owner a).1 = a.1.1 ∧
      a.1.1 ∈ retainedActive C (owner a).1 ∧
      a.1.2.1 ∈ retainedActive C (owner a).1 := by
    have hdata :=
      (mem_lossCoordinateSlice
        C exponent choice a.1.1 (owner a).1).mp (hos a).1
    have hc : a.1.1 ∈ retainedActive C (owner a).1 := by
      rw [← hdata.2]
      exact hchoice _ hdata.1
    have hd : a.1.2.1 ∈ retainedActive C (owner a).1 :=
      (actual_earliest_exterior_record_owner_other_active
        C exponent choice a.1 (hm a).1 (hqA a)
        (owner a).1 a.1.1 (Or.inl rfl)
        (hos a).1 (hos a).2.2.1).1 rfl
    exact ⟨hdata.1, hdata.2, hc, hd⟩
  have hsecond (a : F) :
      (owner a).2 ∈ projectedLossVertices C exponent ∧
      choice (owner a).2 = a.1.2.1 ∧
      a.1.1 ∈ retainedActive C (owner a).2 ∧
      a.1.2.1 ∈ retainedActive C (owner a).2 := by
    have hdata :=
      (mem_lossCoordinateSlice
        C exponent choice a.1.2.1 (owner a).2).mp (hos a).2.1
    have hc : a.1.2.1 ∈ retainedActive C (owner a).2 := by
      rw [← hdata.2]
      exact hchoice _ hdata.1
    have hd : a.1.1 ∈ retainedActive C (owner a).2 :=
      (actual_earliest_exterior_record_owner_other_active
        C exponent choice a.1 (hm a).1 (hqA a)
        (owner a).2 a.1.2.1 (Or.inr rfl)
        (hos a).2.1 (hos a).2.2.2).2 rfl
    exact ⟨hdata.1, hdata.2, hd, hc⟩
  let pick (a : F) : V :=
    if a.1.1 = c0 then (owner a).2 else (owner a).1
  have hpick (a : F) : pick a ∈ B := by
    by_cases h0 : a.1.1 = c0
    · have h1 : a.1.2.1 ≠ c0 := by
        intro heq
        exact hdiff a (h0.trans heq.symm)
      have hh := hsecond a
      change (if a.1.1 = c0 then (owner a).2 else (owner a).1) ∈ B
      rw [if_pos h0]
      exact Finset.mem_filter.mpr
        ⟨hh.1, ⟨⟨a.1.1, a.1.2.1, hdiff a, hh.2.2.1, hh.2.2.2⟩,
          by rw [hh.2.1]; exact h1⟩⟩
    · have hh := hfirst a
      change (if a.1.1 = c0 then (owner a).2 else (owner a).1) ∈ B
      rw [if_neg h0]
      exact Finset.mem_filter.mpr
        ⟨hh.1, ⟨⟨a.1.1, a.1.2.1, hdiff a, hh.2.2.1, hh.2.2.2⟩,
          by rw [hh.2.1]; exact h0⟩⟩
  have hdistinct (a b : F) (hab : a ≠ b) :
      pick a ≠ pick b := by
    have hr : a.1 ≠ b.1 := by
      intro heq
      exact hab (Subtype.ext heq)
    have htarget :
        flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 =
        flipBoolWordAt (flipBoolWordAt b.1.2.2 b.1.1) b.1.2.1 :=
      (hm a).2.trans (hm b).2.symm
    by_cases ha0 : a.1.1 = c0
    · by_cases hb0 : b.1.1 = c0
      · simpa only [pick, if_pos ha0, if_pos hb0] using
          (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
            C exponent choice a.1 b.1 (hm a).1 (hm b).1
            hr htarget (hqA a) (owner a).2 (owner b).2
            a.1.2.1 b.1.2.1 (Or.inr rfl) (Or.inr rfl)
            (hos a).2.1 (hos b).2.1 (hos a).2.2.2 (hos b).2.2.2)
      · simpa only [pick, if_pos ha0, if_neg hb0] using
          (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
            C exponent choice a.1 b.1 (hm a).1 (hm b).1
            hr htarget (hqA a) (owner a).2 (owner b).1
            a.1.2.1 b.1.1 (Or.inr rfl) (Or.inl rfl)
            (hos a).2.1 (hos b).1 (hos a).2.2.2 (hos b).2.2.1)
    · by_cases hb0 : b.1.1 = c0
      · simpa only [pick, if_neg ha0, if_pos hb0] using
          (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
            C exponent choice a.1 b.1 (hm a).1 (hm b).1
            hr htarget (hqA a) (owner a).1 (owner b).2
            a.1.1 b.1.2.1 (Or.inl rfl) (Or.inr rfl)
            (hos a).1 (hos b).2.1 (hos a).2.2.1 (hos b).2.2.2)
      · simpa only [pick, if_neg ha0, if_neg hb0] using
          (actual_any_width_exterior_same_opposite_distinct_records_owner_disjoint
            C exponent choice a.1 b.1 (hm a).1 (hm b).1
            hr htarget (hqA a) (owner a).1 (owner b).1
            a.1.1 b.1.1 (Or.inl rfl) (Or.inl rfl)
            (hos a).1 (hos b).1 (hos a).2.2.1 (hos b).2.2.1)
  have hinj : Function.Injective pick := by
    intro a b hab
    by_contra hne
    exact (hdistinct a b hne) hab
  have hsub : (Finset.univ : Finset F).image pick ⊆ B := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    exact hpick a
  have hcard : F.card ≤ B.card := by
    calc
      F.card = (Finset.univ : Finset F).card := by
        simp only [Finset.card_univ, Fintype.card_coe]
      _ = ((Finset.univ : Finset F).image pick).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ B.card := Finset.card_le_card hsub
  exact hcard

#print axioms actual_true_exterior_fibre_le_bichromatic_away_from_one_chosen_colour

end OrderedEdgeColoring
end JSP000404Research
