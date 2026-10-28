import JSP000404Research.ActualAnyWidthFourLossCentreReuseBarrier
import JSP000404Research.ResidualLossCanonicalOppositeFibreBound
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Arbitrary-n genuine original-source collision fibre packing

One actual opposite Boolean candidate q may be charged by several distinct
earliest-prior original source records. For exponent(v) <= 2, each such
record uses TWO original projected-loss centres, and different records
in the SAME q-fibre use DISJOINT original centres. We formally construct
the injection (actual record, one of its two endpoints) -> loss centre.

This is stronger than the previous pairwise four-centre reuse obstruction:
  2 * |actualLossOppositeCandidateFibre(q)| <= |projectedLossVertices|
for every Boolean width n, not just for n=3. The original source
membership and actual word are retained in every owner witness.
No exterior holes or surplus are assumed or created.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A genuine projected-loss source vertex of one earliest-prior record
cannot equal ANY genuine projected-loss source vertex of ANOTHER record
charging the SAME opposite Boolean word, at arbitrary retained width.
This is source-level DISJOINTNESS, stronger than just card >=4. -/
theorem actual_any_width_same_opposite_distinct_records_owner_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hab : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1)
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
  have hca := ((mem_lossCoordinateSlice C exponent choice c v).mp hv).2
  have hcb := ((mem_lossCoordinateSlice C exponent choice d v).mp hu).2
  have hcd : c = d := hca.symm.trans hcb
  have hshare :
      a.1 = b.1 ∨ a.1 = b.2.1 ∨
      a.2.1 = b.1 ∨ a.2.1 = b.2.1 := by
    rcases hvc with hvc | hvc <;>
      rcases hud with hud | hud
    · exact Or.inl (hvc.symm.trans (hcd.trans hud))
    · exact Or.inr (Or.inl (hvc.symm.trans (hcd.trans hud)))
    · exact Or.inr (Or.inr (Or.inl
        (hvc.symm.trans (hcd.trans hud))))
    · exact Or.inr (Or.inr (Or.inr
        (hvc.symm.trans (hcd.trans hud))))
  have horderA :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).2.1
  have horderB :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice b hb).2.1
  have hpair : (a.1, a.2.1) ≠ (b.1, b.2.1) := by
    intro h
    have hc : a.1 = b.1 :=
      congrArg (fun cd : Fin n × Fin n => cd.1) h
    have hd : a.2.1 = b.2.1 :=
      congrArg (fun cd : Fin n × Fin n => cd.2) h
    exact hab (loss_opposite_same_coordinate_pair_injective
      a b hc hd hopposite)
  obtain ⟨x,y,hxy,hx,hy⟩ :=
    any_width_shared_colour_distinct_pairs_two_source_disagreements
      a.2.2 b.2.2 a.1 a.2.1 b.1 b.2.1
      horderA horderB hpair hopposite hshare
  have hloss : v ∈ projectedLossVertices C exponent :=
    ((mem_lossCoordinateSlice C exponent choice c v).mp hv).1
  have hactive :=
    any_width_projected_loss_retains_all_but_one
      C exponent hexp v hloss
  have hz' : b.2.2 ∈ translatedCompletionWords C v c := by
    rw [hcd]
    exact hz
  exact any_width_translated_cube_two_disagreements_impossible
    C v c a.2.2 b.2.2 x y hxy hx hy hactive ⟨hw,hz'⟩

/-- Uniform FIBREWISE packing: every original opposite target q
charged by m genuine earliest-prior loss collision records requires
at least 2m DISTINCT original projected-loss centres, for EVERY n.

This subsumes all n=3 two/four/six-centre fibre barriers in one
source-native quantitative theorem without hypothesizing exterior holes. -/
theorem actual_any_width_opposite_fibre_twice_card_le_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (q : Fin n → Bool) :
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
    fin_cases i <;> fin_cases j
    · simpa [pick] using
        (actual_any_width_same_opposite_distinct_records_owner_disjoint
          C exponent choice hexp a.1 b.1 (hm a).1 (hm b).1
          hneq htarget (owner a).1 (owner b).1
          a.1.1 b.1.1 (Or.inl rfl) (Or.inl rfl)
          (hos a).1 (hos b).1 (hos a).2.2.1 (hos b).2.2.1)
    · simpa [pick] using
        (actual_any_width_same_opposite_distinct_records_owner_disjoint
          C exponent choice hexp a.1 b.1 (hm a).1 (hm b).1
          hneq htarget (owner a).1 (owner b).2
          a.1.1 b.1.2.1 (Or.inl rfl) (Or.inr rfl)
          (hos a).1 (hos b).2.1 (hos a).2.2.1 (hos b).2.2.2)
    · simpa [pick] using
        (actual_any_width_same_opposite_distinct_records_owner_disjoint
          C exponent choice hexp a.1 b.1 (hm a).1 (hm b).1
          hneq htarget (owner a).2 (owner b).1
          a.1.2.1 b.1.1 (Or.inr rfl) (Or.inl rfl)
          (hos a).2.1 (hos b).1 (hos a).2.2.2 (hos b).2.2.1)
    · simpa [pick] using
        (actual_any_width_same_opposite_distinct_records_owner_disjoint
          C exponent choice hexp a.1 b.1 (hm a).1 (hm b).1
          hneq htarget (owner a).2 (owner b).2
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

#print axioms actual_any_width_same_opposite_distinct_records_owner_disjoint
#print axioms actual_any_width_opposite_fibre_twice_card_le_loss_centres

end OrderedEdgeColoring
end JSP000404Research
