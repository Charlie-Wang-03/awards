import JSP000404Research.SmallOddWireCapacity

/-!
# A ten-wire bound on seven phases

A finite family of 42 Boolean words, counting multiplicity, covers each proper partial
two-colouring of the seven-cycle at least four times. Pairwise separated rows use disjoint
parts of that family. Thus four times the number of rows is at most 42, giving at most ten.
The finite covering statement is verified by ordinary kernel reduction.
-/

namespace JSP000404Research
namespace OddWire

open scoped BigOperators

def sevenSlotMask : Fin 42 → ℕ :=
  ![19, 21, 21, 25, 27, 37, 37, 38, 41, 41, 42, 42, 43, 43, 45, 45, 50, 51, 53, 53, 54,
    73, 74, 74, 76, 77, 82, 82, 84, 84, 85, 85, 86, 86, 89, 90, 90, 100, 102, 106, 106, 108]

def sevenSlotCode (slot : Fin 42) (coordinate : Fin 7) : Bool :=
  (sevenSlotMask slot).testBit coordinate.val

def SevenCompatible (row : Fin 7 → Option Bool) (slot : Fin 42) : Prop :=
  ∀ coordinate sign, row coordinate = some sign → sevenSlotCode slot coordinate = sign

instance (row : Fin 7 → Option Bool) (slot : Fin 42) : Decidable (SevenCompatible row slot) :=
  inferInstanceAs (Decidable (∀ coordinate sign,
    row coordinate = some sign → sevenSlotCode slot coordinate = sign))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem seven_slot_coverage : ∀ row : Fin 7 → Option Bool, PartialValid row →
    4 ≤ ((Finset.univ : Finset (Fin 42)).filter (SevenCompatible row)).card := by
  decide

/-- The fractional covering certificate bounds every separated seven-phase row family. -/
theorem card_le_ten_of_seven_rows {V : Type*} [Fintype V]
    (row : V → Fin 7 → Option Bool) (hvalid : ∀ v, PartialValid (row v))
    (hsep : ∀ v w, v ≠ w → ∃ c a b, row v c = some a ∧ row w c = some b ∧ a ≠ b) :
    Fintype.card V ≤ 10 := by
  classical
  let support (v : V) := (Finset.univ : Finset (Fin 42)).filter (SevenCompatible (row v))
  have hdisjoint : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint support := by
    intro v _ w _ hvw
    apply Finset.disjoint_left.mpr
    intro slot hv hw
    have hvcode := (Finset.mem_filter.mp hv).2
    have hwcode := (Finset.mem_filter.mp hw).2
    obtain ⟨c, a, b, ha, hb, hab⟩ := hsep v w hvw
    exact hab ((hvcode c a ha).symm.trans (hwcode c b hb))
  have hsum : ∑ v, (support v).card ≤ 42 := by
    rw [← Finset.card_biUnion hdisjoint]
    have h := Finset.card_le_card
      (Finset.subset_univ ((Finset.univ : Finset V).biUnion support))
    simpa using h
  have hlow : Fintype.card V * 4 ≤ ∑ v, (support v).card := by
    calc
      Fintype.card V * 4 = ∑ _v : V, 4 := by simp
      _ ≤ ∑ v, (support v).card := Finset.sum_le_sum fun v _ ↦ seven_slot_coverage _ (hvalid v)
  omega

#print axioms seven_slot_coverage
#print axioms card_le_ten_of_seven_rows

end OddWire
end JSP000404Research
