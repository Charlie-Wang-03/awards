import JSP000404Research.ActualLossAnyWidthTwoDisagreements
import JSP000404Research.ResidualTwoFlipExactSymmetricDifference
import Mathlib.Tactic

set_option maxHeartbeats 600000

/-!
# Four genuine projected-loss centres forced by opposite-candidate REUSE

For arbitrary n, two distinct original earliest-prior collision records
with one equal double-flip opposite word MUST involve at least four
different genuine projected-loss owners, provided the original
exponent(v) <= 2.

The proof uses precisely actual loss-coordinate slice owners and their
actual translated completion-cube words, plus a dimension-independent
two-bit Boolean support argument. No fake source, candidate hole, surplus,
planarity, or AngleCap claim is introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Two distinct STRICT ordered coordinate pairs sharing a coordinate
have different second coordinates. At equal opposite two-flip target,
the two original source words differ on these TWO other coordinates. -/
theorem any_width_shared_colour_distinct_pairs_two_source_disagreements
    {n : ℕ} (w z : Fin n → Bool)
    (i j k l : Fin n)
    (hji : j < i) (hlk : l < k)
    (hp : (i,j) ≠ (k,l))
    (heq :
      flipBoolWordAt (flipBoolWordAt w i) j =
        flipBoolWordAt (flipBoolWordAt z k) l)
    (hshared : i = k ∨ i = l ∨ j = k ∨ j = l) :
    ∃ d e : Fin n, d ≠ e ∧ w d ≠ z d ∧ w e ≠ z e := by
  have hflip :
      flipCompletionWord j (flipCompletionWord i w) =
        flipCompletionWord l (flipCompletionWord k z) := by
    simpa [flipCompletionWord, flipBoolWordAt] using heq
  have hdiff (e : Fin n)
      (hx : ((e = j ∨ e = i) ∧ ¬ (e = l ∨ e = k)) ∨
            (¬ (e = j ∨ e = i) ∧ (e = l ∨ e = k))) :
      w e ≠ z e :=
    (two_flip_target_eq_source_diff_iff_pair_exclusive
      w z j i l k (ne_of_lt hji) (ne_of_lt hlk) hflip e).mpr hx
  rcases hshared with hik | hil | hjk | hjl
  · have hjl' : j ≠ l := by
      intro he
      exact hp (Prod.ext hik he)
    refine ⟨j,l,hjl',?_,?_⟩
    · apply hdiff j
      exact Or.inl ⟨Or.inl rfl, by
        intro h
        rcases h with h | h
        · exact hjl' h
        · omega⟩
    · apply hdiff l
      exact Or.inr ⟨by
        intro h
        rcases h with h | h <;> omega, Or.inl rfl⟩
  · have hjk' : j ≠ k := by omega
    refine ⟨j,k,hjk',?_,?_⟩
    · apply hdiff j
      exact Or.inl ⟨Or.inl rfl, by
        intro h
        rcases h with h | h <;> omega⟩
    · apply hdiff k
      exact Or.inr ⟨by
        intro h
        rcases h with h | h <;> omega, Or.inr rfl⟩
  · have hil' : i ≠ l := by omega
    refine ⟨i,l,hil',?_,?_⟩
    · apply hdiff i
      exact Or.inl ⟨Or.inr rfl, by
        intro h
        rcases h with h | h <;> omega⟩
    · apply hdiff l
      exact Or.inr ⟨by
        intro h
        rcases h with h | h <;> omega, Or.inl rfl⟩
  · have hik' : i ≠ k := by
      intro he
      exact hp (Prod.ext he hjl)
    refine ⟨i,k,hik',?_,?_⟩
    · apply hdiff i
      exact Or.inl ⟨Or.inr rfl, by
        intro h
        rcases h with h | h <;> omega⟩
    · apply hdiff k
      exact Or.inr ⟨by
        intro h
        rcases h with h | h <;> omega, Or.inr rfl⟩

/-- Recover ACTUAL owners of both source coordinates of any canonical
earliest-prior collision record, retaining their actual source WORD
membership rather than just their chosen coordinates. -/
theorem actual_earliest_record_has_two_word_owners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice) :
    ∃ v u : V,
      v ∈ lossCoordinateSlice C exponent choice a.1 ∧
      u ∈ lossCoordinateSlice C exponent choice a.2.1 ∧
      a.2.2 ∈ translatedCompletionWords C v a.1 ∧
      a.2.2 ∈ translatedCompletionWords C u a.2.1 := by
  classical
  obtain ⟨_, _, hw, hz⟩ :=
    actual_earliest_loss_collision_record_valid C exponent choice a ha
  obtain ⟨v,hv,hwordv⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨u,hu,hwordu⟩ := Finset.mem_biUnion.mp hz
  exact ⟨v,u,hv,hu,hwordv,hwordu⟩

/-- Distinct REAL collision records charging the SAME opposite word
force FOUR different original projected-loss centres, for any width n.
The genuine exponent<=2 hypothesis prevents a single projected-loss
cube from carrying two source words differing on two Boolean bits. -/
theorem actual_any_width_reused_opposite_forces_four_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hne : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1) :
    4 ≤ (projectedLossVertices C exponent).card := by
  classical
  have horderA :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).2.1
  have horderB :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice b hb).2.1
  have hpairne : (a.1, a.2.1) ≠ (b.1, b.2.1) := by
    intro hpair
    have hc : a.1 = b.1 :=
      congrArg (fun cd : Fin n × Fin n => cd.1) hpair
    have hd : a.2.1 = b.2.1 :=
      congrArg (fun cd : Fin n × Fin n => cd.2) hpair
    exact hne (loss_opposite_same_coordinate_pair_injective
      a b hc hd hopposite)
  have hsource (hshare :
      a.1 = b.1 ∨ a.1 = b.2.1 ∨
      a.2.1 = b.1 ∨ a.2.1 = b.2.1) :
      ∃ d e : Fin n,
        d ≠ e ∧ a.2.2 d ≠ b.2.2 d ∧ a.2.2 e ≠ b.2.2 e :=
    any_width_shared_colour_distinct_pairs_two_source_disagreements
      a.2.2 b.2.2 a.1 a.2.1 b.1 b.2.1
      horderA horderB hpairne hopposite hshare
  obtain ⟨va,ua,hva,hua,hwva,hwua⟩ :=
    actual_earliest_record_has_two_word_owners
      C exponent choice a ha
  obtain ⟨vb,ub,hvb,hub,hwvb,hwub⟩ :=
    actual_earliest_record_has_two_word_owners
      C exponent choice b hb
  have hcross (v u : V) (c d : Fin n)
      (hv : v ∈ lossCoordinateSlice C exponent choice c)
      (hu : u ∈ lossCoordinateSlice C exponent choice d)
      (hvc : c = a.1 ∨ c = a.2.1)
      (hud : d = b.1 ∨ d = b.2.1)
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
    obtain ⟨x,y,hxy,hx,hy⟩ := hsource hshare
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
  have hA : va ≠ ua := by
    intro heq
    have hca := ((mem_lossCoordinateSlice C exponent choice a.1 va).mp hva).2
    have hcb := ((mem_lossCoordinateSlice C exponent choice a.2.1 ua).mp hua).2
    rw [← heq] at hcb
    exact (ne_of_gt horderA) (hca.symm.trans hcb)
  have hB : vb ≠ ub := by
    intro heq
    have hca := ((mem_lossCoordinateSlice C exponent choice b.1 vb).mp hvb).2
    have hcb := ((mem_lossCoordinateSlice C exponent choice b.2.1 ub).mp hub).2
    rw [← heq] at hcb
    exact (ne_of_gt horderB) (hca.symm.trans hcb)
  have hVV := hcross va vb a.1 b.1 hva hvb (Or.inl rfl) (Or.inl rfl) hwva hwvb
  have hVU := hcross va ub a.1 b.2.1 hva hub (Or.inl rfl) (Or.inr rfl) hwva hwub
  have hUV := hcross ua vb a.2.1 b.1 hua hvb (Or.inr rfl) (Or.inl rfl) hwua hwvb
  have hUU := hcross ua ub a.2.1 b.2.1 hua hub (Or.inr rfl) (Or.inr rfl) hwua hwub
  have hfour : ({va,ua,vb,ub} : Finset V).card = 4 := by
    simp [hA, hB, hVV, hVU, hUV, hUU]
  have hsub : ({va,ua,vb,ub} : Finset V) ⊆
      projectedLossVertices C exponent := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ((mem_lossCoordinateSlice C exponent choice a.1 va).mp hva).1
    · exact ((mem_lossCoordinateSlice C exponent choice a.2.1 ua).mp hua).1
    · exact ((mem_lossCoordinateSlice C exponent choice b.1 vb).mp hvb).1
    · exact ((mem_lossCoordinateSlice C exponent choice b.2.1 ub).mp hub).1
  have hcard := Finset.card_le_card hsub
  rw [hfour] at hcard
  exact hcard

/-- No original opposite-word reuse with <=3 actual projected-loss
centres for ANY retained Boolean width, assuming original exponent<=2.
This strictly generalizes the previously n=3-only four-centre barrier. -/
theorem actual_any_width_three_loss_centres_opposite_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 3) :
    Set.InjOn
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
      (actualEarliestLossCollisionRecords C exponent choice) := by
  intro a ha b hb heq
  by_contra hne
  have hfour :=
    actual_any_width_reused_opposite_forces_four_loss_centres
      C exponent choice hexp a b ha hb hne heq
  omega

/-- Exactly original eighth-lane debt: at most three actual loss
centres rule out reused candidate words in arbitrary n with exponent<=2. -/
theorem actual_any_width_three_loss_centres_duplicate_debt_no_reuse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 3) :
    translatedLossDuplicateDebt C exponent choice =
      (actualLossEarliestOppositeCandidateWords C exponent choice).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hinj : Set.InjOn f S :=
    actual_any_width_three_loss_centres_opposite_injective
      C exponent choice hexp hloss
  calc
    translatedLossDuplicateDebt C exponent choice = S.card :=
      (actual_earliest_collision_records_card_eq_duplicate_debt
        C exponent choice).symm
    _ = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ = (actualLossEarliestOppositeCandidateWords
      C exponent choice).card := rfl

/-- Positive source-native eighth-lane candidate REUSE forces at least
four ACTUAL original projected-loss owners. -/
theorem actual_any_width_positive_opposite_reuse_forces_four_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (hreuse :
      (actualLossEarliestOppositeCandidateWords C exponent choice).card <
        translatedLossDuplicateDebt C exponent choice) :
    4 ≤ (projectedLossVertices C exponent).card := by
  by_contra hnot
  have hloss : (projectedLossVertices C exponent).card ≤ 3 := by omega
  have heq := actual_any_width_three_loss_centres_duplicate_debt_no_reuse
    C exponent choice hexp hloss
  omega

#print axioms any_width_shared_colour_distinct_pairs_two_source_disagreements
#print axioms actual_earliest_record_has_two_word_owners
#print axioms actual_any_width_reused_opposite_forces_four_loss_centres
#print axioms actual_any_width_three_loss_centres_opposite_injective
#print axioms actual_any_width_three_loss_centres_duplicate_debt_no_reuse
#print axioms actual_any_width_positive_opposite_reuse_forces_four_centres

end OrderedEdgeColoring
end JSP000404Research
