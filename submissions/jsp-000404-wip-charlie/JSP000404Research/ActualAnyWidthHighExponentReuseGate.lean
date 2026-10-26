import JSP000404Research.ActualAnyWidthOppositeFibrePacking
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Original projected-loss high-exponent obstruction for repeated opposite charges

All earlier 2m-centre bounds assumed exponent(v) <= 2 globally.
Here we remove that assumption: whenever two different genuine
earliest-prior source records charge ONE opposite word and REUSE a
single original loss-source vertex, the reused original centre must
have exponent >= 3.

Consequently, in *any* original configuration (no global exponent
bound), a repeated charge by two original source records forces
EITHER >= 4 genuinely different projected-loss centres, OR at least
one *genuine* projected-loss centre of exponent >= 3.

This is an unconditional source-native collision/profile tradeoff.
It is neither a fictitious hole nor an AngleCap payment argument.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A single original translated cube supporting two words differing
at TWO bits must belong to an original projected-loss centre
with exponent at least THREE. No global exponent hypothesis. -/
theorem actual_projected_loss_cube_two_disagreements_forces_exponent_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) (hv : v ∈ projectedLossVertices C exponent)
    (c : Fin n) (w z : Fin n → Bool)
    (d e : Fin n) (hde : d ≠ e)
    (hd : w d ≠ z d) (he : w e ≠ z e)
    (hw : w ∈ translatedCompletionWords C v c)
    (hz : z ∈ translatedCompletionWords C v c) :
    3 ≤ exponent v := by
  by_contra hge
  have hle : exponent v ≤ 2 := by omega
  have hrigid := (mem_projectedLossVertices C exponent v).mp hv
  have hcard : (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hactive : n ≤ (retainedActive C v).card + 1 := by
    unfold projectedFree at hrigid
    omega
  exact (any_width_translated_cube_two_disagreements_impossible
    C v c w z d e hde hd he hactive) ⟨hw,hz⟩

/-- Any shared ACTUAL original loss owner between two distinct
genuine earliest-prior records hitting the SAME opposite corner
must have exponent >= 3. No bound on exponents anywhere. -/
theorem actual_any_width_reused_opposite_shared_owner_exponent_three
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
    (v : V) (c d : Fin n)
    (hvc : c = a.1 ∨ c = a.2.1)
    (hud : d = b.1 ∨ d = b.2.1)
    (hv : v ∈ lossCoordinateSlice C exponent choice c)
    (hu : v ∈ lossCoordinateSlice C exponent choice d)
    (hw : a.2.2 ∈ translatedCompletionWords C v c)
    (hz : b.2.2 ∈ translatedCompletionWords C v d) :
    3 ≤ exponent v := by
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
  have hz' : b.2.2 ∈ translatedCompletionWords C v c := by
    rw [hcd]
    exact hz
  exact actual_projected_loss_cube_two_disagreements_forces_exponent_three
    C exponent v hloss c a.2.2 b.2.2 x y hxy hx hy hw hz'

/-- The exponent-free, original-source four-loss-centre OR high-exponent
tradeoff: two distinct genuine source records repeating the same opposite
corner force at least four ACTUAL loss centres unless a genuine source
centre with exponent >= 3 is present. This covers every Boolean n and
arbitrary original exponent profiles. -/
theorem actual_any_width_reused_opposite_four_centres_or_high_exponent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hab : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1) :
    4 ≤ (projectedLossVertices C exponent).card ∨
      ∃ v ∈ projectedLossVertices C exponent, 3 ≤ exponent v := by
  classical
  by_cases hhigh :
      ∃ v ∈ projectedLossVertices C exponent, 3 ≤ exponent v
  · exact Or.inr hhigh
  · left
    have hlow (v : V) (hv : v ∈ projectedLossVertices C exponent) :
        exponent v ≤ 2 := by
      by_contra h
      exact hhigh ⟨v,hv,by omega⟩
    obtain ⟨va,ua,hva,hua,hwva,hwua⟩ :=
      actual_earliest_record_has_two_word_owners C exponent choice a ha
    obtain ⟨vb,ub,hvb,hub,hwvb,hwub⟩ :=
      actual_earliest_record_has_two_word_owners C exponent choice b hb
    have hA : va ≠ ua := by
      intro heq
      have hca := ((mem_lossCoordinateSlice C exponent choice a.1 va).mp hva).2
      have hcb := ((mem_lossCoordinateSlice C exponent choice a.2.1 ua).mp hua).2
      rw [← heq] at hcb
      exact (ne_of_gt
        (actual_earliest_loss_collision_record_valid C exponent choice a ha).2.1)
        (hca.symm.trans hcb)
    have hB : vb ≠ ub := by
      intro heq
      have hca := ((mem_lossCoordinateSlice C exponent choice b.1 vb).mp hvb).2
      have hcb := ((mem_lossCoordinateSlice C exponent choice b.2.1 ub).mp hub).2
      rw [← heq] at hcb
      exact (ne_of_gt
        (actual_earliest_loss_collision_record_valid C exponent choice b hb).2.1)
        (hca.symm.trans hcb)
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
      have hh :=
        actual_any_width_reused_opposite_shared_owner_exponent_three
          C exponent choice a b ha hb hab hopposite v c d
          hvc hud hv hu hw hz
      have hvL : v ∈ projectedLossVertices C exponent :=
        ((mem_lossCoordinateSlice C exponent choice c v).mp hv).1
      exact (by omega : False)
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
      rcases hx with h | h | h | h
      · rw [h]
        exact ((mem_lossCoordinateSlice C exponent choice a.1 va).mp hva).1
      · rw [h]
        exact ((mem_lossCoordinateSlice C exponent choice a.2.1 ua).mp hua).1
      · rw [h]
        exact ((mem_lossCoordinateSlice C exponent choice b.1 vb).mp hvb).1
      · rw [h]
        exact ((mem_lossCoordinateSlice C exponent choice b.2.1 ub).mp hub).1
    have hcard := Finset.card_le_card hsub
    rw [hfour] at hcard
    exact hcard

/-- A direct exponent-free criterion usable in the original Planar
AngleCap proof: if there are at most THREE actual projected-loss
centres but two real records reuse a target, one of the actual
loss centres has ORIGINAL exponent at least THREE. -/
theorem actual_any_width_three_loss_centres_reuse_forces_high_exponent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 3)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hab : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1) :
    ∃ v ∈ projectedLossVertices C exponent, 3 ≤ exponent v := by
  have hg :=
    actual_any_width_reused_opposite_four_centres_or_high_exponent
      C exponent choice a b ha hb hab hopposite
  rcases hg with hfour | hhigh
  · omega
  · exact hhigh

#print axioms actual_projected_loss_cube_two_disagreements_forces_exponent_three
#print axioms actual_any_width_reused_opposite_shared_owner_exponent_three
#print axioms actual_any_width_reused_opposite_four_centres_or_high_exponent
#print axioms actual_any_width_three_loss_centres_reuse_forces_high_exponent

end OrderedEdgeColoring
end JSP000404Research
