import JSP000404Research.ActualAnyWidthHighExponentReuseGate
import JSP000404Research.ResidualTwoFlipExactSymmetricDifference
import JSP000404Research.ResidualLossExternalHoleBudget
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# A truly reused ORIGINAL loss-source owner blocks the opposite corner

Two DIFFERENT actual earliest-prior source records may charge the SAME
double-flipped opposite Boolean candidate. If one genuine original
projected-loss vertex is a SOURCE owner in BOTH records, then that
shared vertex's ORIGINAL retained completion cube CONTAINS the
opposite candidate. In particular the candidate is NOT a genuine
GLOBAL true hole, nor an exterior true hole.

No exponent<=2 assumption, no n=4 assumption, no AngleCap assumption,
and no invented hole or surplus are used. This is a TRUE-HOLE
ELIGIBILITY OBSTRUCTION for shared-owner repeated source records.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Strict ordered distinct double-flip pairs sharing their genuine
chosen owner colour c have an A-only other flip colour d. -/
theorem distinct_strict_flip_pairs_shared_owner_other_exclusive
    {n : ℕ} (i j k l c : Fin n)
    (hji : j < i) (hlk : l < k)
    (hp : (i,j) ≠ (k,l))
    (hcA : c = i ∨ c = j)
    (hcB : c = k ∨ c = l) :
    ∃ d : Fin n,
      ((c = i ∧ d = j) ∨ (c = j ∧ d = i)) ∧
      d ≠ k ∧ d ≠ l := by
  rcases hcA with hi | hj
  · refine ⟨j,Or.inl ⟨hi,rfl⟩,?_,?_⟩
    · rcases hcB with hk | hl <;> omega
    · rcases hcB with hk | hl
      · intro h
        exact hp (Prod.ext (hi.symm.trans hk) h)
      · omega
  · refine ⟨i,Or.inr ⟨hj,rfl⟩,?_,?_⟩
    · rcases hcB with hk | hl
      · omega
      · intro h
        exact hp (Prod.ext h (hj.symm.trans hl))
    · rcases hcB with hk | hl <;> omega

/-- SOURCE-NATIVE statement: if two distinct genuine original
earliest-prior collision records hit ONE opposite candidate and share
an ACTUAL loss-source owner, then the opposite candidate is literally
in that owner's original retained completion cube.

This is stronger than the high-exponent overlap gate: under the
shared-owner hypothesis the candidate is covered, not merely counted
with high exponent. -/
theorem actual_any_width_shared_owner_reused_opposite_is_covered_by_owner
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
    flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
      retainedCompletionWords C v := by
  have hca := ((mem_lossCoordinateSlice C exponent choice c v).mp hv).2
  have hcb := ((mem_lossCoordinateSlice C exponent choice d v).mp hu).2
  have hcd : c = d := hca.symm.trans hcb
  have hshareB : c = b.1 ∨ c = b.2.1 := by
    rcases hud with h | h
    · exact Or.inl (hcd.trans h)
    · exact Or.inr (hcd.trans h)
  have hz' : b.2.2 ∈ translatedCompletionWords C v c := by
    rw [hcd]
    exact hz
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
  obtain ⟨e,hepos,hneK,hneL⟩ :=
    distinct_strict_flip_pairs_shared_owner_other_exclusive
      a.1 a.2.1 b.1 b.2.1 c
      horderA horderB hpair hvc hshareB
  have hflip :
      flipCompletionWord a.2.1 (flipCompletionWord a.1 a.2.2) =
      flipCompletionWord b.2.1 (flipCompletionWord b.1 b.2.2) := by
    change flipCompletionWord a.2.1 (flipCompletionWord a.1 a.2.2) =
      flipCompletionWord b.2.1 (flipCompletionWord b.1 b.2.2)
        at hopposite
    exact hopposite
  have hwordDiff : a.2.2 e ≠ b.2.2 e := by
    apply (two_flip_target_eq_source_diff_iff_pair_exclusive
      a.2.2 b.2.2 a.2.1 a.1 b.2.1 b.1
      (ne_of_lt horderA) (ne_of_lt horderB) hflip e).mpr
    refine Or.inl ⟨?_,?_⟩
    · rcases hepos with ⟨_,rfl⟩ | ⟨_,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro he
      rcases he with he | he
      · exact hneL he
      · exact hneK he
  have hnotActive : e ∉ retainedActive C v := by
    intro he
    exact hwordDiff
      (any_width_translated_cube_agrees_at_retained_active
        C v c a.2.2 b.2.2 hw hz' e he)
  have horig : flipBoolWordAt a.2.2 c ∈
      retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c a.2.2).mp hw
  have hflipped : flipBoolWordAt (flipBoolWordAt a.2.2 c) e ∈
      retainedCompletionWords C v :=
    (mem_retainedCompletionWords_flip_iff_of_inactive
      C hnotActive).2 horig
  have htarget :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt a.2.2 c) e := by
    rcases hepos with ⟨hci,hej⟩ | ⟨hcj,hei⟩
    · rw [hci,hej]
    · rw [hcj,hei]
      exact flipBoolWordAt_commute a.2.2
        (ne_of_lt horderA).symm
  rw [htarget]
  exact hflipped

/-- The actual repeated opposite candidate with a common original
owner is NOT an uncovered Boolean hole; the shared original cube
already covers it. This is independent of Boolean dimension. -/
theorem actual_any_width_shared_owner_reused_opposite_not_true_hole
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
    flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∉
      lossLedgerGlobalTrueHoles C := by
  have hmember :=
    actual_any_width_shared_owner_reused_opposite_is_covered_by_owner
      C exponent choice a b ha hb hab hopposite v c d
      hvc hud hv hu hw hz
  have hcovered :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        coveredCompletionWords C :=
    (mem_coveredCompletionWords C _).2
      ⟨v,(mem_completionFibre C _ v).2 hmember⟩
  intro hhole
  exact (Finset.mem_sdiff.mp hhole).2 hcovered

/-- In particular a common-owner repeated opposite candidate can NEVER
pay a TRUE EXTERIOR hole outside all translated-loss slices. -/
theorem actual_any_width_shared_owner_reused_opposite_not_exterior
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
    flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∉
      lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  intro hhole
  exact (actual_any_width_shared_owner_reused_opposite_not_true_hole
    C exponent choice a b ha hb hab hopposite v c d hvc hud hv hu hw hz)
    (Finset.mem_sdiff.mp hhole).1

#print axioms distinct_strict_flip_pairs_shared_owner_other_exclusive
#print axioms actual_any_width_shared_owner_reused_opposite_is_covered_by_owner
#print axioms actual_any_width_shared_owner_reused_opposite_not_true_hole
#print axioms actual_any_width_shared_owner_reused_opposite_not_exterior

end OrderedEdgeColoring
end JSP000404Research
