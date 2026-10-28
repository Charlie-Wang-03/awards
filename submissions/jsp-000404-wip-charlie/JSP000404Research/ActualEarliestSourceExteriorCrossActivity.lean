import JSP000404Research.ActualExteriorOppositeFibrePacking
import JSP000404Research.ResidualLossActiveFlipBlocker
import Mathlib.Tactic

/-!
# Full original earliest-prior debt sources: true exterior forces cross-activity

Earlier square-local true-hole criteria used the more restrictive
earliest ACTUAL EDGE carrier. This module instead starts with every
genuine earliest-prior record used by the ORIGINAL duplicate-debt sum,
even if that record was not one of the selected edge-carrier witnesses.

For an actually eligible exterior q, every original owner of its
translated source w must be ACTIVE at the OTHER flip coordinate.
Under the original root active-choice contract, both genuine source
owners are active at BOTH colours of the collision pair. This is
necessary structural data, NOT a claim of any unreserved hole payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If translating a genuine retained word at colour c and then
flipping a DIFFERENT colour d yields a GLOBAL uncovered Boolean word,
d must be retained-active at the ORIGINAL owner v. Otherwise that
double-flip word remains in the owner's original completion cube. -/
theorem actual_translated_owner_true_hole_forces_other_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c d : Fin n) (w : Fin n → Bool)
    (hw : w ∈ translatedCompletionWords C v c)
    (hq : flipBoolWordAt (flipBoolWordAt w c) d ∈
      lossLedgerGlobalTrueHoles C) :
    d ∈ retainedActive C v := by
  classical
  by_contra hnot
  have horig : flipBoolWordAt w c ∈
      retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c w).mp hw
  have hstill :
      flipBoolWordAt (flipBoolWordAt w c) d ∈
        retainedCompletionWords C v :=
    (mem_retainedCompletionWords_flip_iff_of_inactive
      C hnot).2 horig
  have hcovered :
      flipBoolWordAt (flipBoolWordAt w c) d ∈
        coveredCompletionWords C :=
    (mem_coveredCompletionWords C _).2
      ⟨v,(mem_completionFibre C _ v).2 hstill⟩
  exact (Finset.mem_sdiff.mp hq).2 hcovered

/-- For ANY genuine source record used in the exact original
earliest-prior duplicate-debt sum, a true exterior opposite word
forces every genuine owner in its c-slice to retain the OTHER
flip colour, even before assuming the chosen colour is active. -/
theorem actual_earliest_exterior_record_owner_other_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hq : flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
      lossLedgerOutsideTranslatedTrueHoles C exponent choice)
    (v : V) (c : Fin n)
    (hc : c = a.1 ∨ c = a.2.1)
    (hv : v ∈ lossCoordinateSlice C exponent choice c)
    (hw : a.2.2 ∈ translatedCompletionWords C v c) :
    (c = a.1 → a.2.1 ∈ retainedActive C v) ∧
    (c = a.2.1 → a.1 ∈ retainedActive C v) := by
  have hglobal : flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
      lossLedgerGlobalTrueHoles C :=
    (Finset.mem_sdiff.mp hq).1
  have horder := (actual_earliest_loss_collision_record_valid
    C exponent choice a ha).2.1
  constructor
  · intro hcfirst
    have hcq :
        flipBoolWordAt (flipBoolWordAt a.2.2 c) a.2.1 ∈
          lossLedgerGlobalTrueHoles C := by
      rw [hcfirst]
      exact hglobal
    exact actual_translated_owner_true_hole_forces_other_active
      C v c a.2.1 a.2.2 hw hcq
  · intro hcsecond
    have hcq :
        flipBoolWordAt (flipBoolWordAt a.2.2 c) a.1 ∈
          lossLedgerGlobalTrueHoles C := by
      rw [hcsecond]
      rw [← flipBoolWordAt_commute a.2.2 (ne_of_lt horder).symm]
      exact hglobal
    exact actual_translated_owner_true_hole_forces_other_active
      C v c a.1 a.2.2 hw hcq

/-- Under the ROOT active-choice contract, an eligible original
earliest-prior debt record has TWO DISTINCT genuine projected-loss
owners, each retained-active at BOTH true collision colours. These
witnesses are original vertices, not synthetic paid-hole tokens. -/
theorem actual_earliest_exterior_record_has_two_biactive_owners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hq : flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    ∃ v u : V,
      v ≠ u ∧
      v ∈ projectedLossVertices C exponent ∧
      u ∈ projectedLossVertices C exponent ∧
      a.1 ∈ retainedActive C v ∧
      a.2.1 ∈ retainedActive C v ∧
      a.1 ∈ retainedActive C u ∧
      a.2.1 ∈ retainedActive C u ∧
      a.2.2 ∈ translatedCompletionWords C v a.1 ∧
      a.2.2 ∈ translatedCompletionWords C u a.2.1 := by
  obtain ⟨v,u,hv,hu,hw,hz⟩ :=
    actual_earliest_record_has_two_word_owners C exponent choice a ha
  have hvdata := (mem_lossCoordinateSlice C exponent choice a.1 v).mp hv
  have hudata := (mem_lossCoordinateSlice C exponent choice a.2.1 u).mp hu
  have hvc : a.1 ∈ retainedActive C v := by
    rw [← hvdata.2]
    exact hchoice v hvdata.1
  have huc : a.2.1 ∈ retainedActive C u := by
    rw [← hudata.2]
    exact hchoice u hudata.1
  have hvother :=
    (actual_earliest_exterior_record_owner_other_active
      C exponent choice a ha hq v a.1 (Or.inl rfl) hv hw).1 rfl
  have huother :=
    (actual_earliest_exterior_record_owner_other_active
      C exponent choice a ha hq u a.2.1 (Or.inr rfl) hu hz).2 rfl
  have hne : v ≠ u := by
    intro heq
    subst u
    have hchoiceeq : a.1 = a.2.1 := hvdata.2.symm.trans hudata.2
    exact ((actual_earliest_loss_collision_record_valid
      C exponent choice a ha).1) hchoiceeq
  exact ⟨v,u,hne,hvdata.1,hudata.1,
    hvc,hvother,huother,huc,hw,hz⟩

#print axioms actual_translated_owner_true_hole_forces_other_active
#print axioms actual_earliest_exterior_record_owner_other_active
#print axioms actual_earliest_exterior_record_has_two_biactive_owners

end OrderedEdgeColoring
end JSP000404Research
