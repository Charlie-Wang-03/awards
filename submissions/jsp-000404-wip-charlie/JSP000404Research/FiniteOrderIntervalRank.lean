import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Finite linear-order interval span rank

For a finite linearly ordered type, measure an unordered pair {a,b} by the
cardinality of its closed order interval.  If one endpoint is held fixed and
the other moves strictly outward past the old endpoint, the interval span
strictly grows.

The complementary natural-valued rank

  |V| - span(a,b)

therefore strictly decreases under outward rematching.
-/

namespace JSP000404Research

def orderIntervalSpan
    {V : Type*} [LinearOrder V] [Fintype V]
    (a b : V) : ℕ :=
  if a ≤ b then (Finset.Icc a b).card else (Finset.Icc b a).card

def orderIntervalRank
    {V : Type*} [LinearOrder V] [Fintype V]
    (a b : V) : ℕ :=
  Fintype.card V - orderIntervalSpan a b

theorem orderIntervalSpan_symm
    {V : Type*} [LinearOrder V] [Fintype V]
    (a b : V) :
    orderIntervalSpan a b = orderIntervalSpan b a := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · unfold orderIntervalSpan
    simp [hab.le, not_le_of_gt hab]
  · rfl
  · unfold orderIntervalSpan
    simp [hba.le, not_le_of_gt hba]

theorem Icc_ssubset_Icc_of_right_lt
    {V : Type*} [LinearOrder V]
    {a b c : V}
    (hab : a ≤ b)
    (hbc : b < c) :
    Set.Icc a b ⊂ Set.Icc a c := by
  constructor
  · intro x hx
    exact ⟨hx.1, hx.2.trans hbc.le⟩
  · intro hEq
    have hcOld : c ∈ Set.Icc a b := by
      rw [hEq]
      exact ⟨hab.trans hbc.le, le_rfl⟩
    exact (not_le_of_gt hbc) hcOld.2

theorem finset_Icc_ssubset_of_right_lt
    {V : Type*} [LinearOrder V] [LocallyFiniteOrder V]
    [LocallyFiniteOrderBot V] [LocallyFiniteOrderTop V]
    {a b c : V}
    (hab : a ≤ b)
    (hbc : b < c) :
    Finset.Icc a b ⊂ Finset.Icc a c := by
  constructor
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1,hx.2.trans hbc.le⟩
  · intro hEq
    have hcOld : c ∈ Finset.Icc a b := by
      rw [hEq]
      simp only [Finset.mem_Icc]
      exact ⟨hab.trans hbc.le,le_rfl⟩
    simp only [Finset.mem_Icc] at hcOld
    exact (not_le_of_gt hbc) hcOld.2

theorem orderIntervalSpan_lt_of_same_left_outward
    {V : Type*} [LinearOrder V] [Fintype V]
    {a b c : V}
    (hab : a ≤ b)
    (hbc : b < c) :
    orderIntervalSpan a b < orderIntervalSpan a c := by
  classical
  unfold orderIntervalSpan
  have hac : a ≤ c := hab.trans hbc.le
  simp [hab,hac]
  apply Finset.card_lt_card
  constructor
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1,hx.2.trans hbc.le⟩
  · intro hEq
    have hcOld : c ∈ Finset.Icc a b := by
      rw [hEq]
      simp only [Finset.mem_Icc]
      exact ⟨hac,le_rfl⟩
    simp only [Finset.mem_Icc] at hcOld
    exact (not_le_of_gt hbc) hcOld.2

theorem orderIntervalSpan_lt_of_same_right_outward
    {V : Type*} [LinearOrder V] [Fintype V]
    {a b c : V}
    (hcb : c < b)
    (hba : b ≤ a) :
    orderIntervalSpan a b < orderIntervalSpan a c := by
  classical
  unfold orderIntervalSpan
  have hca : c ≤ a := hcb.le.trans hba
  have habBranch : ¬ a ≤ b := by
    by_cases hEq : a = b
    · subst a
      exact not_le_of_gt hcb
    · exact not_le_of_gt (lt_of_le_of_ne hba hEq.symm)
  have hacBranch : ¬ a ≤ c := by
    exact not_le_of_gt (hcb.trans_le hba)
  simp [habBranch,hacBranch]
  apply Finset.card_lt_card
  constructor
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hcb.le.trans hx.1,hx.2⟩
  · intro hEq
    have hcOld : c ∈ Finset.Icc b a := by
      rw [hEq]
      simp only [Finset.mem_Icc]
      exact ⟨le_rfl,hca⟩
    simp only [Finset.mem_Icc] at hcOld
    exact (not_le_of_gt hcb) hcOld.1

theorem orderIntervalRank_lt_of_span_lt
    {V : Type*} [LinearOrder V] [Fintype V]
    {a b c d : V}
    (hspan :
      orderIntervalSpan c d >
        orderIntervalSpan a b) :
    orderIntervalRank c d <
      orderIntervalRank a b := by
  unfold orderIntervalRank
  have habBound :
      orderIntervalSpan a b ≤ Fintype.card V := by
    unfold orderIntervalSpan
    split_ifs <;> exact Finset.card_le_univ _
  have hcdBound :
      orderIntervalSpan c d ≤ Fintype.card V := by
    unfold orderIntervalSpan
    split_ifs <;> exact Finset.card_le_univ _
  omega

#print axioms orderIntervalSpan_lt_of_same_left_outward
#print axioms orderIntervalRank_lt_of_span_lt

end JSP000404Research
