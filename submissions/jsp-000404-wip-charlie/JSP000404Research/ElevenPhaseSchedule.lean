import JSP000404Research.ElevenPhaseRows

/-!
# A forty-point bound for coherent integer pair times

The only order hypothesis is the actual middle-pair betweenness for each increasing
triple. Local signed gaps construct the rows; modular order transport supplies their
coherence in every labeling of a triple.
-/

namespace JSP000404Research.ElevenPhase

variable {V : Type*} [LinearOrder V]

def pairBefore (time : V → V → ℤ) (v w : V) : Bool :=
  if v < w then phaseBefore (time v w) else !phaseBefore (time v w)

theorem pairBefore_swap (time : V → V → ℤ) (hsymm : ∀ v w, time v w = time w v)
    {v w : V} (hvw : v ≠ w) : pairBefore time w v = !pairBefore time v w := by
  rcases lt_or_gt_of_ne hvw with h | h
  · simp [pairBefore, h, not_lt_of_ge h.le, hsymm w v]
  · simp [pairBefore, h, not_lt_of_ge h.le, hsymm w v]

theorem coherent_order_of_symmetric_times (time : V → V → ℤ)
    (hsymm : ∀ v w, time v w = time w v)
    (htriangle : ∀ {a b c}, a < b → b < c →
      Between (time a c) (time a b) (time b c) ∧ |time b c - time a b| ≤ 11 ∧
        2 ≤ |time b c - time a b| ∧ |time a c - time a b| ≤ 9 ∧
        |time b c - time a c| ≤ 9)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    OrderedPhases (time a b % 11) (time a c % 11) (time b c % 11)
      (pairBefore time a b) (pairBefore time a c) (pairBefore time b c) := by
  let Q (a b c : V) := OrderedPhases (time a b % 11) (time a c % 11) (time b c % 11)
    (pairBefore time a b) (pairBefore time a c) (pairBefore time b c)
  have hsorted {a b c : V} (hab : a < b) (hbc : b < c) : Q a b c := by
    obtain ⟨hbetween, hspan, hsep, hleft, hright⟩ := htriangle hab hbc
    simpa only [Q, pairBefore, ite_eq_left hab, ite_eq_left hbc,
      ite_eq_left (hab.trans hbc)] using
      ordered_phases_of_integer_triangle hbetween hspan hsep hleft hright
  have hswapFirst {a b c : V} (hab : a ≠ b) (h : Q a b c) : Q b a c := by
    dsimp only [Q] at *
    rw [hsymm b a, pairBefore_swap time hsymm hab]
    exact (ordered_phases_swap_first _ _ _ _ _ _).mp h
  have hswapLast {a b c : V} (hbc : b ≠ c) (h : Q a b c) : Q a c b := by
    dsimp only [Q] at *
    rw [hsymm c b, pairBefore_swap time hsymm hbc]
    exact (ordered_phases_swap_last _ _ _ _ _ _).mp h
  change Q a b c
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact hsorted hab hbc
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact hswapLast hcb.ne (hsorted hac hcb)
      · exact hswapLast (hca.trans hab).ne (hswapFirst hca.ne (hsorted hca hab))
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact hswapFirst hba.ne (hsorted hba hac)
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact hswapFirst hba.ne (hswapLast hca.ne (hsorted hbc hca))
      · exact hswapFirst hba.ne
          (hswapLast (hcb.trans hba).ne (hswapFirst hcb.ne (hsorted hcb hba)))

theorem before_of_event_row {r : Fin 11 → Option Bool} {time : ℤ} {sign : Bool}
    (h : r (phaseOf time) = some (OddWire.eventBit time sign)) :
    before r (phaseOf time) = if sign then phaseBefore time else !phaseBefore time := by
  unfold before
  rw [h, phaseOf_value]
  cases sign
  · exact event_bit_before_false time
  · exact event_bit_before time

theorem shared_of_some_ne {r s : Fin 11 → Option Bool} {c : Fin 11} {a b : Bool}
    (hr : r c = some a) (hs : s c = some b) (hab : a ≠ b) : Shared r s c := by
  cases a <;> cases b <;> simp_all [Shared]

theorem card_le_forty_of_ordered_times [Fintype V] (time : V → V → ℤ)
    (hsymm : ∀ v w, time v w = time w v)
    (hspan : ∀ v e f, v ≠ e → v ≠ f → |time v f - time v e| ≤ 11)
    (hsame : ∀ v e f, v ≠ e → v ≠ f → decide (v < e) = decide (v < f) →
      |time v f - time v e| ≤ 9)
    (hdifferent : ∀ v e f, v ≠ e → v ≠ f → decide (v < e) ≠ decide (v < f) →
      2 ≤ |time v f - time v e|)
    (hbetween : ∀ {a b c}, a < b → b < c → Between (time a c) (time a b) (time b c)) :
    Fintype.card V ≤ 40 := by
  classical
  obtain ⟨r, hvalid, hrow⟩ := exists_rows_of_local_times time (fun v w ↦ v ≠ w)
    (fun v w ↦ decide (v < w)) hspan hsame hdifferent
  have htriangle {a b c : V} (hab : a < b) (hbc : b < c) :
      Between (time a c) (time a b) (time b c) ∧ |time b c - time a b| ≤ 11 ∧
        2 ≤ |time b c - time a b| ∧ |time a c - time a b| ≤ 9 ∧
        |time b c - time a c| ≤ 9 := by
    have hac := hab.trans hbc
    refine ⟨hbetween hab hbc, ?_, ?_, ?_, ?_⟩
    · simpa only [hsymm b a] using hspan b a c hab.ne.symm hbc.ne
    · simpa only [hsymm b a] using hdifferent b a c hab.ne.symm hbc.ne
        (by simp [hbc, not_lt_of_ge hab.le])
    · exact hsame a b c hab.ne hac.ne (by simp [hab, hac])
    · simpa only [hsymm c a, hsymm c b] using hsame c a b hac.ne.symm hbc.ne.symm
        (by simp [not_lt_of_ge hac.le, not_lt_of_ge hbc.le])
  apply card_le_forty_of_coherent_rows r hvalid (fun v w ↦ phaseOf (time v w))
  · intro v w hvw
    have hv := hrow v w hvw
    have hw := hrow w v hvw.symm
    rw [hsymm w v] at hw
    apply shared_of_some_ne hv hw
    apply OddWire.eventBit_ne
    rcases lt_or_gt_of_ne hvw with h | h <;> simp [h, not_lt_of_ge h.le]
  · intro a b c hab hac hbc
    rw [phaseOf_value, phaseOf_value, phaseOf_value,
      before_of_event_row (hrow a b hab), before_of_event_row (hrow a c hac),
      before_of_event_row (hrow b c hbc)]
    simpa [pairBefore] using coherent_order_of_symmetric_times time hsymm
      (fun {a b c} hab hbc ↦ htriangle hab hbc) a b c hab hac hbc

#print axioms coherent_order_of_symmetric_times
#print axioms card_le_forty_of_ordered_times

end JSP000404Research.ElevenPhase
