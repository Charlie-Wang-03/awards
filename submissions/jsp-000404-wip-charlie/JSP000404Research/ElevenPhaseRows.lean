import JSP000404Research.ElevenPhaseCapacity

/-!
# Every incident event survives the eleven-phase row construction

The row interface retains its value at each original incident event. This permits the
subsequent proof to transport the actual three-event order into the completed row family.
-/

namespace JSP000404Research.ElevenPhase

def phaseOf (time : ℤ) : Fin 11 := ⟨(time % 11).toNat, by omega⟩

theorem phaseOf_value (time : ℤ) : ((phaseOf time).val : ℤ) = time % 11 :=
  Int.toNat_of_nonneg (Int.emod_nonneg time (by decide))

theorem eventBit_eq_of_congruent {a b : ℤ} {sa sb : Bool}
    (hmod : a % 11 = b % 11) (hspan : |b - a| ≤ 11)
    (hsame : sa = sb → |b - a| ≤ 9) (hdifferent : sa ≠ sb → 2 ≤ |b - a|) :
    OddWire.eventBit a sa = OddWire.eventBit b sb := by
  rcases le_total a b with hab | hba
  all_goals first
    | simp only [abs_of_nonneg (sub_nonneg.mpr hab)] at hspan hsame hdifferent
    | simp only [abs_of_nonpos (sub_nonpos.mpr hba)] at hspan hsame hdifferent
  all_goals cases sa <;> cases sb <;>
    simp_all only [ne_eq, Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false,
      not_false_eq_true, false_implies, forall_const, OddWire.eventBit,
      Bool.not_true, Bool.not_false]
    <;> split_ifs <;> first | decide | omega

theorem eventBit_ne_of_adjacent {a b : ℤ} {sa sb : Bool}
    (hadj : (a % 11 + 1) % 11 = b % 11) (hspan : |b - a| ≤ 11)
    (hsame : sa = sb → |b - a| ≤ 9) (hdifferent : sa ≠ sb → 2 ≤ |b - a|) :
    OddWire.eventBit a sa ≠ OddWire.eventBit b sb := by
  rcases le_total a b with hab | hba
  all_goals first
    | simp only [abs_of_nonneg (sub_nonneg.mpr hab)] at hspan hsame hdifferent
    | simp only [abs_of_nonpos (sub_nonpos.mpr hba)] at hspan hsame hdifferent
  all_goals cases sa <;> cases sb <;>
    simp_all only [ne_eq, Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false,
      not_false_eq_true, false_implies, forall_const, OddWire.eventBit,
      Bool.not_true, Bool.not_false]
    <;> split_ifs <;> first | decide | omega

theorem exists_rows_of_local_times {V E : Type*} (time : V → E → ℤ)
    (incident : V → E → Prop) (sign : V → E → Bool)
    (hspan : ∀ v e f, incident v e → incident v f → |time v f - time v e| ≤ 11)
    (hsame : ∀ v e f, incident v e → incident v f → sign v e = sign v f →
      |time v f - time v e| ≤ 9)
    (hdifferent : ∀ v e f, incident v e → incident v f → sign v e ≠ sign v f →
      2 ≤ |time v f - time v e|) :
    ∃ r : V → Fin 11 → Option Bool, (∀ v, OddWire.PartialValid (r v)) ∧
      ∀ v e, incident v e →
        r v (phaseOf (time v e)) = some (OddWire.eventBit (time v e) (sign v e)) := by
  classical
  have hconsistent (v : V) (e f : E) (he : incident v e) (hf : incident v f)
      (hband : phaseOf (time v e) = phaseOf (time v f)) :
      OddWire.eventBit (time v e) (sign v e) =
        OddWire.eventBit (time v f) (sign v f) := by
    have hmod : time v e % 11 = time v f % 11 := by
      rw [← phaseOf_value (time v e), ← phaseOf_value (time v f), hband]
    exact eventBit_eq_of_congruent hmod (hspan v e f he hf)
      (hsame v e f he hf) (hdifferent v e f he hf)
  let r (v : V) (c : Fin 11) : Option Bool :=
    if h : ∃ e, incident v e ∧ phaseOf (time v e) = c then
      some (OddWire.eventBit (time v h.choose) (sign v h.choose)) else none
  have hrow_event (v : V) (e : E) (he : incident v e) :
      r v (phaseOf (time v e)) = some (OddWire.eventBit (time v e) (sign v e)) := by
    have hex : ∃ f, incident v f ∧ phaseOf (time v f) = phaseOf (time v e) := ⟨e, he, rfl⟩
    dsimp only [r]
    rw [dite_eq_left hex]
    exact congrArg some (hconsistent v hex.choose e hex.choose_spec.1 he hex.choose_spec.2)
  have hrow_some (v : V) (c : Fin 11) (b : Bool) (hrow : r v c = some b) :
      ∃ e, incident v e ∧ phaseOf (time v e) = c ∧
        OddWire.eventBit (time v e) (sign v e) = b := by
    by_cases hex : ∃ e, incident v e ∧ phaseOf (time v e) = c
    · simp only [r, dite_eq_left hex] at hrow
      exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, Option.some.inj hrow⟩
    · simp [r, hex] at hrow
  refine ⟨r, ?_, hrow_event⟩
  intro v a b hadj bit ha hb
  obtain ⟨e, he, hbe, hse⟩ := hrow_some v a bit ha
  obtain ⟨f, hf, hbf, hsf⟩ := hrow_some v b bit hb
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hadj
  have hmod : (time v e % 11 + 1) % 11 = time v f % 11 := by
    change (((a.val + 1) % 11 : ℕ) : ℤ) = b.val at hcast
    push_cast at hcast
    rw [← hbe, ← hbf, phaseOf_value, phaseOf_value] at hcast
    exact hcast
  have hne := eventBit_ne_of_adjacent hmod (hspan v e f he hf)
    (hsame v e f he hf) (hdifferent v e f he hf)
  exact hne (hse.trans hsf.symm)

#print axioms exists_rows_of_local_times

end JSP000404Research.ElevenPhase
