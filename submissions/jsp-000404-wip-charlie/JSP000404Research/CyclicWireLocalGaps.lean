import JSP000404Research.IntegralWireCapacity

/-!
# Incident gaps from an integral cyclic wire schedule

Nonnegative consecutive time increments make each wire monotone between cuts. A zero
increment preserves the movement sign. Across the reflected seam, a zero remaining gap
requires opposite endpoint signs. These facts imply all the local gap hypotheses needed
by the integral Boolean coding theorem.
-/

namespace JSP000404Research
namespace IntegralWire

theorem sign_eq_of_equal_time
    {m : ℕ} (time : Fin (m + 1) → ℤ) (sign : Fin (m + 1) → Bool)
    (hmono : Monotone time)
    (hstep : ∀ i : Fin m, time i.castSucc = time i.succ → sign i.castSucc = sign i.succ)
    {i j : Fin (m + 1)} (heq : time i = time j) : sign i = sign j := by
  have hforward : ∀ j : Fin (m + 1), ∀ i, i ≤ j → time i = time j → sign i = sign j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro i hi _
      have : i = 0 := le_antisymm hi (Fin.zero_le i)
      subst i
      rfl
    | succ j ih =>
      intro i hij htime
      by_cases hequal : i = j.succ
      · subst i
        rfl
      have hiprev : i ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ j.val
        have hijval := hij
        change i.val ≤ j.val + 1 at hijval
        have hneval : i.val ≠ j.val + 1 := by
          intro h
          exact hequal (Fin.ext h)
        omega
      have hprev : time i = time j.castSucc := by
        have hlo := hmono hiprev
        have hhi := hmono (Fin.castSucc_le_succ j)
        omega
      exact (ih i hiprev hprev).trans (hstep j (hprev.symm.trans htime))
  rcases le_total i j with hij | hji
  · exact hforward j i hij heq
  · exact (hforward i j hji heq.symm).symm

theorem local_signed_gaps_of_monotone_schedule
    {m : ℕ} (time : Fin (m + 1) → ℤ) (sign : Fin (m + 1) → Bool) (period : ℤ)
    (hmono : Monotone time)
    (hstep : ∀ i : Fin m, time i.castSucc = time i.succ → sign i.castSucc = sign i.succ)
    (hspan : time (Fin.last m) - time 0 ≤ period)
    (hseam : time (Fin.last m) - time 0 = period → sign (Fin.last m) ≠ sign 0)
    (i j : Fin (m + 1)) :
    |time j - time i| ≤ period ∧
      (sign i = sign j → |time j - time i| < period) ∧
      (sign i ≠ sign j → 1 ≤ |time j - time i|) := by
  have hi0 := hmono (Fin.zero_le i)
  have hj0 := hmono (Fin.zero_le j)
  have hilast := hmono (Fin.le_last i)
  have hjlast := hmono (Fin.le_last j)
  have hbound : |time j - time i| ≤ period := by
    rw [abs_le]
    omega
  refine ⟨hbound, ?_, ?_⟩
  · intro hsign
    by_contra hnot
    have hequal : |time j - time i| = period := le_antisymm hbound (le_of_not_gt hnot)
    have hfull : time (Fin.last m) - time 0 = period := by
      rcases le_total (time i) (time j) with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hequal
        omega
      · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hequal
        omega
    apply hseam hfull
    rcases le_total (time i) (time j) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hequal
      have he0 : time i = time 0 := by omega
      have helast : time j = time (Fin.last m) := by omega
      exact (sign_eq_of_equal_time time sign hmono hstep helast).symm.trans
        (hsign.symm.trans (sign_eq_of_equal_time time sign hmono hstep he0))
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hequal
      have he0 : time j = time 0 := by omega
      have helast : time i = time (Fin.last m) := by omega
      exact (sign_eq_of_equal_time time sign hmono hstep helast).symm.trans
        (hsign.trans (sign_eq_of_equal_time time sign hmono hstep he0))
  · intro hdifferent
    have hne : time i ≠ time j := by
      intro heq
      exact hdifferent (sign_eq_of_equal_time time sign hmono hstep heq)
    have habs : 0 < |time j - time i| := abs_pos.mpr (sub_ne_zero.mpr hne.symm)
    omega

/-- The required incident bounds follow from the consecutive cyclic delay constraints. -/
theorem local_signed_gaps_of_cyclic_delays
    {m : ℕ} (time : Fin (m + 1) → ℤ) (sign : Fin (m + 1) → Bool) (period : ℤ)
    (hadjacent : ∀ i : Fin m,
      (if sign i.castSucc = sign i.succ then (0 : ℤ) else 1) ≤ time i.succ - time i.castSucc)
    (hwrap : (if sign (Fin.last m) = sign 0 then (1 : ℤ) else 0) ≤
      time 0 - time (Fin.last m) + period) (i j : Fin (m + 1)) :
    |time j - time i| ≤ period ∧
      (sign i = sign j → |time j - time i| < period) ∧
      (sign i ≠ sign j → 1 ≤ |time j - time i|) := by
  have hstep (i : Fin m) : time i.castSucc ≤ time i.succ := by
    have h := hadjacent i
    split_ifs at h <;> omega
  have hmono : Monotone time := Fin.monotone_iff_le_succ.mpr hstep
  apply local_signed_gaps_of_monotone_schedule time sign period hmono
  · intro k htime
    have h := hadjacent k
    split_ifs at h with heq
    · exact heq
    · omega
  · split_ifs at hwrap <;> omega
  · intro hfull heq
    rw [ite_eq_left heq] at hwrap
    omega

/-- Complete local wire lists satisfying the cyclic delays obey the dyadic bound. -/
theorem card_le_two_pow_of_cyclic_wire_schedules
    {V E : Type*} [Fintype V] {m : ℕ} (period : ℕ) (hperiod : 0 < period)
    (time : E → ℤ) (wire : V → Fin (m + 1) → E) (sign : V → E → Bool)
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire v i.castSucc) = sign v (wire v i.succ) then (0 : ℤ) else 1) ≤
        time (wire v i.succ) - time (wire v i.castSucc))
    (hwrap : ∀ v,
      (if sign v (wire v (Fin.last m)) = sign v (wire v 0) then (1 : ℤ) else 0) ≤
        time (wire v 0) - time (wire v (Fin.last m)) + period)
    (hpair : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j ∧
      sign v (wire v i) ≠ sign w (wire w j)) : Fintype.card V ≤ 2 ^ period := by
  let incident (v : V) (e : E) : Prop := ∃ i, wire v i = e
  have hgaps (v : V) (i j : Fin (m + 1)) := local_signed_gaps_of_cyclic_delays
    (fun i ↦ time (wire v i)) (fun i ↦ sign v (wire v i)) period
    (hadjacent v) (hwrap v) i j
  apply card_le_two_pow_of_integral_events period hperiod time incident sign
  · rintro v e f ⟨i, rfl⟩ ⟨j, rfl⟩
    exact (hgaps v i j).1
  · rintro v e f ⟨i, rfl⟩ ⟨j, rfl⟩
    exact (hgaps v i j).2.1
  · rintro v e f ⟨i, rfl⟩ ⟨j, rfl⟩
    exact (hgaps v i j).2.2
  · intro v w hvw
    obtain ⟨i, j, heq, hsign⟩ := hpair v w hvw
    refine ⟨wire v i, ⟨i, rfl⟩, ⟨j, heq.symm⟩, ?_⟩
    simpa only [heq] using hsign

#print axioms sign_eq_of_equal_time
#print axioms local_signed_gaps_of_monotone_schedule
#print axioms local_signed_gaps_of_cyclic_delays
#print axioms card_le_two_pow_of_cyclic_wire_schedules

end IntegralWire
end JSP000404Research
