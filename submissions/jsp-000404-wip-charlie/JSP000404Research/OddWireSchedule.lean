import JSP000404Research.SmallOddWireCapacity
import JSP000404Research.CyclicWireGraph

/-!
# Doubled cyclic delays and small odd capacities

Consecutive two-unit delays imply the full incident signed-gap conditions. Half-grid
retiming therefore connects three- and five-phase coding to strict cyclic wire schedules.
-/

namespace JSP000404Research
namespace OddWire

theorem sign_eq_of_forward_gap_lt_two
    {m : ℕ} (time : Fin (m + 1) → ℤ) (sign : Fin (m + 1) → Bool)
    (hmono : Monotone time)
    (hadjacent : ∀ i : Fin m,
      (if sign i.castSucc = sign i.succ then (0 : ℤ) else 2) ≤
        time i.succ - time i.castSucc)
    {i j : Fin (m + 1)} (hle : time i ≤ time j) (hgap : time j - time i < 2) :
    sign i = sign j := by
  let shifted (k : Fin (m + 1)) := (time k - time i) / 2
  have hshifted : Monotone shifted := by
    intro a b hab
    have h := hmono hab
    dsimp [shifted]
    omega
  apply IntegralWire.sign_eq_of_equal_time shifted sign hshifted
  · intro k hequal
    have h := hadjacent k
    dsimp [shifted] at hequal
    split_ifs at h with hsign
    · exact hsign
    · omega
  · dsimp [shifted]
    omega

/-- Doubled cyclic delays give a two-unit separation and the reflected closing bound. -/
theorem local_signed_gaps_of_doubled_delays
    {m : ℕ} (time : Fin (m + 1) → ℤ) (sign : Fin (m + 1) → Bool) (period : ℤ)
    (hadjacent : ∀ i : Fin m,
      (if sign i.castSucc = sign i.succ then (0 : ℤ) else 2) ≤
        time i.succ - time i.castSucc)
    (hwrap : (if sign (Fin.last m) = sign 0 then (2 : ℤ) else 0) ≤
      time 0 - time (Fin.last m) + period) (i j : Fin (m + 1)) :
    |time j - time i| ≤ period ∧
      (sign i = sign j → |time j - time i| ≤ period - 2) ∧
      (sign i ≠ sign j → 2 ≤ |time j - time i|) := by
  have hmono : Monotone time := Fin.monotone_iff_le_succ.mpr (by
    intro k
    have h := hadjacent k
    split_ifs at h <;> omega)
  have hfull : time (Fin.last m) - time 0 ≤ period := by
    split_ifs at hwrap <;> omega
  have hforward (i j : Fin (m + 1)) (hle : time i ≤ time j) :
      time j - time i ≤ period ∧
        (sign i = sign j → time j - time i ≤ period - 2) ∧
        (sign i ≠ sign j → 2 ≤ time j - time i) := by
    have hi0 := hmono (Fin.zero_le i)
    have hjlast := hmono (Fin.le_last j)
    refine ⟨by omega, ?_, ?_⟩
    · intro hequal
      by_contra hlarge
      have hfirst := sign_eq_of_forward_gap_lt_two time sign hmono hadjacent hi0
        (show time i - time 0 < 2 by omega)
      have hlast := sign_eq_of_forward_gap_lt_two time sign hmono hadjacent hjlast
        (show time (Fin.last m) - time j < 2 by omega)
      have hends : sign (Fin.last m) = sign 0 :=
        hlast.symm.trans (hequal.symm.trans hfirst.symm)
      rw [ite_eq_left hends] at hwrap
      omega
    · intro hne
      by_contra hsmall
      exact hne (sign_eq_of_forward_gap_lt_two time sign hmono hadjacent hle (by omega))
  rcases le_total (time i) (time j) with hle | hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hforward i j hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    obtain ⟨hbound, hsame, hdifferent⟩ := hforward j i hle
    refine ⟨by omega, fun h ↦ ?_, fun h ↦ ?_⟩
    · have h := hsame h.symm
      omega
    · have h := hdifferent (Ne.symm h)
      omega

theorem exists_partial_rows_of_cyclic_schedules
    {V E : Type*} {m : ℕ} (q : ℕ) (hq : q = 3 ∨ q = 5 ∨ q = 7)
    (time : E → ℤ) (wire : V → Fin (m + 1) → E) (sign : V → E → Bool)
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire v i.castSucc) = sign v (wire v i.succ) then (0 : ℤ) else 2) ≤
        time (wire v i.succ) - time (wire v i.castSucc))
    (hwrap : ∀ v,
      (if sign v (wire v (Fin.last m)) = sign v (wire v 0) then (2 : ℤ) else 0) ≤
        time (wire v 0) - time (wire v (Fin.last m)) + q)
    (hpair : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j ∧
      sign v (wire v i) ≠ sign w (wire w j)) :
    ∃ row : V → Fin q → Option Bool, (∀ v, PartialValid (row v)) ∧
      ∀ v w, v ≠ w → ∃ c a b, row v c = some a ∧ row w c = some b ∧ a ≠ b := by
  let incident (v : V) (e : E) : Prop := ∃ i, wire v i = e
  have hgaps (v : V) (i j : Fin (m + 1)) := local_signed_gaps_of_doubled_delays
    (fun i ↦ time (wire v i)) (fun i ↦ sign v (wire v i)) q
    (hadjacent v) (hwrap v) i j
  apply exists_partial_rows_of_events q hq time incident sign
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

theorem card_le_small_period_of_cyclic_schedules
    {V E : Type*} [Fintype V] {m : ℕ} (q : ℕ) (hq : q = 3 ∨ q = 5)
    (time : E → ℤ) (wire : V → Fin (m + 1) → E) (sign : V → E → Bool)
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire v i.castSucc) = sign v (wire v i.succ) then (0 : ℤ) else 2) ≤
        time (wire v i.succ) - time (wire v i.castSucc))
    (hwrap : ∀ v,
      (if sign v (wire v (Fin.last m)) = sign v (wire v 0) then (2 : ℤ) else 0) ≤
        time (wire v 0) - time (wire v (Fin.last m)) + q)
    (hpair : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j ∧
      sign v (wire v i) ≠ sign w (wire w j)) : Fintype.card V ≤ q := by
  obtain ⟨row, hvalid, hsep⟩ := exists_partial_rows_of_cyclic_schedules q (by omega)
    time wire sign hadjacent hwrap hpair
  exact card_le_small_period_of_rows hq row hvalid hsep

end OddWire

namespace WireGraph

open Quiver

theorem exists_partial_rows_of_simple_cycle_winding
    {V E : Type*} {m : ℕ} (q : ℕ) (hq : q = 3 ∨ q = 5 ∨ q = 7)
    (wire : V → Fin (m + 1) → E) (sign : V → E → Bool) (original : E → ℝ)
    (hcover : ∀ e : E, ∃ v i, wire v i = e)
    (hpair : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j ∧
      sign v (wire v i) ≠ sign w (wire w j))
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire v i.castSucc) = sign v (wire v i.succ) then (0 : ℝ) else 1) <
        original (wire v i.succ) - original (wire v i.castSucc))
    (hclosing : ∀ v,
      (if sign v (wire v (Fin.last m)) = sign v (wire v 0) then (1 : ℝ) else 0) <
        original (wire v 0) - original (wire v (Fin.last m)) + ((q : ℝ) + 1) / 2)
    (hcycles : ∀ (e : Event wire) (p : Quiver.Path (V := Event wire) e e),
      p.vertices.dropLast.Nodup → p.length ≠ 0 →
        CyclicGraph.pathWeight (winding wire) p = 1 ∨
        CyclicGraph.pathWeight (winding wire) p = 2) :
    ∃ row : V → Fin q → Option Bool, (∀ v, OddWire.PartialValid (row v)) ∧
      ∀ v w, v ≠ w → ∃ c a b, row v c = some a ∧ row w c = some b ∧ a ≠ b := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hempty => exact ⟨fun _ _ ↦ none, fun v ↦ isEmptyElim v, fun v ↦ isEmptyElim v⟩
  | inr hnonempty =>
    obtain ⟨v₀⟩ := hnonempty
    have hconnected := strongly_connected wire hcover (by
      intro v w hvw
      obtain ⟨i, j, heq, _⟩ := hpair v w hvw
      exact ⟨i, j, heq⟩)
    have hsource : ∀ {a b : Event wire} (e : a ⟶ b),
        (delay wire sign e : ℝ) < original b - original a +
          (winding wire e : ℝ) * ((q : ℝ) + 1) / 2 := by
      intro a b e
      cases e with
      | adjacent v i => simpa only [delay, winding, Int.cast_ite, Int.cast_zero, Int.cast_one,
          zero_mul, zero_div, add_zero] using hadjacent v i
      | closing v => simpa only [delay, winding, Int.cast_ite, Int.cast_zero, Int.cast_one,
          one_mul] using hclosing v
    obtain ⟨time, htime⟩ := CyclicGraph.exists_half_grid_retiming
      (delay wire sign) (winding wire) q original (wire v₀ 0) hconnected
      (by
        intro a b e
        simpa only [Int.cast_natCast, mul_div_assoc] using hsource e) hcycles
    apply OddWire.exists_partial_rows_of_cyclic_schedules q hq time wire sign
    · intro v i
      have h := htime (Arc.adjacent v i)
      simpa only [delay, winding, mul_zero, add_zero, mul_ite, mul_one] using h
    · intro v
      have h := htime (Arc.closing v)
      simpa only [delay, winding, mul_one, mul_ite, mul_zero] using h
    · exact hpair

theorem card_le_small_period_of_simple_cycle_winding
    {V E : Type*} [Fintype V] {m : ℕ} (q : ℕ) (hq : q = 3 ∨ q = 5)
    (wire : V → Fin (m + 1) → E) (sign : V → E → Bool) (original : E → ℝ)
    (hcover : ∀ e : E, ∃ v i, wire v i = e)
    (hpair : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j ∧
      sign v (wire v i) ≠ sign w (wire w j))
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire v i.castSucc) = sign v (wire v i.succ) then (0 : ℝ) else 1) <
        original (wire v i.succ) - original (wire v i.castSucc))
    (hclosing : ∀ v,
      (if sign v (wire v (Fin.last m)) = sign v (wire v 0) then (1 : ℝ) else 0) <
        original (wire v 0) - original (wire v (Fin.last m)) + ((q : ℝ) + 1) / 2)
    (hcycles : ∀ (e : Event wire) (p : Quiver.Path (V := Event wire) e e),
      p.vertices.dropLast.Nodup → p.length ≠ 0 →
        CyclicGraph.pathWeight (winding wire) p = 1 ∨
        CyclicGraph.pathWeight (winding wire) p = 2) : Fintype.card V ≤ q := by
  obtain ⟨row, hvalid, hsep⟩ := exists_partial_rows_of_simple_cycle_winding q (by omega)
    wire sign original hcover hpair hadjacent hclosing hcycles
  exact OddWire.card_le_small_period_of_rows hq row hvalid hsep

end WireGraph

#print axioms OddWire.local_signed_gaps_of_doubled_delays
#print axioms WireGraph.card_le_small_period_of_simple_cycle_winding

end JSP000404Research
