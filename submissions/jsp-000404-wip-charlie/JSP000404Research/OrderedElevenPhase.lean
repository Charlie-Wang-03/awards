import JSP000404Research.ElevenPhaseSchedule
import JSP000404Research.OddWireSchedule
import JSP000404Research.OrderedDirectionWires

/-!
# Concrete ordered wires preserve the full eleven-phase interface

Monotone times on each sorted wire preserve its original direction comparisons. The
original middle-pair betweenness therefore survives integer retiming, as do all local
signed gaps. This proves the forty-wire bound for the concrete winding construction.
-/

namespace JSP000404Research.OrderedWires

open Quiver

variable {V : Type*} [LinearOrder V] [Fintype V] {width : ℝ}
variable (D : DirectionData V width)
variable (hinjective : ∀ v, Function.Injective (D.localDirectionValue v))
variable {m : ℕ} (hcard : Fintype.card V = m + 2)

theorem card_le_forty_of_doubled_schedule (H : PairEvent V → ℤ)
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire D hinjective hcard v i.castSucc) =
          sign v (wire D hinjective hcard v i.succ) then (0 : ℤ) else 2) ≤
        H (wire D hinjective hcard v i.succ) - H (wire D hinjective hcard v i.castSucc))
    (hclosing : ∀ v,
      (if sign v (wire D hinjective hcard v (Fin.last m)) =
          sign v (wire D hinjective hcard v 0) then (2 : ℤ) else 0) ≤
        H (wire D hinjective hcard v 0) - H (wire D hinjective hcard v (Fin.last m)) + 11) :
    Fintype.card V ≤ 40 := by
  classical
  have hmono (v : V) : Monotone (fun i ↦ H (wire D hinjective hcard v i)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have h := hadjacent v i
    split_ifs at h <;> omega
  let time (v w : V) : ℤ := if h : v = w then 0 else H (eventAt v ⟨w, Ne.symm h⟩)
  have htime {v w : V} (hvw : v ≠ w) : time v w = H (eventAt v ⟨w, hvw.symm⟩) := by
    simp only [time, dite_eq_right hvw]
  have hsymm (v w : V) : time v w = time w v := by
    by_cases hvw : v = w
    · subst w
      rfl
    · rw [htime hvw, htime (Ne.symm hvw), eventAt_swap hvw]
  have hlocal (v e f : V) (hve : v ≠ e) (hvf : v ≠ f) :
      |time v f - time v e| ≤ 11 ∧
        (decide (v < e) = decide (v < f) → |time v f - time v e| ≤ 9) ∧
        (decide (v < e) ≠ decide (v < f) → 2 ≤ |time v f - time v e|) := by
    obtain ⟨i, hi⟩ := (orderedRays D hinjective hcard v).1.surjective ⟨e, hve.symm⟩
    obtain ⟨j, hj⟩ := (orderedRays D hinjective hcard v).1.surjective ⟨f, hvf.symm⟩
    have h := OddWire.local_signed_gaps_of_doubled_delays
      (fun k ↦ H (wire D hinjective hcard v k))
      (fun k ↦ sign v (wire D hinjective hcard v k)) 11
      (hadjacent v) (hclosing v) i j
    norm_num only [wire, hi, hj, sign_eventAt, htime hve, htime hvf] at h ⊢
    exact h
  have hpreserve (v : V) (e f : OtherVertex v)
      (hle : D.localDirectionValue v e ≤ D.localDirectionValue v f) :
      time v e.1 ≤ time v f.1 := by
    obtain ⟨i, hi⟩ := (orderedRays D hinjective hcard v).1.surjective e
    obtain ⟨j, hj⟩ := (orderedRays D hinjective hcard v).1.surjective f
    have hvalues : value D (wire D hinjective hcard v i) ≤
        value D (wire D hinjective hcard v j) := by
      simpa only [wire, hi, hj, value_eventAt] using hle
    have hij := (value_wire_strictMono D hinjective hcard v).le_iff_le.mp hvalues
    simpa only [wire, hi, hj, htime e.2.symm, htime f.2.symm] using hmono v hij
  apply ElevenPhase.card_le_forty_of_ordered_times time hsymm
    (fun v e f he hf ↦ (hlocal v e f he hf).1)
    (fun v e f he hf ↦ (hlocal v e f he hf).2.1)
    (fun v e f he hf ↦ (hlocal v e f he hf).2.2)
  intro a b c hab hbc
  have hac := hab.trans hbc
  rcases D.between hab hbc with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · left
    constructor
    · apply hpreserve a ⟨b, hab.ne.symm⟩ ⟨c, hac.ne.symm⟩
      simpa [DirectionData.localDirectionValue, not_lt_of_ge hab.le,
        not_lt_of_ge hac.le] using hleft
    · have h := hpreserve c ⟨a, hac.ne⟩ ⟨b, hbc.ne⟩ (by
        simpa [DirectionData.localDirectionValue, hac, hbc] using hright)
      simpa only [hsymm c a, hsymm c b] using h
  · right
    constructor
    · have h := hpreserve c ⟨b, hbc.ne⟩ ⟨a, hac.ne⟩ (by
        simpa [DirectionData.localDirectionValue, hac, hbc] using hleft)
      simpa only [hsymm c a, hsymm c b] using h
    · apply hpreserve a ⟨c, hac.ne.symm⟩ ⟨b, hab.ne.symm⟩
      simpa [DirectionData.localDirectionValue, not_lt_of_ge hab.le,
        not_lt_of_ge hac.le] using hright

theorem card_le_forty_of_winding (hm : 0 < m) (hwidth : 0 < width) (hbound : width < 6)
    (hcycles : ∀ (e : WireGraph.Event (wire D hinjective hcard))
      (p : Quiver.Path (V := WireGraph.Event (wire D hinjective hcard)) e e),
      p.vertices.dropLast.Nodup → p.length ≠ 0 →
        CyclicGraph.pathWeight (WireGraph.winding (wire D hinjective hcard)) p = 1 ∨
        CyclicGraph.pathWeight (WireGraph.winding (wire D hinjective hcard)) p = 2) :
    Fintype.card V ≤ 40 := by
  have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v₀⟩ := hnonempty
  let original (e : PairEvent V) : ℝ := (6 / width) * value D e
  have hdelays := scaled_wire_delays D hinjective hcard hm hwidth hbound
  have hconnected := WireGraph.strongly_connected (wire D hinjective hcard)
    (wire_covers D hinjective hcard) (by
      intro v w hvw
      obtain ⟨i, j, heq, _⟩ := wire_pair D hinjective hcard v w hvw
      exact ⟨i, j, heq⟩)
  have hsource : ∀ {a b : WireGraph.Event (wire D hinjective hcard)} (e : a ⟶ b),
      (WireGraph.delay (wire D hinjective hcard) sign e : ℝ) < original b - original a +
        (WireGraph.winding (wire D hinjective hcard) e : ℝ) * ((11 : ℝ) + 1) / 2 := by
    intro a b e
    cases e with
    | adjacent v i =>
      simpa [WireGraph.delay, WireGraph.winding, original] using hdelays.1 v i
    | closing v =>
      convert hdelays.2 v using 1 <;> norm_num [WireGraph.delay, WireGraph.winding, original]
  obtain ⟨H, hH⟩ := CyclicGraph.exists_half_grid_retiming
    (WireGraph.delay (wire D hinjective hcard) sign)
    (WireGraph.winding (wire D hinjective hcard)) 11 original
    (wire D hinjective hcard v₀ 0) hconnected hsource hcycles
  apply card_le_forty_of_doubled_schedule D hinjective hcard H
  · intro v i
    have h := hH (WireGraph.Arc.adjacent v i)
    simpa only [WireGraph.delay, WireGraph.winding, mul_zero, add_zero, mul_ite, mul_one]
      using h
  · intro v
    have h := hH (WireGraph.Arc.closing v)
    simpa only [WireGraph.delay, WireGraph.winding, mul_one, mul_ite, mul_zero] using h

#print axioms card_le_forty_of_doubled_schedule
#print axioms card_le_forty_of_winding

end JSP000404Research.OrderedWires
