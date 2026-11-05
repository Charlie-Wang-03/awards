import JSP000404Research.SimpleWireCycle

/-!
# Embedding from complete pair-crossing data

Strictly ordered event times partition every wire into half-open cyclic intervals. If every
intersection of distinct wire curves is one of their shared events, overlapping projected
arrow intervals have the same source. The simple-cycle winding theorem then applies.
-/

namespace JSP000404Research
namespace WireGraph
namespace CurveData

open Quiver

universe u v
variable {V : Type u} {E : Type v} {m : ℕ} {wire : V → Fin (m + 1) → E}
variable (D : CurveData wire)

/-- Every intersection of distinct curves occurs at a shared event, modulo the period. -/
def CrossingsComplete : Prop :=
  ∀ (v w : V), v ≠ w → ∀ x, D.curve v x = D.curve w x →
    ∃ (i j : Fin (m + 1)) (k : ℤ),
      wire v i = wire w j ∧ x = D.time (wire v i) + (k : ℝ) * D.period

theorem event_shift_strict (a b : E) {k l : ℤ} (hkl : k < l) :
    D.time a + (k : ℝ) * D.period < D.time b + (l : ℝ) * D.period := by
  have hreal : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  nlinarith [D.time_lt a, D.time_nonneg b, D.period_pos]

theorem event_in_arrow_interval {a b : Event wire} (edge : a ⟶ b)
    (i : Fin (m + 1)) (k l : ℤ)
    (hlo : D.time a + (k : ℝ) * D.period ≤
      D.time (wire (centre wire edge) i) + (l : ℝ) * D.period)
    (hhi : D.time (wire (centre wire edge) i) + (l : ℝ) * D.period <
      D.time b + ((k + arrowTurns wire edge : ℤ) : ℝ) * D.period) :
    wire (centre wire edge) i = a := by
  cases edge with
  | adjacent v j =>
    simp only [centre, arrowTurns, Nat.cast_zero, add_zero] at hlo hhi ⊢
    have hshift : k = l := by
      rcases lt_trichotomy k l with hlt | heq | hgt
      · have h := D.event_shift_strict (wire v j.succ) (wire v i) hlt
        linarith
      · exact heq
      · have h := D.event_shift_strict (wire v i) (wire v j.castSucc) hgt
        linarith
    subst l
    have hloIndex : j.castSucc ≤ i := (D.ordered v).le_iff_le.mp (by linarith)
    have hhiIndex : i < j.succ := (D.ordered v).lt_iff_lt.mp (by linarith)
    have hi : i = j.castSucc := by
      apply Fin.ext
      change j.val ≤ i.val at hloIndex
      change i.val < j.val + 1 at hhiIndex
      dsimp only [Fin.val_castSucc]
      omega
    rw [hi]
  | closing v =>
    simp only [centre, arrowTurns, Nat.cast_one] at hlo hhi ⊢
    have hshift : k = l := by
      rcases lt_trichotomy k l with hlt | heq | hgt
      · have hle : k + 1 ≤ l := by omega
        rcases hle.eq_or_lt with heq | hlt'
        · have hfirst := (D.ordered v).monotone (Fin.zero_le i)
          rw [← heq] at hhi
          linarith
        · have h := D.event_shift_strict (wire v 0) (wire v i) hlt'
          linarith
      · exact heq
      · have h := D.event_shift_strict (wire v i) (wire v (Fin.last m)) hgt
        linarith
    subst l
    have hlast : Fin.last m ≤ i := (D.ordered v).le_iff_le.mp (by linarith)
    have hi := le_antisymm (Fin.le_last i) hlast
    rw [hi]

theorem source_on_wire {a b : Event wire} (edge : a ⟶ b) :
    ∃ i, wire (centre wire edge) i = a := by
  cases edge with
  | adjacent v i => exact ⟨i.castSucc, rfl⟩
  | closing v => exact ⟨Fin.last m, rfl⟩

theorem sourceSeparated_of_crossingsComplete (hcross : D.CrossingsComplete) :
    D.SourceSeparated := by
  intro a b c d edge other k l x hlo hhi hlo' hhi' hcurve
  by_cases hcentre : centre wire edge = centre wire other
  · obtain ⟨i, hi⟩ := source_on_wire edge
    obtain ⟨j, hj⟩ := source_on_wire other
    by_cases horder : D.time a + (k : ℝ) * D.period ≤ D.time c + (l : ℝ) * D.period
    · have hlow : D.time a + (k : ℝ) * D.period ≤
          D.time (wire (centre wire edge) j) + (l : ℝ) * D.period := by
        simpa [hcentre, hj] using horder
      have hhigh : D.time (wire (centre wire edge) j) + (l : ℝ) * D.period <
          D.time b + ((k + arrowTurns wire edge : ℤ) : ℝ) * D.period := by
        simpa [hcentre, hj] using hlo'.trans_lt hhi
      exact (show @Eq E a c by
        simpa [hcentre, hj] using (D.event_in_arrow_interval edge j k l hlow hhigh).symm)
    · have hlow : D.time c + (l : ℝ) * D.period ≤
          D.time (wire (centre wire other) i) + (k : ℝ) * D.period := by
        simpa [← hcentre, hi] using (lt_of_not_ge horder).le
      have hhigh : D.time (wire (centre wire other) i) + (k : ℝ) * D.period <
          D.time d + ((l + arrowTurns wire other : ℤ) : ℝ) * D.period := by
        simpa [← hcentre, hi] using hlo.trans_lt hhi'
      exact (show @Eq E a c by
        simpa [← hcentre, hi] using D.event_in_arrow_interval other i l k hlow hhigh)
  · obtain ⟨i, j, hevent, hphase, hx⟩ :=
      hcross (centre wire edge) (centre wire other) hcentre x hcurve
    have hfirst := D.event_in_arrow_interval edge i k hevent
      (by simpa [← hx] using hlo) (by simpa [← hx] using hhi)
    have hsecond := D.event_in_arrow_interval other j l hevent
      (by simpa [← hphase, ← hx] using hlo') (by simpa [← hphase, ← hx] using hhi')
    exact hfirst.symm.trans (hphase.trans hsecond)

theorem simple_cycle_winding_of_crossingsComplete (hcross : D.CrossingsComplete)
    {a : Event wire} (p : Quiver.Path (V := Event wire) a a)
    (hpos : 0 < p.length) (hsimple : p.vertices.dropLast.Nodup) :
    CyclicGraph.pathWeight (winding wire) p = 1 ∨
      CyclicGraph.pathWeight (winding wire) p = 2 :=
  D.simple_cycle_turns_one_or_two (D.sourceSeparated_of_crossingsComplete hcross) p hpos hsimple

#print axioms sourceSeparated_of_crossingsComplete
#print axioms simple_cycle_winding_of_crossingsComplete

end CurveData
end WireGraph
end JSP000404Research
