import JSP000404Research.CyclicWireGraph
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Topology.ContinuousOn

/-!
# Continuous lifted traces of consecutive-wire walks

The geometric data supply continuous antiperiodic wire graphs agreeing at every event.
Following a directed quiver walk gives a continuous lifted graph. Its provenance records
the actual arrow occurrence followed at each point, for use in the simple-cycle embedding
argument. No disjointness conclusion is assumed or asserted in this module.
-/

namespace JSP000404Research
namespace WireGraph

open Quiver

universe u v
variable {V : Type u} {E : Type v} {m : ℕ} (wire : V → Fin (m + 1) → E)

def centre : ∀ {a b : Event wire}, (a ⟶ b) → V
  | _, _, .adjacent v _ => v
  | _, _, .closing v => v

def arrowTurns : ∀ {a b : Event wire}, (a ⟶ b) → ℕ
  | _, _, .adjacent _ _ => 0
  | _, _, .closing _ => 1

def pathTurns {a b : Event wire} (p : Quiver.Path (V := Event wire) a b) : ℕ :=
  Quiver.Path.addWeight (arrowTurns wire) p

@[simp] theorem pathTurns_nil (a : Event wire) :
    pathTurns wire (.nil : Quiver.Path (V := Event wire) a a) = 0 := by
  simp [pathTurns]

@[simp] theorem pathTurns_cons {a b c : Event wire}
    (p : Quiver.Path (V := Event wire) a b) (e : b ⟶ c) :
    pathTurns wire (p.cons e) = pathTurns wire p + arrowTurns wire e := by
  simp [pathTurns]

theorem pathTurns_cast {a b : Event wire} (p : Quiver.Path (V := Event wire) a b) :
    (pathTurns wire p : ℤ) = CyclicGraph.pathWeight (winding wire) p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [pathTurns_cons, Nat.cast_add, CyclicGraph.pathWeight_cons, ih]
    congr 1
    cases e <;> rfl

/-- Continuous wire curves with their event times and reflected period. -/
structure CurveData where
  period : ℝ
  period_pos : 0 < period
  time : E → ℝ
  time_nonneg : ∀ e, 0 ≤ time e
  time_lt : ∀ e, time e < period
  ordered : ∀ v, StrictMono (fun i ↦ time (wire v i))
  height : E → ℝ
  curve : V → ℝ → ℝ
  continuous : ∀ v, Continuous (curve v)
  antiperiodic : ∀ v, Function.Antiperiodic (curve v) period
  at_event : ∀ v i, curve v (time (wire v i)) = height (wire v i)

namespace CurveData

variable {wire} (D : CurveData wire)

theorem event_shift (v : V) (i : Fin (m + 1)) (k : ℕ) :
    D.curve v (D.time (wire v i) + (k : ℝ) * D.period) =
      (-1 : ℝ) ^ k * D.height (wire v i) := by
  have h := (D.antiperiodic v).add_nsmul_eq (x := D.time (wire v i)) k
  simpa [nsmul_eq_mul, zsmul_eq_mul, D.at_event] using h

theorem arrow_source_shift {a b : Event wire} (e : a ⟶ b) (k : ℕ) :
    D.curve (centre wire e) (D.time a + (k : ℝ) * D.period) =
      (-1 : ℝ) ^ k * D.height a := by
  cases e <;> exact D.event_shift _ _ k

theorem arrow_target_shift {a b : Event wire} (e : a ⟶ b) (k : ℕ) :
    D.curve (centre wire e) (D.time b + (k : ℝ) * D.period) =
      (-1 : ℝ) ^ k * D.height b := by
  cases e <;> exact D.event_shift _ _ k

theorem arrow_time_lt {a b : Event wire} (e : a ⟶ b) :
    D.time a < D.time b + (arrowTurns wire e : ℝ) * D.period := by
  cases e with
  | adjacent v i => simpa [arrowTurns] using D.ordered v i.castSucc_lt_succ
  | closing v =>
    simp only [arrowTurns, Nat.cast_one, one_mul]
    linarith [D.time_nonneg (wire v 0), D.time_lt (wire v (Fin.last m))]

def endTime {a b : Event wire} (p : Quiver.Path (V := Event wire) a b) : ℝ :=
  D.time b + (pathTurns wire p : ℝ) * D.period

theorem time_le_endTime {a b : Event wire} (p : Quiver.Path (V := Event wire) a b) :
    D.time a ≤ D.endTime p := by
  induction p with
  | nil => simp [endTime]
  | cons p e ih =>
    have h := D.arrow_time_lt e
    simp only [endTime, pathTurns_cons, Nat.cast_add] at ih ⊢
    nlinarith

theorem endTime_lt_cons {a b c : Event wire} (p : Quiver.Path (V := Event wire) a b)
    (e : b ⟶ c) : D.endTime p < D.endTime (p.cons e) := by
  have h := D.arrow_time_lt e
  simp only [endTime, pathTurns_cons, Nat.cast_add]
  nlinarith

/-- A trace point lies on a half-open arrow occurrence of the walk. -/
def TraceAt {a b : Event wire} (p : Quiver.Path (V := Event wire) a b) (x y : ℝ) : Prop :=
  ∃ (c d : Event wire) (before : Quiver.Path (V := Event wire) a c) (edge : c ⟶ d)
    (after : Quiver.Path (V := Event wire) d b),
    p = before.comp (edge.toPath.comp after) ∧
    D.endTime before ≤ x ∧ x < D.endTime (before.cons edge) ∧
    y = D.curve (centre wire edge) x

/-- Pasting the actual wire graphs produces a continuous lifted walk with point provenance. -/
theorem exists_trace {a b : Event wire} (p : Quiver.Path (V := Event wire) a b) :
    ∃ trace : ℝ → ℝ,
      ContinuousOn trace (Set.Icc (D.time a) (D.endTime p)) ∧
      trace (D.time a) = D.height a ∧
      trace (D.endTime p) = (-1 : ℝ) ^ pathTurns wire p * D.height b ∧
      ∀ x ∈ Set.Ico (D.time a) (D.endTime p), D.TraceAt p x (trace x) := by
  classical
  induction p with
  | nil =>
    refine ⟨fun _ ↦ D.height a, continuous_const.continuousOn, rfl, ?_, ?_⟩
    · simp
    · simp [endTime]
  | @cons b c p edge ih =>
    obtain ⟨previous, hcontinuous, hstart, hend, htrace⟩ := ih
    let joined (x : ℝ) := if x ≤ D.endTime p then previous x else D.curve (centre wire edge) x
    have hstart_le := D.time_le_endTime p
    have hfinish := D.endTime_lt_cons p edge
    have hmatch : previous (D.endTime p) = D.curve (centre wire edge) (D.endTime p) := by
      rw [hend]
      exact (D.arrow_source_shift edge (pathTurns wire p)).symm
    have hleft : ContinuousOn joined (Set.Icc (D.time a) (D.endTime p)) := by
      apply hcontinuous.congr
      intro x hx
      simp [joined, hx.2]
    have hright : ContinuousOn joined (Set.Icc (D.endTime p) (D.endTime (p.cons edge))) := by
      apply (D.continuous (centre wire edge)).continuousOn.congr
      intro x hx
      by_cases heq : x = D.endTime p
      · subst x
        simp [joined, hmatch]
      · have hlt : D.endTime p < x := lt_of_le_of_ne hx.1 (Ne.symm heq)
        simp [joined, not_le_of_gt hlt]
    refine ⟨joined, ?_, ?_, ?_, ?_⟩
    · have h := hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc
      rw [Set.Icc_union_Icc_eq_Icc hstart_le hfinish.le] at h
      exact h
    · simpa [joined, hstart_le] using hstart
    · simp only [joined, ite_eq_right (not_le_of_gt hfinish)]
      exact D.arrow_target_shift edge (pathTurns wire (p.cons edge))
    · intro x hx
      by_cases hleft : x < D.endTime p
      · have hold := htrace x ⟨hx.1, hleft⟩
        simp only [joined, ite_eq_left hleft.le]
        rcases hold with ⟨u, v, before, step, after, heq, hlo, hhi, hvalue⟩
        refine ⟨u, v, before, step, after.cons edge, ?_, hlo, hhi, hvalue⟩
        simp [heq]
      · refine ⟨b, c, p, edge, .nil, ?_, le_of_not_gt hleft, hx.2, ?_⟩
        · simp
        · by_cases heq : x = D.endTime p
          · subst x
            simpa [joined] using hmatch
          · have hlt : D.endTime p < x := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm heq)
            simp [joined, not_le_of_gt hlt]

#print axioms exists_trace

end CurveData
end WireGraph
end JSP000404Research
