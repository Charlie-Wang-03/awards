import JSP000404Research.WireCurveTrace
import JSP000404Research.PeriodicCycleOrder

/-!
# Winding of embedded simple wire cycles

Half-open arrow intervals assign each point on a lifted walk to an arrow occurrence.
An embedding separates the source events of distinct overlapping arrow intervals. Simplicity
then forces a repeated projected point to come from the same occurrence. This supplies the
disjoint period pieces needed for the reflected-strip winding bound.
-/

namespace JSP000404Research

open Quiver

theorem simple_path_prefix_unique {V : Type*} [Quiver V] {a b c : V}
    (p : Quiver.Path a b) (hsimple : p.vertices.dropLast.Nodup)
    (left right : Quiver.Path a c) (tailLeft tailRight : Quiver.Path c b)
    (hleft : p = left.comp tailLeft) (hright : p = right.comp tailRight)
    (hltLeft : left.length < p.length) (hltRight : right.length < p.length) :
    left = right := by
  have hleftIndex : left.length < p.vertices.dropLast.length := by simpa using hltLeft
  have hrightIndex : right.length < p.vertices.dropLast.length := by simpa using hltRight
  have hleftVertex : p.vertices.dropLast[left.length] = c := by
    rw [List.getElem_dropLast]
    simp [hleft]
  have hrightVertex : p.vertices.dropLast[right.length] = c := by
    rw [List.getElem_dropLast]
    simp [hright]
  have hlength : left.length = right.length :=
    hsimple.getElem_inj_iff.mp (hleftVertex.trans hrightVertex.symm)
  exact ((Quiver.Path.comp_inj' hlength).mp (hleft.symm.trans hright)).1

namespace WireGraph
namespace CurveData

universe u v
variable {V : Type u} {E : Type v} {m : ℕ} {wire : V → Fin (m + 1) → E}
variable (D : CurveData wire)

/-- Projected half-open arrow intervals sharing a point have the same source event. -/
def SourceSeparated : Prop :=
  ∀ {a b c d : Event wire} (edge : a ⟶ b) (other : c ⟶ d) (k l : ℤ) (x : ℝ),
    D.time a + (k : ℝ) * D.period ≤ x →
    x < D.time b + ((k + arrowTurns wire edge : ℤ) : ℝ) * D.period →
    D.time c + (l : ℝ) * D.period ≤ x →
    x < D.time d + ((l + arrowTurns wire other : ℤ) : ℝ) * D.period →
    D.curve (centre wire edge) x = D.curve (centre wire other) x → a = c

theorem arrow_span_le_period {a b : Event wire} (edge : a ⟶ b) :
    D.time b + (arrowTurns wire edge : ℝ) * D.period ≤ D.time a + D.period := by
  cases edge with
  | adjacent v i =>
    simp only [arrowTurns, Nat.cast_zero, zero_mul, add_zero]
    linarith [D.time_nonneg (wire v i.castSucc), D.time_lt (wire v i.succ)]
  | closing v =>
    simp only [arrowTurns, Nat.cast_one, one_mul]
    have h := (D.ordered v).monotone (Fin.zero_le (Fin.last m))
    linarith

theorem antiperiodic_shift_cancel (v : V) (x : ℝ) (k : ℕ) :
    (-1 : ℝ) ^ k * D.curve v (x + (k : ℝ) * D.period) = D.curve v x := by
  have h := (D.antiperiodic v).add_nsmul_eq (x := x) k
  have hsquare : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [show D.curve v (x + (k : ℝ) * D.period) =
    (-1 : ℝ) ^ k * D.curve v x by simpa [nsmul_eq_mul, zsmul_eq_mul] using h]
  rw [← mul_assoc, hsquare, one_mul]

theorem trace_shift_injective (hseparated : D.SourceSeparated)
    {a b : Event wire} (p : Quiver.Path (V := Event wire) a b)
    (hsimple : p.vertices.dropLast.Nodup) (x y z : ℝ) (i j : ℕ)
    (hi : D.TraceAt p (x + (i : ℝ) * D.period) y)
    (hj : D.TraceAt p (x + (j : ℝ) * D.period) z)
    (hvalue : (-1 : ℝ) ^ i * y = (-1 : ℝ) ^ j * z) : i = j := by
  obtain ⟨c, d, before, edge, after, hp, hlo, hhi, hy⟩ := hi
  obtain ⟨c', d', before', edge', after', hp', hlo', hhi', hz⟩ := hj
  have hcurve : D.curve (centre wire edge) x = D.curve (centre wire edge') x := by
    rw [hy, hz, D.antiperiodic_shift_cancel, D.antiperiodic_shift_cancel] at hvalue
    exact hvalue
  have hsource : c = c' := by
    apply hseparated edge edge' (pathTurns wire before - i) (pathTurns wire before' - j) x
    · simp only [Int.cast_sub, Int.cast_natCast]
      dsimp only [endTime] at hlo
      linarith
    · simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
      simp only [endTime, pathTurns_cons, Nat.cast_add] at hhi
      nlinarith
    · simp only [Int.cast_sub, Int.cast_natCast]
      dsimp only [endTime] at hlo'
      linarith
    · simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
      simp only [endTime, pathTurns_cons, Nat.cast_add] at hhi'
      nlinarith
    · exact hcurve
  subst c'
  have hbefore : before = before' := by
    apply simple_path_prefix_unique p hsimple before before'
      (edge.toPath.comp after) (edge'.toPath.comp after') hp hp'
    · simp [hp]
    · simp [hp']
  subst before'
  have hspan := D.arrow_span_le_period edge
  have hspan' := D.arrow_span_le_period edge'
  simp only [endTime, pathTurns_cons, Nat.cast_add] at hlo hhi hlo' hhi'
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hreal : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    nlinarith [D.period_pos]
  · exact heq
  · have hreal : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
    nlinarith [D.period_pos]

include D in
theorem closed_path_turns_pos {a : Event wire} (p : Quiver.Path (V := Event wire) a a)
    (hpos : 0 < p.length) : 0 < pathTurns wire p := by
  have htime : D.time a < D.endTime p := by
    cases p with
    | nil => simp at hpos
    | cons before edge =>
      exact (D.time_le_endTime before).trans_lt (D.endTime_lt_cons before edge)
  by_contra h
  have hzero := Nat.eq_zero_of_not_pos h
  simp [endTime, hzero] at htime

/-- An embedded nonempty simple consecutive-wire cycle makes one or two turns. -/
theorem simple_cycle_turns_one_or_two (hseparated : D.SourceSeparated)
    {a : Event wire} (p : Quiver.Path (V := Event wire) a a)
    (hpos : 0 < p.length) (hsimple : p.vertices.dropLast.Nodup) :
    CyclicGraph.pathWeight (winding wire) p = 1 ∨
      CyclicGraph.pathWeight (winding wire) p = 2 := by
  have hturns := D.closed_path_turns_pos p hpos
  obtain ⟨trace, hcontinuous, hstart, hend, htrace⟩ := D.exists_trace p
  have hle : pathTurns wire p ≤ 2 := by
    apply winding_le_two_of_disjoint_period_pieces hturns D.period_pos trace hcontinuous
    · simpa [endTime, hstart] using hend
    · intro i j hne x hx heq
      have hmem (k : Fin (pathTurns wire p)) :
          x + (k.val : ℝ) * D.period ∈ Set.Ico (D.time a) (D.endTime p) := by
        have hk : (k.val : ℝ) + 1 ≤ pathTurns wire p := by exact_mod_cast k.isLt
        have hkzero : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
        dsimp only [endTime]
        constructor <;> nlinarith [hx.1, hx.2, D.period_pos]
      exact hne (Fin.ext (D.trace_shift_injective hseparated p hsimple x _ _ i.val j.val
        (htrace _ (hmem i)) (htrace _ (hmem j)) heq))
  rw [← pathTurns_cast]
  omega

#print axioms simple_cycle_turns_one_or_two

end CurveData
end WireGraph
end JSP000404Research
