import JSP000404Research.OrderedDirectionWires
import JSP000404Research.ProjectionWireCurves
import JSP000404Research.WireCurveEmbedding

/-!
# Geometric curves for the ordered-direction wire graph

A forward polar lift realizes the sorted pair-event graph by rotating projections. Its
complete pair-crossing data discharge the simple-cycle winding premise in the integral
retiming capacity theorem.
-/

namespace JSP000404Research
namespace OrderedWires

variable {V : Type*} [LinearOrder V] [Fintype V]
variable {width : ℝ} (D : DirectionData V width)
variable (hinjective : ∀ v, Function.Injective (D.localDirectionValue v))
variable {m : ℕ} (hcard : Fintype.card V = m + 2)
variable {p : V → Plane} {base lam : ℝ} (F : ForwardAngleLift p base)
variable (hwidth : 0 < width) (hlam : 0 < lam) (hscale : lam * width = Real.pi)
variable (hvalue : ∀ i j, D.value i j = (F.theta i j - base) / lam)

noncomputable def forwardCurveData : WireGraph.CurveData (wire D hinjective hcard) where
  period := width
  period_pos := hwidth
  time := value D
  time_nonneg := fun e ↦ D.nonnegative e.2
  time_lt := fun e ↦ D.belowWidth e.2
  ordered := value_wire_strictMono D hinjective hcard
  height := fun e ↦ projectionWireCurve base lam (p e.1.1) (value D e)
  curve := fun v ↦ projectionWireCurve base lam (p v)
  continuous := fun v ↦ projectionWireCurve_continuous base lam (p v)
  antiperiodic := fun v ↦ projectionWireCurve_antiperiodic base lam width (p v) hscale
  at_event := by
    intro v i
    let other := (orderedRays D hinjective hcard v).1 i
    change projectionWireCurve base lam (p v) (value D (eventAt v other)) =
      projectionWireCurve base lam (p (eventAt v other).1.1) (value D (eventAt v other))
    by_cases h : other.1 < v
    · simpa [eventAt, h, value, hvalue] using
        (F.projectionWireCurve_at_event h (ne_of_gt hlam)).symm
    · simp [eventAt, h]

omit [Fintype V] in
include F hlam hscale hvalue in
theorem crossing_at_eventAt (v w : V) (hvw : v ≠ w) (time : ℝ)
    (hcross : projectionWireCurve base lam (p v) time =
      projectionWireCurve base lam (p w) time) :
    ∃ k : ℤ, time = value D (eventAt v ⟨w, hvw.symm⟩) + (k : ℝ) * width := by
  by_cases h : w < v
  · simpa [eventAt, h, value, hvalue] using
      F.projectionWireCurve_crossing h hlam hscale time hcross.symm
  · have hlt : v < w := lt_of_le_of_ne (le_of_not_gt h) hvw
    simpa [eventAt, h, value, hvalue] using
      F.projectionWireCurve_crossing hlt hlam hscale time hcross

theorem forwardCurveData_crossingsComplete :
    (forwardCurveData D hinjective hcard F hwidth hlam hscale hvalue).CrossingsComplete := by
  intro v w hvw time hcross
  obtain ⟨i, hi⟩ := (orderedRays D hinjective hcard v).1.surjective ⟨w, hvw.symm⟩
  obtain ⟨j, hj⟩ := (orderedRays D hinjective hcard w).1.surjective ⟨v, hvw⟩
  obtain ⟨k, hk⟩ := crossing_at_eventAt D F hlam hscale hvalue v w hvw time hcross
  refine ⟨i, j, k, ?_, ?_⟩
  · simpa only [wire, hi, hj] using eventAt_swap hvw
  · change time = value D (wire D hinjective hcard v i) + (k : ℝ) * width
    simpa only [wire, hi] using hk

include F hwidth hlam hscale hvalue in
theorem simple_cycle_winding_of_forward_lift
    (e : WireGraph.Event (wire D hinjective hcard))
    (path : Quiver.Path (V := WireGraph.Event (wire D hinjective hcard)) e e)
    (hsimple : path.vertices.dropLast.Nodup) (hpos : path.length ≠ 0) :
    CyclicGraph.pathWeight (WireGraph.winding (wire D hinjective hcard)) path = 1 ∨
      CyclicGraph.pathWeight (WireGraph.winding (wire D hinjective hcard)) path = 2 :=
  WireGraph.CurveData.simple_cycle_winding_of_crossingsComplete
    (forwardCurveData D hinjective hcard F hwidth hlam hscale hvalue)
    (forwardCurveData_crossingsComplete D hinjective hcard F hwidth hlam hscale hvalue)
    path (Nat.pos_of_ne_zero hpos) hsimple

include D hinjective hcard F hwidth hlam hscale hvalue in
/-- The first capacity family for a genuine forward polar lift. -/
theorem card_le_two_pow_of_forward_lift (hm : 0 < m) (n : ℕ) (hn : 0 < n)
    (hbound : width < (n : ℝ) + 1 / 2) : Fintype.card V ≤ 2 ^ n := by
  exact card_le_two_pow_of_winding D hinjective hcard hm hwidth n hn hbound
    (simple_cycle_winding_of_forward_lift D hinjective hcard F hwidth hlam hscale hvalue)

#print axioms forwardCurveData_crossingsComplete
#print axioms simple_cycle_winding_of_forward_lift
#print axioms card_le_two_pow_of_forward_lift

end OrderedWires
end JSP000404Research
