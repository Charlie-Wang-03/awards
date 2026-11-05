import JSP000404Research.CyclicWireGraph
import JSP000404Research.LocalDirectionValueCore
import Mathlib.Data.Fintype.Sort

/-!
# Consecutive wires of a strict local direction array

Events are increasing pairs of original vertices. Each centre orders its incident events by
their direction values. The resulting finite wire lists have shared events with opposite
movement signs. These definitions give the concrete graph for the remaining winding theorem.
-/

namespace JSP000404Research
namespace OrderedWires

variable {V : Type*} [LinearOrder V]

abbrev PairEvent (V : Type*) [LinearOrder V] := {p : V × V // p.1 < p.2}

def eventAt (v : V) (other : OtherVertex v) : PairEvent V :=
  if h : other.1 < v then ⟨(other.1, v), h⟩
  else ⟨(v, other.1), lt_of_le_of_ne (le_of_not_gt h) other.2.symm⟩

def sign (v : V) (e : PairEvent V) : Bool := decide (v = e.1.1)

def value {width : ℝ} (D : DirectionData V width) (e : PairEvent V) : ℝ :=
  D.value e.1.1 e.1.2

theorem value_eventAt {width : ℝ} (D : DirectionData V width) (v : V) (other : OtherVertex v) :
    value D (eventAt v other) = D.localDirectionValue v other := by
  simp only [value, eventAt, DirectionData.localDirectionValue]
  split_ifs <;> rfl

theorem sign_eventAt (v : V) (other : OtherVertex v) :
    sign v (eventAt v other) = decide (v < other.1) := by
  by_cases h : other.1 < v
  · simp [eventAt, sign, h, ne_of_gt h, not_lt_of_ge h.le]
  · have hv : v < other.1 := lt_of_le_of_ne (le_of_not_gt h) other.2.symm
    simp [eventAt, sign, h, hv]

theorem eventAt_swap {v w : V} (hvw : v ≠ w) :
    eventAt v ⟨w, hvw.symm⟩ = eventAt w ⟨v, hvw⟩ := by
  rcases lt_or_gt_of_ne hvw with h | h
  · simp [eventAt, h, not_lt_of_ge h.le]
  · simp [eventAt, h, not_lt_of_ge h.le]

theorem opposite_signs {v w : V} (hvw : v ≠ w) :
    sign v (eventAt v ⟨w, hvw.symm⟩) ≠ sign w (eventAt w ⟨v, hvw⟩) := by
  rw [sign_eventAt, sign_eventAt]
  rcases lt_or_gt_of_ne hvw with h | h <;> simp [h, not_lt_of_ge h.le]

theorem different_sign_local_gap {width : ℝ} (D : DirectionData V width)
    (v : V) (a b : OtherVertex v)
    (hsign : sign v (eventAt v a) ≠ sign v (eventAt v b)) :
    1 ≤ |D.localDirectionValue v a - D.localDirectionValue v b| := by
  rw [sign_eventAt, sign_eventAt] at hsign
  by_cases hav : a.1 < v <;> by_cases hbv : b.1 < v
  · simp [not_lt_of_ge hav.le, not_lt_of_ge hbv.le] at hsign
  · have hvb : v < b.1 := lt_of_le_of_ne (le_of_not_gt hbv) b.2.symm
    simpa [DirectionData.localDirectionValue, hav, hbv] using D.middleSeparated hav hvb
  · have hva : v < a.1 := lt_of_le_of_ne (le_of_not_gt hav) a.2.symm
    have h := D.middleSeparated hbv hva
    simpa [DirectionData.localDirectionValue, hav, hbv, abs_sub_comm] using h
  · have hva : v < a.1 := lt_of_le_of_ne (le_of_not_gt hav) a.2.symm
    have hvb : v < b.1 := lt_of_le_of_ne (le_of_not_gt hbv) b.2.symm
    simp [hva, hvb] at hsign

theorem same_sign_local_gap {width : ℝ} (D : DirectionData V width)
    (v : V) (a b : OtherVertex v) (hne : a ≠ b)
    (hsign : sign v (eventAt v a) = sign v (eventAt v b)) :
    |D.localDirectionValue v a - D.localDirectionValue v b| ≤ width - 1 := by
  have hab : a.1 ≠ b.1 := fun h ↦ hne (Subtype.ext h)
  rw [sign_eventAt, sign_eventAt] at hsign
  by_cases hav : a.1 < v <;> by_cases hbv : b.1 < v
  · rcases lt_or_gt_of_ne hab with hab | hba
    · simpa [DirectionData.localDirectionValue, hav, hbv] using D.lastGap hab hbv
    · simpa [DirectionData.localDirectionValue, hav, hbv, abs_sub_comm] using D.lastGap hba hav
  · have hvb : v < b.1 := lt_of_le_of_ne (le_of_not_gt hbv) b.2.symm
    simp [not_lt_of_ge hav.le, hvb] at hsign
  · have hva : v < a.1 := lt_of_le_of_ne (le_of_not_gt hav) a.2.symm
    simp [hva, not_lt_of_ge hbv.le] at hsign
  · have hva : v < a.1 := lt_of_le_of_ne (le_of_not_gt hav) a.2.symm
    have hvb : v < b.1 := lt_of_le_of_ne (le_of_not_gt hbv) b.2.symm
    rcases lt_or_gt_of_ne hab with hab | hba
    · simpa [DirectionData.localDirectionValue, hav, hbv] using D.firstGap hva hab
    · simpa [DirectionData.localDirectionValue, hav, hbv, abs_sub_comm] using D.firstGap hvb hba

section Enumeration

variable [Fintype V] {width : ℝ} (D : DirectionData V width)
variable (hinjective : ∀ v, Function.Injective (D.localDirectionValue v))
variable {m : ℕ} (hcard : Fintype.card V = m + 2)

/-- Increasing enumeration of the incident rays, retaining its strict value order. -/
noncomputable def orderedRays (v : V) :
    {rays : Fin (m + 1) ≃ OtherVertex v //
      StrictMono (fun i ↦ D.localDirectionValue v (rays i))} := by
  classical
  let otherOrder : LinearOrder (OtherVertex v) :=
    LinearOrder.lift' (D.localDirectionValue v) (hinjective v)
  letI := otherOrder
  have hother : Fintype.card (OtherVertex v) = m + 1 := by
    change Fintype.card {j : V // j ≠ v} = m + 1
    rw [Fintype.card_subtype_compl (fun j : V ↦ j = v), Fintype.card_subtype_eq, hcard]
    omega
  let order := monoEquivOfFin (OtherVertex v) hother
  refine ⟨order.toEquiv, ?_⟩
  intro i j hij
  exact @OrderIso.strictMono (Fin (m + 1)) (OtherVertex v) _ otherOrder.toPreorder order i j hij

noncomputable def wire (v : V) (i : Fin (m + 1)) : PairEvent V :=
  eventAt v ((orderedRays D hinjective hcard v).1 i)

theorem value_wire_strictMono (v : V) :
    StrictMono (fun i ↦ value D (wire D hinjective hcard v i)) := by
  simpa only [wire, value_eventAt] using (orderedRays D hinjective hcard v).2

theorem wire_covers (e : PairEvent V) : ∃ v i, wire D hinjective hcard v i = e := by
  let other : OtherVertex e.1.1 := ⟨e.1.2, ne_of_gt e.2⟩
  obtain ⟨i, hi⟩ := (orderedRays D hinjective hcard e.1.1).1.surjective other
  refine ⟨e.1.1, i, ?_⟩
  simp only [wire, hi]
  apply Subtype.ext
  simp [eventAt, other, not_lt_of_ge e.2.le]

theorem wire_pair (v w : V) (hvw : v ≠ w) :
    ∃ i j, wire D hinjective hcard v i = wire D hinjective hcard w j ∧
      sign v (wire D hinjective hcard v i) ≠ sign w (wire D hinjective hcard w j) := by
  obtain ⟨i, hi⟩ := (orderedRays D hinjective hcard v).1.surjective ⟨w, hvw.symm⟩
  obtain ⟨j, hj⟩ := (orderedRays D hinjective hcard w).1.surjective ⟨v, hvw⟩
  refine ⟨i, j, ?_, ?_⟩
  · simpa only [wire, hi, hj] using eventAt_swap hvw
  · simpa only [wire, hi, hj] using opposite_signs hvw

/-- Scaling a narrower strict local array supplies the consecutive strict source delays. -/
theorem scaled_wire_delays (hm : 0 < m) (hwidth : 0 < width) {target : ℝ}
    (htarget : width < target) :
    let scale := target / width
    (∀ v (i : Fin m),
      (if sign v (wire D hinjective hcard v i.castSucc) =
          sign v (wire D hinjective hcard v i.succ) then (0 : ℝ) else 1) <
        scale * value D (wire D hinjective hcard v i.succ) -
          scale * value D (wire D hinjective hcard v i.castSucc)) ∧
    (∀ v,
      (if sign v (wire D hinjective hcard v (Fin.last m)) =
          sign v (wire D hinjective hcard v 0) then (1 : ℝ) else 0) <
        scale * value D (wire D hinjective hcard v 0) -
          scale * value D (wire D hinjective hcard v (Fin.last m)) + target) := by
  dsimp only
  let scale := target / width
  have hscale : 1 < scale := (one_lt_div hwidth).mpr htarget
  have hpos : 0 < scale := lt_trans zero_lt_one hscale
  have htotal : scale * width = target := by
    dsimp [scale]
    field_simp
  constructor
  · intro v i
    have hlt := value_wire_strictMono D hinjective hcard v i.castSucc_lt_succ
    by_cases hsign : sign v (wire D hinjective hcard v i.castSucc) =
        sign v (wire D hinjective hcard v i.succ)
    · rw [ite_eq_left hsign]
      have h := mul_pos hpos (sub_pos.mpr hlt)
      change 0 < scale * _ - scale * _
      nlinarith
    · rw [ite_eq_right hsign]
      have hgap : 1 ≤ |value D (wire D hinjective hcard v i.castSucc) -
          value D (wire D hinjective hcard v i.succ)| := by
        simpa only [wire, value_eventAt] using different_sign_local_gap D v
          ((orderedRays D hinjective hcard v).1 i.castSucc)
          ((orderedRays D hinjective hcard v).1 i.succ) hsign
      rw [abs_of_nonpos (sub_nonpos.mpr hlt.le)] at hgap
      have hprod := mul_le_mul_of_nonneg_left hgap hpos.le
      change 1 < scale * _ - scale * _
      nlinarith
  · intro v
    have hindex : (0 : Fin (m + 1)) < Fin.last m := by
      change 0 < m
      exact hm
    have hlt := value_wire_strictMono D hinjective hcard v hindex
    by_cases hsign : sign v (wire D hinjective hcard v (Fin.last m)) =
        sign v (wire D hinjective hcard v 0)
    · rw [ite_eq_left hsign]
      have hne : (orderedRays D hinjective hcard v).1 (Fin.last m) ≠
          (orderedRays D hinjective hcard v).1 0 := by
        exact (orderedRays D hinjective hcard v).1.injective.ne (ne_of_gt hindex)
      have hgap : |value D (wire D hinjective hcard v (Fin.last m)) -
          value D (wire D hinjective hcard v 0)| ≤ width - 1 := by
        simpa only [wire, value_eventAt] using same_sign_local_gap D v
          ((orderedRays D hinjective hcard v).1 (Fin.last m))
          ((orderedRays D hinjective hcard v).1 0) hne hsign
      rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hgap
      have hprod := mul_le_mul_of_nonneg_left hgap hpos.le
      change 1 < scale * _ - scale * _ + target
      nlinarith
    · rw [ite_eq_right hsign]
      have hfirst := D.nonnegative (wire D hinjective hcard v 0).2
      have hlast := D.belowWidth (wire D hinjective hcard v (Fin.last m)).2
      change 0 ≤ value D (wire D hinjective hcard v 0) at hfirst
      change value D (wire D hinjective hcard v (Fin.last m)) < width at hlast
      have hgap : 0 < width + value D (wire D hinjective hcard v 0) -
          value D (wire D hinjective hcard v (Fin.last m)) := by linarith
      have hprod := mul_pos hpos hgap
      change 0 < scale * _ - scale * _ + target
      nlinarith

/-- The concrete ordered-direction reduction retains only its simple-cycle winding premise. -/
theorem card_le_two_pow_of_winding (hm : 0 < m) (hwidth : 0 < width)
    (n : ℕ) (hn : 0 < n) (hbound : width < (n : ℝ) + 1 / 2)
    (hcycles : ∀ (e : WireGraph.Event (wire D hinjective hcard))
      (p : Quiver.Path (V := WireGraph.Event (wire D hinjective hcard)) e e),
      p.vertices.dropLast.Nodup → p.length ≠ 0 →
        CyclicGraph.pathWeight (WireGraph.winding (wire D hinjective hcard)) p = 1 ∨
        CyclicGraph.pathWeight (WireGraph.winding (wire D hinjective hcard)) p = 2) :
    Fintype.card V ≤ 2 ^ n := by
  have hdelays := scaled_wire_delays D hinjective hcard hm hwidth hbound
  exact WireGraph.card_le_two_pow_of_simple_cycle_winding n hn (wire D hinjective hcard) sign
    (fun e ↦ (((n : ℝ) + 1 / 2) / width) * value D e)
    (wire_covers D hinjective hcard) (wire_pair D hinjective hcard)
    hdelays.1 hdelays.2 hcycles

end Enumeration

#print axioms different_sign_local_gap
#print axioms same_sign_local_gap
#print axioms value_wire_strictMono
#print axioms wire_covers
#print axioms wire_pair
#print axioms scaled_wire_delays
#print axioms card_le_two_pow_of_winding

end OrderedWires
end JSP000404Research
