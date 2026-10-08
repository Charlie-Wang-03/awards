import JSP000404Research.CyclicBandPhaseSlip
import Mathlib.Tactic

/-!
# Absence of cyclic floor-phase slips gives strict weighted capacity

A saturated centre necessarily has a paired cyclic coordinate
(natural floor of real gap, integer-band jump) = (0, 1).

Consequently, if a centre has no such phase slip, its local
standard-band budget improves from n+1 to n. When all centres
have no phase slips, the weighted Hansel capacity is at most 2^n.

Both implications are unconditional theorems *from their stated
hypotheses*. The absence of phase slips for arbitrary geometric
configurations is not asserted or assumed to have been proved.
-/

namespace JSP000404Research
namespace DirectionData
namespace LocalDirectionCycle

/-- No floor-zero/unit-band-jump phase slip at a centre leaves at
least one unit of strict local palette slack. -/
theorem exponent_add_incidentBands_card_le_n_of_no_phase_slip
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (hno : (0, 1) ∉ List.zip
      ((cyclicRealGapsAt t C.values).map Nat.floor)
      (cyclicBandJumps n (C.values.map Nat.floor))) :
    C.exponent + (D.incidentBands (n + 1) i).card ≤ n := by
  have hbound := C.exponent_add_incidentBands_card_le ht
  have hnotTight :
      C.exponent + (D.incidentBands (n + 1) i).card ≠ n + 1 := by
    intro htight
    exact hno (C.has_floor_zero_unit_band_jump_of_local_tight
      ht htight)
  omega

end LocalDirectionCycle

/-- A concrete all-centres no-phase-slip condition is sufficient
for the target weighted 2^n capacity. -/
theorem weighted_capacity_of_no_cyclic_phase_slips
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hno : ∀ i : V,
      (0, 1) ∉ List.zip
        ((cyclicRealGapsAt t (cycles i).values).map Nat.floor)
        (cyclicBandJumps n ((cycles i).values.map Nat.floor))) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  have hlocal : ∀ i : V,
      (cycles i).exponent +
        (D.incidentBands (n + 1) i).card ≤ n := by
    intro i
    exact (cycles i).exponent_add_incidentBands_card_le_n_of_no_phase_slip
      ht (hno i)
  exact weighted_capacity_of_strict_local_direction_cycles
    D ht cycles hlocal

#print axioms LocalDirectionCycle.exponent_add_incidentBands_card_le_n_of_no_phase_slip
#print axioms weighted_capacity_of_no_cyclic_phase_slips

end DirectionData
end JSP000404Research
