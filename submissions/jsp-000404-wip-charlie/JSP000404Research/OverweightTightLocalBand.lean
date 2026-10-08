import JSP000404Research.StrictCyclicBandSlack
import Mathlib.Tactic

/-!
# Necessary local saturation in any hypothetical overweight configuration

For a standard direction colouring, every local cycle has
  exponent(i) + incidentBands(i).card <= n+1.

The Hansel strict-deficit criterion shows that a hypothetical configuration
whose total dyadic centre weight exceeds 2^n must contain at least one
centre where the local n+1 budget is exactly saturated. In particular it
cannot have a strict cyclic floor-vs-band-jump exponent inequality at
every centre.

These are obstruction theorems, not a general proof that no overweight
configuration exists.
-/

namespace JSP000404Research
namespace DirectionData

open scoped BigOperators

/-- Every hypothetical violation of the 2^n weighted capacity has an
actual centre saturating the full n+1 local band budget. -/
theorem overweight_exists_tight_local_band_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    ∃ i : V,
      (cycles i).exponent +
        (D.incidentBands (n + 1) i).card = n + 1 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hlocal : ∀ i : V,
      (cycles i).exponent +
        (D.incidentBands (n + 1) i).card ≤ n := by
    intro i
    have hbound :=
      (cycles i).exponent_add_incidentBands_card_le ht
    have hne := hnone i
    omega
  have hbound :=
    weighted_capacity_of_strict_local_direction_cycles
      D ht cycles hlocal
  omega

/-- Equivalently, a hypothetical overweight configuration must have a
centre where strict domination of the cyclic floor exponent by the
integer-band-jump exponent fails. -/
theorem overweight_exists_non_strict_cyclic_floor_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    ∃ i : V,
      ¬ (listExponent
          ((cyclicRealGapsAt t (cycles i).values).map Nat.floor) <
        listExponent
          (cyclicBandJumps n ((cycles i).values.map Nat.floor))) := by
  classical
  by_contra hnone
  push_neg at hnone
  have hcapacity :=
    weighted_capacity_of_strict_cyclic_floor_slack
      D ht cycles hnone
  omega

#print axioms overweight_exists_tight_local_band_centre
#print axioms overweight_exists_non_strict_cyclic_floor_centre

end DirectionData
end JSP000404Research
