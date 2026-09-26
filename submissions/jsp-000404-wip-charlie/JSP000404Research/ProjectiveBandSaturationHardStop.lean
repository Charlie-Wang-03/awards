
import JSP000404Research.ScaledCyclicBandBudget
import Mathlib.Tactic

/-!
# Local saturation does not force occupation of the two boundary bands

The final n+1 -> n merge outlet needs a saturated centre to occupy both old
bands 0 and n.  This cannot be deduced from the local cyclic band-budget
equality alone.

Take

  n = 3, delta = 1/5, t = 16/5,

and the two scaled projective coordinates

  x0 = 19/10, x1 = 2.

They occupy only the interior bands 1 and 2.

Their cyclic real gaps are

  1/10, 31/10,

so the floor-gap quotient list is [0,3] and its exponent is 2.  The number of
missing bands among 0,1,2,3 is also 2.  Hence the local inequality

  exponent <= missing bands

is saturated, even though neither boundary band 0 nor boundary band 3 is
occupied.

Therefore the boundary-band condition in ProjectiveBandLastMergeCapacity must
come from a suitable global choice of projective cut (or another global
payment argument), not from pointwise saturation alone.
-/

namespace JSP000404Research

def localSaturationHardStopAngles : List ℝ :=
  [(19 : ℝ) / 10, 2]

theorem localSaturationHardStop_floorBands :
    floorBandList localSaturationHardStopAngles = [1, 2] := by
  norm_num [localSaturationHardStopAngles, floorBandList]

theorem localSaturationHardStop_gapFloors :
    (cyclicGapsAt ((16 : ℝ) / 5)
      localSaturationHardStopAngles).map Nat.floor = [0, 3] := by
  norm_num [localSaturationHardStopAngles, cyclicGapsAt,
    successiveDiffsFrom]

theorem localSaturationHardStop_exponent :
    listExponent
      ((cyclicGapsAt ((16 : ℝ) / 5)
        localSaturationHardStopAngles).map Nat.floor) = 2 := by
  rw [localSaturationHardStop_gapFloors]
  norm_num [listExponent, excess]

theorem localSaturationHardStop_missing :
    cyclicBandMissing 4
      (floorBandList localSaturationHardStopAngles) = 2 := by
  rw [localSaturationHardStop_floorBands]
  norm_num [cyclicBandMissing, linearBandMissing]

theorem localSaturationHardStop_exact_saturation :
    listExponent
      ((cyclicGapsAt ((16 : ℝ) / 5)
        localSaturationHardStopAngles).map Nat.floor)
      =
    cyclicBandMissing 4
      (floorBandList localSaturationHardStopAngles) := by
  rw [localSaturationHardStop_exponent,
      localSaturationHardStop_missing]

theorem localSaturationHardStop_boundary_bands_absent :
    0 ∉ (floorBandList localSaturationHardStopAngles).toFinset ∧
    3 ∉ (floorBandList localSaturationHardStopAngles).toFinset := by
  rw [localSaturationHardStop_floorBands]
  decide

#print axioms localSaturationHardStop_floorBands
#print axioms localSaturationHardStop_gapFloors
#print axioms localSaturationHardStop_exact_saturation
#print axioms localSaturationHardStop_boundary_bands_absent

end JSP000404Research
