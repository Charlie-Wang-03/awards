import JSP000404Research.LocalZeroFloorMass
import Mathlib.Tactic

/-!
# A displayed zero-floor block is bounded by global zero-floor mass

This is a purely list-theoretic bridge.  If a global raw-gap list is split as

  pre ++ block ++ post

and every gap in block has natural floor zero, then block.sum is at most the
global listZeroGapMass of the floor quotients.

It separates the remainder-budget argument from later geometric work that
identifies a same-band interval with such a block.
-/

namespace JSP000404Research

theorem listZeroGapMass_map_floor_eq_sum_of_all_zero
    (gs : List ℝ)
    (hzero : ∀ g ∈ gs, Nat.floor g = 0) :
    listZeroGapMass (gs.map Nat.floor) gs = gs.sum := by
  induction gs with
  | nil =>
      simp [listZeroGapMass]
  | cons g gs ih =>
      have hg : Nat.floor g = 0 :=
        hzero g (by simp)
      have htail : ∀ x ∈ gs, Nat.floor x = 0 := by
        intro x hx
        exact hzero x (by simp [hx])
      simp [listZeroGapMass, hg, ih htail]

theorem zero_floor_block_sum_le_global_mass
    (gpre gblock gpost : List ℝ)
    (hzero : ∀ g ∈ gblock, Nat.floor g = 0)
    (hpre0 : ∀ g ∈ gpre, 0 ≤ g)
    (hpost0 : ∀ g ∈ gpost, 0 ≤ g) :
    gblock.sum ≤
      listZeroGapMass
        ((gpre ++ gblock ++ gpost).map Nat.floor)
        (gpre ++ gblock ++ gpost) := by
  have hpreLen :
      (gpre.map Nat.floor).length = gpre.length := by simp
  have hblockLen :
      (gblock.map Nat.floor).length = gblock.length := by simp
  have hpreMass0 :
      0 ≤ listZeroGapMass (gpre.map Nat.floor) gpre := by
    exact listZeroGapMass_nonneg
      (gpre.map Nat.floor) gpre hpreLen
      hpre0
  have hpostMass0 :
      0 ≤ listZeroGapMass (gpost.map Nat.floor) gpost := by
    exact listZeroGapMass_nonneg
      (gpost.map Nat.floor) gpost (by simp)
      hpost0
  have hblockMass :
      listZeroGapMass (gblock.map Nat.floor) gblock =
        gblock.sum :=
    listZeroGapMass_map_floor_eq_sum_of_all_zero
      gblock hzero
  rw [List.map_append]
  rw [listZeroGapMass_append
      ((gpre ++ gblock).map Nat.floor)
      (gpost.map Nat.floor)
      (gpre ++ gblock) gpost (by simp)]
  rw [List.map_append]
  rw [listZeroGapMass_append
      (gpre.map Nat.floor)
      (gblock.map Nat.floor)
      gpre gblock hpreLen]
  rw [hblockMass]
  linarith

#print axioms listZeroGapMass_map_floor_eq_sum_of_all_zero
#print axioms zero_floor_block_sum_le_global_mass

end JSP000404Research
